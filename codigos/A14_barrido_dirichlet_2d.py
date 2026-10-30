# Extracto literal del cuaderno revisado, celda 88 (índice desde 0).
# Ejecutar después de las celdas de definiciones previas del notebook.

# ----------------------------------------------------------
# Entrenamiento 2D con checkpoint/reanudación y comparación fuerte/penalizado.
# ----------------------------------------------------------
BARRIDO_N = [6,10] if MODO=='demostracion' else [12,24,40,75]
BARRIDO_SEMILLAS = [SEMILLA] if MODO=='demostracion' else [SEMILLA,SEMILLA+1,SEMILLA+2]
BARRIDO_ADAM = 20 if MODO=='demostracion' else 4000
BARRIDO_LBFGS = 0 if MODO=='demostracion' else 120
BARRIDO_EVAL = 31 if MODO=='demostracion' else 201
BARRIDO_CKPT_CADA = 300
BARRIDO_CKPT_LBFGS = 20

CARPETA_MODELOS_2D=SALIDA/'modelos_2d_barrido'; CARPETA_MODELOS_2D.mkdir(parents=True,exist_ok=True)

def firma_2d(cfg):
    return hashlib.sha256(json.dumps(cfg,sort_keys=True).encode('utf-8')).hexdigest()[:16]

def entrenar_poisson_2d_revisado(N,semilla,fuerte,ep_adam,ep_lbfgs):
    cfg={'revision':'2d_stability_strong_v2','N':int(N),'semilla':int(semilla),
         'fuerte':bool(fuerte),'adam':int(ep_adam),'lbfgs':int(ep_lbfgs),
         'dtype':str(DTYPE_2D),'bc_peso':10.0 if not fuerte else 0.0,
         'arquitectura':'MLP_2_50_50_1_tanh','optimizador':'Adam1e-3+LBFGS1'}
    firma=firma_2d(cfg)
    archivo=CARPETA_MODELOS_2D/f'{firma}.pt'
    ckpt=CARPETA_MODELOS_2D/f'{firma}.parcial.pt'
    fijar_semilla(semilla)
    red=(RedPoisson2D_Fuerte() if fuerte else RedPoisson2D(False)).to(DEVICE,dtype=DTYPE_2D)
    optim=torch.optim.Adam(red.parameters(),lr=1e-3)
    interior,borde=crear_puntos_2d(N)
    ep_inicio=0; history=[]; lb_done=0; old_seconds=0.0; old_lb_state=None
    if archivo.exists():
        data=torch.load(archivo,map_location='cpu',weights_only=False)
        if data.get('cfg')==cfg and data.get('estado')=='completado':
            red.load_state_dict(data['modelo'])
            return red,data['metricas'],data.get('historia',[]),firma
    if ckpt.exists():
        estado=torch.load(ckpt,map_location='cpu',weights_only=False)
        if estado.get('cfg')==cfg:
            red.load_state_dict(estado['modelo'])
            optim.load_state_dict(estado['optim_adam'])
            ep_inicio=int(estado['adam_done']); lb_done=int(estado['lbfgs_done'])
            history=list(estado['historia']); old_seconds=float(estado['segundos'])
            old_lb_state=estado.get('optim_lbfgs')
            print('Reanudando 2D:',N,semilla,fuerte,ep_inicio,lb_done)
    inicio=time.perf_counter()
    def objetivo():
        p=interior.detach().requires_grad_(True)
        residuo=laplaciano_2d(red,p)+2*torch.pi**2*solucion_exacta_2d(p)
        pde=residuo.square().mean()
        bc=pde.new_zeros(()) if fuerte else red(borde).square().mean()
        return pde+10*bc,pde,bc
    def guardado_parcial(adam_done,lbfgs_done,lb_state=None):
        paquete={'cfg':cfg,'modelo':red.state_dict(),'optim_adam':optim.state_dict(),
                 'optim_lbfgs':lb_state,'adam_done':adam_done,'lbfgs_done':lbfgs_done,
                 'historia':history,'segundos':old_seconds+time.perf_counter()-inicio}
        temporal=ckpt.with_suffix('.tmp.pt')
        torch.save(paquete,temporal); temporal.replace(ckpt)
    for ep in range(ep_inicio,ep_adam):
        optim.zero_grad(set_to_none=True)
        perdida,pde,bc=objetivo()
        if not torch.isfinite(perdida): raise FloatingPointError(f'Pérdida no finita: {cfg}')
        perdida.backward(); optim.step()
        if ep==0 or (ep+1)%max(1,ep_adam//25)==0 or ep+1==ep_adam:
            history.append({'paso':ep+1,'perdida_pre_paso':float(perdida.detach()),
                            'PDE_pre_paso':float(pde.detach()),'BC_pre_paso':float(bc.detach())})
        if (ep+1)%BARRIDO_CKPT_CADA==0 or ep+1==ep_adam:
            guardado_parcial(ep+1,lb_done,old_lb_state)
    if ep_lbfgs:
        optimizer=torch.optim.LBFGS(red.parameters(),lr=1,max_iter=min(BARRIDO_CKPT_LBFGS,ep_lbfgs),
                                    history_size=20,line_search_fn='strong_wolfe')
        if old_lb_state is not None: optimizer.load_state_dict(old_lb_state)
        def closure():
            optimizer.zero_grad(set_to_none=True)
            loss,_,_=objetivo(); loss.backward(); return loss
        while lb_done<ep_lbfgs:
            optimizer.param_groups[0]['max_iter']=min(BARRIDO_CKPT_LBFGS,ep_lbfgs-lb_done)
            optimizer.step(closure)
            internos=int(optimizer.state[optimizer._params[0]].get('n_iter',0))
            if internos<=lb_done:break
            lb_done=internos
            old_lb_state=optimizer.state_dict()
            guardado_parcial(ep_adam,lb_done,old_lb_state)
    # Calcular el objetivo realmente final, luego evaluar en cuadrícula independiente.
    total,pde,bc=objetivo()
    metricas=evaluar_estabilidad_2d(red,n_eval=BARRIDO_EVAL)
    metricas.update({'N':N,'N_f':(N-1)**2,'semilla':semilla,'fuerte':fuerte,
                     'tipo':'Dirichlet_fuerte' if fuerte else 'Dirichlet_penalizado',
                     'pasos_Adam':ep_adam,'pasos_LBFGS':lb_done,'segundos':old_seconds+time.perf_counter()-inicio,
                     'J_total_train':float(total.detach()), 'J_PDE_train':float(pde.detach()),
                     'J_BC_train':float(bc.detach()),'firma':firma,'dtype':str(DTYPE_2D)})
    # state_dict CPU para carga sin GPU.
    salida={'cfg':cfg,'estado':'completado',
            'modelo':{k:v.detach().cpu() for k,v in red.state_dict().items()},
            'metricas':metricas,'historia':history}
    temporal=archivo.with_suffix('.tmp.pt')
    torch.save(salida,temporal); temporal.replace(archivo)
    if ckpt.exists():ckpt.unlink()
    return red,metricas,history,firma

resultados_barrido=[]
if EJECUTAR_BARRIDO_2D:
    for N in BARRIDO_N:
        for semilla in BARRIDO_SEMILLAS:
            for fuerte in [False,True]:
                red,m,h,firma=entrenar_poisson_2d_revisado(N,semilla,fuerte,BARRIDO_ADAM,BARRIDO_LBFGS)
                resultados_barrido.append(m)
                guardar_csv('convergencia_poisson2d_revisada.csv',resultados_barrido)
                print(f'N={N:3d} semilla={semilla} fuerte={fuerte} '
                      f'L2={m["error_L2_rel"]:.3e}, H1={m["error_H1_rel"]:.3e}, '
                      f'max_err={m["error_max_test"]:.3e}, max_r={m["residuo_max_test"]:.3e}')
    tabla=pd.DataFrame(resultados_barrido)
    resumen=tabla.groupby(['N','tipo'],as_index=False).agg(
        L2_mediana=('error_L2_rel','median'),H1_mediana=('error_H1_rel','median'),
        max_error_mediana=('error_max_test','median'),
        max_residuo_mediana=('residuo_max_test','median'),
        L2_std=('error_L2_rel','std'),segundos_mediana=('segundos','median'))
    guardar_csv('resumen_convergencia_poisson2d.csv',resumen.to_dict('records'))
    print(resumen.to_string(index=False))
else:
    print('Barrido 2D omitido; activar EJECUTAR_BARRIDO_2D para ejecutarlo.')
