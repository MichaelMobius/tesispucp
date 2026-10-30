# Extracto literal del cuaderno revisado, celda 69 (índice desde 0).
# Ejecutar después de las celdas de definiciones previas del notebook.

# Diagnóstico adicional, aislado por firma de configuración y subdirectorio.
if EJECUTAR_DIAGNOSTICO_SHIN:
    casos_diag = [(50,None),(100,None),(200,None),(200,100)]
    diag_resultados=[]
    archivo_diag=SALIDA/'diagnostico_oscilatorio_controlado.csv'
    if archivo_diag.exists():
        diag_resultados=pd.read_csv(archivo_diag).to_dict('records')
    for n, batch in casos_diag:
        # Los mismos parámetros iniciales para PINN y LIPR a cada N.
        fijar_semilla(SEMILLA+60000+n)
        init=RedShinDirichletFuerte().to(device=DEVICE,dtype=DTYPE_REG)
        estado_init=copy.deepcopy(init.state_dict())
        for metodo in ['PINN','LIPR']:
            cfg_diag={'n':[n], 'adam':(35 if MODO=='demostracion' else 2500),
                      'lbfgs':(0 if MODO=='demostracion' else 100),
                      'eval':(201 if MODO=='demostracion' else 2001),'batch':batch}
            firma=firma_shin('oscilatorio',n,metodo,cfg_diag)
            if any(str(r.get('firma_protocolo'))==firma for r in diag_resultados):
                continue
            fijar_semilla(SEMILLA+60000+n)
            modelo,fila,hist=entrenar_shin('oscilatorio',n,metodo,cfg_diag,estado_init)
            x_ref=torch.linspace(-1,1,401 if MODO=='demostracion' else 2001,
                                 dtype=DTYPE_REG,device=DEVICE).reshape(-1,1)
            with torch.no_grad():
                err=(modelo(x_ref)-exacta_shin(x_ref,'oscilatorio')).flatten().cpu().numpy()
            x_eval=x_ref.detach().cpu().numpy().ravel()
            r_vals=[]
            for ini in range(0,len(x_ref),256):
                x=x_ref[ini:ini+256].detach().requires_grad_(True)
                u=modelo(x)
                ux=grad(u,x,torch.ones_like(u),create_graph=True)[0]
                uxx=grad(ux,x,torch.ones_like(ux),create_graph=False)[0]
                r_vals.extend((-uxx-fuente_shin(x,'oscilatorio')).detach().flatten().cpu().numpy())
            fila.update({'batch_diag':('total' if batch is None else batch),
                         'J_PDE_test':float(np.mean(np.asarray(r_vals)**2)),
                         'residuo_max_test':float(np.max(np.abs(r_vals)))})
            diag_resultados.append(fila)
            guardar_csv(archivo_diag.name,diag_resultados)
            diag_dir=SALIDA/'diagnostico_shin_modelos'; diag_dir.mkdir(exist_ok=True)
            torch.save({'modelo':{k:v.detach().cpu() for k,v in modelo.state_dict().items()},
                        'firma':firma,'fila':fila},diag_dir/f'{firma}.pt')
            fig,ax=plt.subplots(1,2,figsize=(11,3.5))
            ax[0].plot(x_eval,err); ax[0].set_title('Error firmado h - u*')
            ax[1].plot(x_eval,r_vals); ax[1].set_title('Residuo -h\u2033 - f')
            for a in ax: a.set_xlabel('x'); a.grid(alpha=.25)
            fig.suptitle(f'N={n} | {metodo} | batch={batch or "total"}')
            guardar_figura(f'diagnostico_oscilatorio_{metodo}_N{n}_B{batch or "total"}.png')
            print('Diagnóstico:',n,batch,metodo,'L2=',fila['error_L2_discreto'])
    print(pd.DataFrame(diag_resultados)[['N_f','metodo','batch_diag','error_L2_discreto','J_PDE_test','residuo_max_test']].to_string(index=False))
else:
    print('Diagnóstico Shin omitido por configuración.')
