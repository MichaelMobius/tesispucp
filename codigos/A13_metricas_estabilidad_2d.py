# Extracto literal del cuaderno revisado, celda 87 (índice desde 0).
# Ejecutar después de las celdas de definiciones previas del notebook.

# ----------------------------------------------------------
# Métricas de estabilidad 2D, independientes de la malla de entrenamiento.
# Esta celda depende de las definiciones RedPoisson2D y laplaciano_2d de arriba.
# ----------------------------------------------------------
import hashlib

class RedPoisson2D_Fuerte(nn.Module):
    """Misma arquitectura 50-50, con contorno Dirichlet exactamente cero."""
    def __init__(self):
        super().__init__()
        self.base=RedPoisson2D(con_datos=False)
    def forward(self,p):
        return (1-p[:,0:1].square())*(1-p[:,1:2].square())*self.base(p)

def malla_prueba_2d(n):
    e=np.linspace(-1,1,int(n),dtype=np.float64)
    X,Y=np.meshgrid(e,e,indexing='ij')
    return np.column_stack((X.ravel(),Y.ravel()))

def puntos_borde_prueba_2d(n):
    e=np.linspace(-1,1,int(n),dtype=np.float64)
    u=np.ones_like(e)
    return np.concatenate((np.column_stack((e,-u)),np.column_stack((e,u)),
                           np.column_stack((-u,e)),np.column_stack((u,e))),axis=0)

def evaluar_estabilidad_2d(modelo, n_eval=101, lote=512):
    """Máximos DISCRETOS: no son cotas certificadas del continuo.

    Ecuación Deltah=-2pi^2u*; residuo r=Deltah+2pi^2u*.
    H1 incluye funciones y primeras derivadas en la misma malla de evaluación.
    """
    evaluacion=malla_prueba_2d(n_eval)
    suma_e2=suma_u2=suma_h1e2=suma_h1u2=0.0
    suma_r2=0.0; max_r=0.0; max_e=0.0
    for ini in range(0,len(evaluacion),lote):
        p=torch.as_tensor(evaluacion[ini:ini+lote],dtype=DTYPE_2D,device=DEVICE).detach().requires_grad_(True)
        h=modelo(p)
        du=grad(h,p,torch.ones_like(h),create_graph=True)[0]
        ux=du[:,0:1]; uy=du[:,1:2]
        uxx=grad(ux,p,torch.ones_like(ux),create_graph=True)[0][:,0:1]
        uyy=grad(uy,p,torch.ones_like(uy),create_graph=False)[0][:,1:2]
        exact=solucion_exacta_2d(p)
        exact_grad=torch.cat((torch.pi*torch.cos(torch.pi*p[:,0:1])*torch.sin(torch.pi*p[:,1:2]),
                        torch.pi*torch.sin(torch.pi*p[:,0:1])*torch.cos(torch.pi*p[:,1:2])),dim=1)
        e=h-exact
        r=uxx+uyy+2*torch.pi**2*exact
        e2=float(e.square().sum().detach()); u2=float(exact.square().sum().detach())
        g2=float((du-exact_grad).square().sum().detach())
        ng2=float(exact_grad.square().sum().detach())
        suma_e2+=e2; suma_u2+=u2
        suma_h1e2+=(e2+g2); suma_h1u2+=(u2+ng2)
        suma_r2+=float(r.square().sum().detach())
        max_r=max(max_r,float(r.detach().abs().max()))
        max_e=max(max_e,float(e.detach().abs().max()))
    borde=puntos_borde_prueba_2d(n_eval)
    max_bc=0.0
    for ini in range(0,len(borde),lote):
        p=torch.as_tensor(borde[ini:ini+lote],dtype=DTYPE_2D,device=DEVICE)
        with torch.no_grad():
            max_bc=max(max_bc,float(modelo(p).abs().max()))
    return {'J_PDE_test':suma_r2/len(evaluacion),
            'residuo_max_test':max_r,'error_max_test':max_e,
            'defecto_frontera_max':max_bc,
            'cota_estabilidad_evaluada':0.5*max_r+max_bc,
            'error_L2_rel':np.sqrt(suma_e2/max(suma_u2,1e-30)),
            'error_H1_rel':np.sqrt(suma_h1e2/max(suma_h1u2,1e-30)),
            'n_eval_lado':int(n_eval),'puntos_eval':len(evaluacion),
            'tipo_cota':'maximos_discretos_no_certificados'}

# Verificación analítica de la parametrización fuerte (incluidas las esquinas).
_modelo_control=RedPoisson2D_Fuerte().to(DEVICE,dtype=DTYPE_2D)
_borde_control=torch.as_tensor(puntos_borde_prueba_2d(15),dtype=DTYPE_2D,device=DEVICE)
assert float(_modelo_control(_borde_control).abs().max().detach()) < 1e-12
print('Contorno fuerte: verificación discreta exacta superada.')

# Diagnóstico sobre los DOS modelos ya entrenados de Poisson 2D.
filas_originales=[]
for nombre,variable,con_datos in [('con_datos','modelo_2d_datos',True),('sin_datos','modelo_2d_sin',False)]:
    modelo_original=globals().get(variable)
    if modelo_original is None:
        p=SALIDA/'modelos_2d_originales'/f'poisson2d_{nombre}.pt'
        if p.exists():
            contenido=torch.load(p,map_location='cpu',weights_only=True)
            modelo_original=RedPoisson2D(con_datos=con_datos).to(DEVICE,dtype=DTYPE_2D)
            modelo_original.load_state_dict(contenido['state_dict'])
    if modelo_original is not None:
        f=evaluar_estabilidad_2d(modelo_original,n_eval=(31 if MODO=='demostracion' else 201))
        f.update({'tipo':nombre,'origen':'entrenamiento_original','N':int(CFG['n_poisson2d'])})
        filas_originales.append(f)
if filas_originales:
    guardar_csv('estabilidad_modelos_originales_2d.csv',filas_originales)
    print(pd.DataFrame(filas_originales).to_string(index=False))
else:
    print('No se hallaron modelos originales; ejecutar antes los bloques Poisson 2D.')
