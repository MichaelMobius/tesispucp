# -*- coding: utf-8 -*-
# Seminormas de Holder y cobertura
# Fuente: Tesis_PUCP_PINN_Poisson_Experimentos.ipynb (ejecución del 29/10/2026)

# Regularidad Holder y cobertura
# Bibliotecas y parámetros propios del experimento.
import os
import sys
import json
import time
import random
import subprocess
import importlib.util
from pathlib import Path
import numpy as np
import pandas as pd
import torch
from torch import nn
import matplotlib.pyplot as plt
from scipy.integrate import solve_ivp
from scipy.interpolate import RegularGridInterpolator

# Parámetros de la ejecución.
MODO = 'experimento'  # 'demostracion' para una ejecución corta
SEMILLA = 2026
GUARDAR_EN_DRIVE = True  # resultados persistentes en Google Drive
DEVICE = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
DTYPE_REG = torch.float64
DTYPE_2D = torch.float32
CFG = {}

def fijar_semilla(semilla):
    random.seed(int(semilla))
    np.random.seed(int(semilla))
    torch.manual_seed(int(semilla))
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(int(semilla))

fijar_semilla(SEMILLA)

if GUARDAR_EN_DRIVE and importlib.util.find_spec('google') is not None and importlib.util.find_spec('google.colab') is not None:
    from google.colab import drive
    if not Path('/content/drive/MyDrive').exists():
        drive.mount('/content/drive')
    SALIDA = Path('/content/drive/MyDrive/Experimentos_PINN_PUCP') / MODO
else:
    SALIDA = Path('resultados_pinn') / MODO
SALIDA.mkdir(parents=True, exist_ok=True)

def guardar_csv(nombre, filas):
    tabla = pd.DataFrame(filas)
    if len(tabla):
        tabla.to_csv(SALIDA / nombre, index=False)
    return tabla

def guardar_figura(nombre):
    plt.tight_layout()
    plt.savefig(SALIDA / nombre, dpi=180, bbox_inches='tight')
    plt.show()
    plt.close()

print('Diagnóstico Holder y cobertura:', DEVICE, '| salida:', SALIDA)

# Para conectar directamente (3.3) con LIPR de Shin se usa alpha=1.
# Cambiar a 0.5 y ejecutar esta sección otra vez para estudiar Holder fraccionario.
ALPHA_HOLDER = 1.0
FACTOR_PESO_HOLDER = 1.0  # prefactor ilustrativo, NO constante certificada (3.1)

# ----------------------------------------------------------
# Redes y derivadas para el experimento de regularización
# ----------------------------------------------------------
from torch.autograd import grad

class RedPoissonRegularizada(nn.Module):
    """MLP completamente conectada con dos capas ocultas de 50 neuronas."""
    def __init__(self):
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(1, 50), nn.Tanh(),
            nn.Linear(50, 50), nn.Tanh(),
            nn.Linear(50, 1)
        )

    def forward(self, x):
        return self.net(x)

def derivadas_hasta_tercera(modelo, x):
    # x debe permitir diferenciación. Devuelve u, u_x, u_xx y u_xxx.
    u = modelo(x)
    ux = grad(u, x, torch.ones_like(u), create_graph=True)[0]
    uxx = grad(ux, x, torch.ones_like(ux), create_graph=True)[0]
    uxxx = grad(uxx, x, torch.ones_like(uxx), create_graph=True)[0]
    return u, ux, uxx, uxxx

def fuente_poisson_tanh(x):
    # Si u(x) = tanh(x), entonces -u''(x) = 2*tanh(x)*sech^2(x).
    return 2.0 * torch.tanh(x) / torch.cosh(x).square()

def componentes_perdida(modelo, x_f, x_b, metodo, lambda_r):
    """Calcula la pérdida PINN, media cuadrática o LIPR de Shin (4.1).

    En PINN estándar basta u_xx. Las derivadas u_xxx se calculan
    únicamente para las dos variantes regularizadas, evitando trabajo extra.
    """
    x = x_f.detach().requires_grad_(True)
    u = modelo(x)
    ux = grad(u, x, torch.ones_like(u), create_graph=True)[0]
    uxx = grad(ux, x, torch.ones_like(ux), create_graph=True)[0]

    # 1) Residuo de la EDP: -u''(x) = 2*tanh(x)*sech^2(x).
    residuo = -uxx - fuente_poisson_tanh(x)
    perdida_pde = residuo.square().mean()

    # 2) Dirichlet en los dos extremos; media = 1/2 de la suma de cuadrados.
    perdida_bc = (modelo(x_b) - torch.tanh(x_b)).square().mean()
    perdida_base = perdida_pde + perdida_bc

    # 3) Regularización. El máximo de Shin NO es una media.
    if metodo == 'PINN':
        regularizador = x.new_zeros(())
    elif metodo in ('Media', 'LIPR-Shin'):
        uxxx = grad(uxx, x, torch.ones_like(uxx), create_graph=True)[0]
        cuadrados = uxxx.square()
        if metodo == 'Media':
            regularizador = cuadrados.mean()
        else:
            # Shin (4.1): max_i |d L[u]/dx (x_i)|^2,
            # para L[u]=-u_xx equivale a max_i |u_xxx(x_i)|^2.
            # Selección explícita del índice máximo: conserva la derivada
            # respecto de todos los parámetros, incluidos los sesgos.
            posicion = cuadrados.detach().reshape(-1).argmax()
            regularizador = cuadrados.reshape(-1)[posicion]
    else:
        raise ValueError(f'Método desconocido: {metodo}')

    perdida_total = perdida_base + lambda_r * regularizador
    return perdida_total, perdida_pde, perdida_bc, regularizador

def errores_relativos_1d(modelo, n_eval=1001):
    """Error L2 y error H1, integrados en una cuadrícula independiente."""
    x = torch.linspace(-1, 1, n_eval, device=DEVICE,
                       dtype=DTYPE_REG).reshape(-1, 1).requires_grad_(True)
    u = modelo(x)
    ux = grad(u, x, torch.ones_like(u), create_graph=False)[0]
    exacta = torch.tanh(x)
    exacta_x = 1.0 - exacta.square()

    # Regla trapezoidal. Incluye u y su derivada en la norma H1.
    e2 = torch.trapz((u - exacta).square().flatten(), x.flatten())
    n2 = torch.trapz(exacta.square().flatten(), x.flatten())
    e_der = torch.trapz((ux - exacta_x).square().flatten(), x.flatten())
    n_der = torch.trapz(exacta_x.square().flatten(), x.flatten())
    return (float(torch.sqrt(e2/n2).detach().cpu()),
            float(torch.sqrt((e2+e_der)/(n2+n_der)).detach().cpu()))

def rejilla_shin(n):
    # Cuadrícula auxiliar, utilizada solo en el modo determinista.
    if n == 1:
        return torch.zeros((1,1), device=DEVICE, dtype=DTYPE_REG)
    return torch.linspace(-1, 1, n, device=DEVICE, dtype=DTYPE_REG).reshape(-1,1)

# ----------------------------------------------------------
# Cocientes de Holder y mediciones sobre una malla independiente
# ----------------------------------------------------------
def aproximar_holder(puntos, valores, alpha=0.5, bloque=256):
    """Máximo de cocientes Holder sobre TODOS los pares i<j, por bloques."""
    x=puntos.detach().reshape(-1).cpu().numpy().astype(float)
    v=valores.detach().reshape(-1).cpu().numpy().astype(float)
    assert len(x)==len(np.unique(x)), 'Los puntos auxiliares deben ser distintos.'
    mejor=0.0
    for i in range(0,len(x),bloque):
        xx=x[i:i+bloque,None]
        vv=v[i:i+bloque,None]
        diferencias=np.abs(xx-x[None,:])
        cocientes=np.divide(np.abs(vv-v[None,:]),
            np.maximum(diferencias,1e-300)**alpha)
        # La diagonal tiene cociente 0: dos puntos iguales se excluyen.
        cocientes[diferencias==0]=0.0
        mejor=max(mejor,float(cocientes.max()))
    return mejor


def evaluar_operador(modelo, x_np, bloque=256):
    """Valores de -h''(x) sin retener el grafo del entrenamiento."""
    salidas=[]
    for inicio in range(0,len(x_np),bloque):
        x=torch.as_tensor(x_np[inicio:inicio+bloque],device=DEVICE,
              dtype=DTYPE_REG).reshape(-1,1).detach().requires_grad_(True)
        u=modelo(x)
        ux=grad(u,x,torch.ones_like(u),create_graph=True)[0]
        uxx=grad(ux,x,torch.ones_like(ux),create_graph=False)[0]
        salidas.append((-uxx).detach().cpu().flatten().numpy())
    return np.concatenate(salidas)



def evaluar_gradiente_operador_1d(modelo, x_np, bloque=256):
    """|d(L[h])/dx|=|h^(3)| en puntos de prueba, no supremo continuo."""
    salidas=[]
    for inicio in range(0,len(x_np),bloque):
        x=torch.as_tensor(x_np[inicio:inicio+bloque],device=DEVICE,
              dtype=DTYPE_REG).reshape(-1,1).detach().requires_grad_(True)
        u=modelo(x)
        ux=grad(u,x,torch.ones_like(u),create_graph=True)[0]
        uxx=grad(ux,x,torch.ones_like(ux),create_graph=True)[0]
        uxxx=grad(uxx,x,torch.ones_like(uxx),create_graph=False)[0]
        salidas.append(uxxx.abs().detach().cpu().reshape(-1).numpy())
    return np.concatenate(salidas)


def perdida_holder_discreta(modelo,x_f,x_b,x_aux,alpha,peso):
    # Penaliza diferencias del OPERADOR -u'', no su tercera derivada.
    x=x_f.detach().clone().requires_grad_(True)
    u=modelo(x); ux=grad(u,x,torch.ones_like(u),create_graph=True)[0]
    uxx=grad(ux,x,torch.ones_like(ux),create_graph=True)[0]
    jpde=(-uxx-fuente_poisson_tanh(x)).square().mean()
    jbc=(modelo(x_b)-torch.tanh(x_b)).square().mean()
    z=x_aux.detach().clone().requires_grad_(True)
    uz=modelo(z); uzx=grad(uz,z,torch.ones_like(uz),create_graph=True)[0]
    uzxx=grad(uzx,z,torch.ones_like(uzx),create_graph=True)[0]
    Lv=-uzxx
    # Usamos todos los pares sin diagonal en el regularizador diferenciable.
    idx_i,idx_j=torch.triu_indices(len(z),len(z),offset=1,device=DEVICE)
    delta=(z[idx_i]-z[idx_j]).abs().pow(alpha)
    sq=((Lv[idx_i]-Lv[idx_j]).abs()/delta).square()
    indice_max = sq.detach().argmax()
    holder_sq=sq[indice_max]
    return jpde+jbc+peso*holder_sq,holder_sq


def entrenar_diagnostico_holder(n, metodo, alpha, seed, pasos,
                                 K_aux=48, muestreo='iid'):
    fijar_semilla(seed)
    modelo=RedPoissonRegularizada().to(DEVICE,dtype=DTYPE_REG)
    if muestreo=='iid':
        # Muestra iid uniformemente en [-1,1], ordenada solo para graficar.
        x_f=-1+2*torch.rand((n,1),device=DEVICE,dtype=DTYPE_REG)
        x_f=x_f.sort(dim=0).values
    else:
        x_f=rejilla_shin(n)
    x_b=torch.tensor([[-1.0],[1.0]],device=DEVICE,dtype=DTYPE_REG)
    # La malla auxiliar NO coincide con la de entrenamiento.
    x_aux=torch.linspace(-1,1,K_aux,device=DEVICE,dtype=DTYPE_REG).reshape(-1,1)
    optimizador=torch.optim.Adam(modelo.parameters(),lr=1e-3)
    for paso in range(pasos):
        optimizador.zero_grad(set_to_none=True)
        if metodo=='Holder':
            L,pen=perdida_holder_discreta(modelo,x_f,x_b,x_aux,alpha,
                                          peso=FACTOR_PESO_HOLDER * n**(-alpha-0.5))
        else:
            L,_,_,_=componentes_perdida(modelo,x_f,x_b,
                         'LIPR-Shin' if metodo=='LIPR' else 'PINN',n**(-1.5))
        L.backward()
        optimizador.step()
    return modelo,x_f.detach(),float(L.detach().cpu())


def radio_cobertura_1d(x_train):
    """Radio EXACTO en [-1,1] para puntos 1D ordenados."""
    s=np.sort(np.asarray(x_train).reshape(-1))
    return max(float(s[0]+1),float(1-s[-1]),
               float(np.diff(s).max()/2) if len(s)>1 else 0.)

print('Herramientas de Holder, diagnóstico y cobertura preparadas.')

# ----------------------------------------------------------
# Experimento Holder: muestreo, residuo y errores independientes
# ----------------------------------------------------------
# Para no confundir este estudio con la figura de Shin, empleamos muestreo iid.
if MODO=='demostracion':
    N_HOLDER=[12,24]
    EPOCAS_HOLDER=20
    K_HOLDER=16
    N_EVAL_HOLDER=128
    MALLAS_HOLDER=[16,32,64]
else:
    N_HOLDER=[20,40,80,160]
    EPOCAS_HOLDER=550
    K_HOLDER=96
    N_EVAL_HOLDER=512
    MALLAS_HOLDER=[32,64,128,256,512]

filas_holder=[]
modelos_diagnostico={}
_x_evaluacion=np.linspace(-1,1,N_EVAL_HOLDER)
for numero in N_HOLDER:
    for metodo in ['PINN','LIPR','Holder']:
        modelo,x_train,perdida_entreno=entrenar_diagnostico_holder(
            numero,metodo,ALPHA_HOLDER,SEMILLA+17,EPOCAS_HOLDER,
            K_aux=K_HOLDER,muestreo='iid')
        estimacion_op=evaluar_operador(modelo,_x_evaluacion)
        _x_cuda=torch.as_tensor(_x_evaluacion,device=DEVICE,dtype=DTYPE_REG).reshape(-1,1)
        rhs=fuente_poisson_tanh(_x_cuda).detach().cpu().numpy().reshape(-1)
        residuo_eval=estimacion_op-rhs
        _x_f=x_train.cpu().numpy().reshape(-1)
        rhs_train=fuente_poisson_tanh(x_train).cpu().numpy().reshape(-1)
        residuo_train=evaluar_operador(modelo,_x_f)-rhs_train
        # Calculamos los errores respecto de la solución exacta en una malla de prueba.
        l2_rel,h1_rel=errores_relativos_1d(modelo,n_eval=1001)
        with torch.no_grad():
            u_eval=modelo(_x_cuda).cpu().numpy().reshape(-1)
        c0=float(np.max(np.abs(u_eval-np.tanh(_x_evaluacion))))
        delta=radio_cobertura_1d(_x_f)
        fila={'N_f':numero,'metodo':metodo,'muestreo':'iid',
              'alpha':ALPHA_HOLDER,'semilla':SEMILLA+17,
              'peso_holder_m':FACTOR_PESO_HOLDER * numero**(-ALPHA_HOLDER-0.5),
              'peso_lipr_m':numero**(-1.5),
              'perdida_ultimo_batch':perdida_entreno,
              'residuo_max_prueba':float(np.max(np.abs(residuo_eval))),
              'residuo_max_entrenamiento':float(np.max(np.abs(residuo_train))),
              'L2_rel':l2_rel,'H1_rel':h1_rel,'C0_evaluado':c0,
              'radio_cobertura_exacto':delta,'epocas':EPOCAS_HOLDER,
              'K_aux':K_HOLDER}
        filas_holder.append(fila)
        guardar_csv('resultados_diagnostico_holder.csv',filas_holder)
        if numero==max(N_HOLDER):
            modelos_diagnostico[metodo]=(modelo,x_train,_x_evaluacion,residuo_eval)
        print(f'Holder N={numero} {metodo:6}: L2={l2_rel:.2e}, '
              f'C0={c0:.2e}, residuo_max={fila["residuo_max_prueba"]:.2e}')

# Refinamiento de la malla auxiliar para calcular cotas inferiores S_K,alpha.
model_ref=modelos_diagnostico['LIPR'][0]
refinamiento_holder=[]
for K in MALLAS_HOLDER:
    z=np.linspace(-1,1,K)
    op=evaluar_operador(model_ref,z)
    px=torch.as_tensor(z.reshape(-1,1),dtype=DTYPE_REG)
    vx=torch.as_tensor(op.reshape(-1,1),dtype=DTYPE_REG)
    for alpha in [0.5,1.0]:
        S=aproximar_holder(px,vx,alpha)
        # Solo para alpha=1: por el teorema del valor medio, el supremo
        # continuo coincide con sup|L'[h]|, que también aproximamos.
        max_grad_malla = (float(np.max(evaluar_gradiente_operador_1d(model_ref,z)))
                          if alpha == 1.0 else np.nan)
        refinamiento_holder.append({'K':K,'alpha':alpha,
              'seminorma_discreta':S,'max_gradiente_operador_en_malla':max_grad_malla})
guardar_csv('refinamiento_seminorma_holder.csv',refinamiento_holder)

# Cubierta con puntos deterministas e iid, medida geométrica independiente del modelo.
filas_cobertura=[]
for n in [4,8,16,32,64,128]:
    rng=np.random.default_rng(SEMILLA+n)
    filas_cobertura.extend([
      {'N_f':n,'muestreo':'equiespaciado','radio_exacto':radio_cobertura_1d(np.linspace(-1,1,n))},
      {'N_f':n,'muestreo':'iid','radio_exacto':radio_cobertura_1d(rng.uniform(-1,1,n))},
    ])
guardar_csv('radios_cobertura_1d.csv',filas_cobertura)

# ----------------------------------------------------------
# Figura: diagnóstico de la regularidad Holder y de la cobertura
# ----------------------------------------------------------
fig,axes=plt.subplots(2,2,figsize=(14,9))

# A. Ejemplo matemático de pico no detectado por un muestreo escaso.
puntos_sparse=np.linspace(-1,1,10)
centro=(puntos_sparse[4]+puntos_sparse[5])/2
xx=np.linspace(-1,1,1200)
sigma=(puntos_sparse[5]-puntos_sparse[4])/9
pico=np.exp(-((xx-centro)/sigma)**2)
axes[0,0].plot(xx,pico,label='Residuo localizado (ejemplo construido)')
axes[0,0].scatter(puntos_sparse,np.exp(-((puntos_sparse-centro)/sigma)**2),
                  color='red',label='Puntos de colocación',zorder=5)
axes[0,0].set(title='A. Pico residual entre muestras',xlabel='x',ylabel='|r(x)|')
axes[0,0].legend(fontsize=8)

# B. Malla auxiliar y estimadores inferiores de la seminorma continua.
tabla_ref=pd.DataFrame(refinamiento_holder)
for alpha in [0.5,1.0]:
    d=tabla_ref[tabla_ref.alpha==alpha]
    axes[0,1].plot(d.K,d.seminorma_discreta,'o-',label=rf'$\alpha={alpha:g}$')
axes[0,1].set(title='B. Refinamiento de la seminorma Holder discreta',
              xlabel='Número de puntos auxiliares K',ylabel=r'$S_{K,\alpha}$')
# Para alpha=1, comparación independiente con max|L'[h]| sobre Q_K.
d=tabla_ref[tabla_ref.alpha==1.0]
if d['max_gradiente_operador_en_malla'].notna().any():
    axes[0,1].plot(d.K, d.max_gradiente_operador_en_malla,'k--',
                   label=r'$\max_{Q_K}|\partial_x\mathcal{L}[h]|$')
axes[0,1].legend()

# C. Residuo máximo independiente versus número de muestras iid.
datos_h=pd.DataFrame(filas_holder)
for metodo in ['PINN','LIPR','Holder']:
    d=datos_h[datos_h.metodo==metodo].sort_values('N_f')
    axes[1,0].loglog(d.N_f,d.residuo_max_prueba,'o-',label=metodo)
axes[1,0].set(title='C. Residuo máximo en malla de prueba',
              xlabel=r'$N_f$ (muestras iid)',ylabel=r'$\max_{Q_K}|r_\theta|$')
axes[1,0].legend(fontsize=8)

# D. Error en C0 calculado frente al número de puntos.
for metodo in ['PINN','LIPR','Holder']:
    d=datos_h[datos_h.metodo==metodo].sort_values('N_f')
    axes[1,1].loglog(d.N_f,d.C0_evaluado,'o-',label=metodo)
axes[1,1].set(title='D. Error uniforme evaluado (no supremo certificado)',
              xlabel=r'$N_f$',ylabel=r'$\max_{Q_K}|h_\theta-u^*|$')
axes[1,1].legend(fontsize=8)
for ax in axes.flat:
    ax.grid(True,which='both',alpha=.25)
fig.suptitle('Regularidad Holder, muestreo y error para Poisson 1D',fontsize=15)
guardar_figura('diagnostico_holder_poisson1d.png')

# ----------------------------------------------------------
# Figura auxiliar: cobertura y prueba de la cota FINITA en la malla
# ----------------------------------------------------------
fig,axs=plt.subplots(1,2,figsize=(12.5,4.5))
cob=pd.DataFrame(filas_cobertura)
for modo in ['equiespaciado','iid']:
    d=cob[cob.muestreo==modo].sort_values('N_f')
    axs[0].loglog(d.N_f,d.radio_exacto,'o-',label=modo)
axs[0].set(xlabel=r'$N_f$',ylabel=r'$\delta_m$',
           title='Radio de cobertura exacto en [-1,1]')
axs[0].legend()

# Para una cuadrícula finita, la desigualdad es exacta si el máximo
# de cocientes se calcula sobre la UNIÓN de prueba y entrenamiento.
modelo,x_train,x_e,r_e=modelos_diagnostico['LIPR']
x_t=x_train.detach().cpu().numpy().reshape(-1)
union=np.unique(np.concatenate((x_e,x_t)))
operator=evaluar_operador(modelo,union)
_rhs=fuente_poisson_tanh(torch.tensor(union,device=DEVICE,dtype=DTYPE_REG).reshape(-1,1)).detach().cpu().numpy().reshape(-1)
z_t=torch.tensor(union.reshape(-1,1),dtype=DTYPE_REG)
for alpha in [0.5,1.0]:
    s_oper=aproximar_holder(z_t,torch.tensor(operator.reshape(-1,1)),alpha)
    s_rhs=aproximar_holder(z_t,torch.tensor(_rhs.reshape(-1,1)),alpha)
    t_res=evaluar_operador(modelo,x_t)-fuente_poisson_tanh(
      torch.tensor(x_t,device=DEVICE,dtype=DTYPE_REG).reshape(-1,1)).detach().cpu().numpy().reshape(-1)
    delta_grid=np.max(np.min(abs(x_e[:,None]-x_t[None,:]),axis=1))
    lado_izq=float(np.max(np.abs(r_e)))
    lado_der=float(np.max(np.abs(t_res))+(s_oper+s_rhs)*delta_grid**alpha)
    assert lado_izq <= lado_der+1e-8,('cota finita',alpha,lado_izq,lado_der)
    axs[1].bar([fr'LHS $\alpha={alpha}$',fr'RHS $\alpha={alpha}$'],[lado_izq,lado_der],
               alpha=.65,label=rf'$\alpha={alpha}$')
axs[1].set(title='Desigualdad de cobertura en malla FINITA',ylabel='Valor evaluado')
for ax in axs:ax.grid(True,alpha=.25)
fig.suptitle('Control geométrico del residuo: diagnóstico numérico')
guardar_figura('holder_cobertura_y_cota_finita.png')
print('La cota de la malla finita se verificó; NO implica una cota continua certificada.')
