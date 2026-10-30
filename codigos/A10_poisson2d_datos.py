# -*- coding: utf-8 -*-
# Poisson 2D con observaciones
# Fuente: Tesis_PUCP_PINN_Poisson_Experimentos.ipynb (ejecución del 29/10/2026)

# Poisson 2D con observaciones
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
CFG = {
    'ep_poisson2d': 60 if MODO=='demostracion' else 6000,
    'n_poisson2d': 9 if MODO=='demostracion' else 75,
    'n_evaluacion': 25 if MODO=='demostracion' else 101,
}

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

print('Poisson 2D con observaciones:', DEVICE, '| salida:', SALIDA)

# ----------------------------------------------------------
# Poisson 2D: arquitectura, puntos y derivadas del operador
# ----------------------------------------------------------
def solucion_exacta_2d(p):
    return torch.sin(torch.pi * p[:, 0:1]) * torch.sin(torch.pi * p[:, 1:2])

def laplaciano_2d(modelo, puntos):
    # Deltau = u_xx + u_yy; el laplaciano no incluye derivadas mixtas.
    u = modelo(puntos)
    grads = torch.autograd.grad(u, puntos, torch.ones_like(u), create_graph=True)[0]
    ux = grads[:, 0:1]
    uy = grads[:, 1:2]
    uxx = torch.autograd.grad(ux, puntos, torch.ones_like(ux), create_graph=True)[0][:, 0:1]
    uyy = torch.autograd.grad(uy, puntos, torch.ones_like(uy), create_graph=True)[0][:, 1:2]
    return uxx + uyy

def crear_puntos_2d(N):
    # N subdivisiones por eje; los puntos residuales son interiores.
    eje = torch.linspace(-1, 1, N+1, device=DEVICE, dtype=DTYPE_2D)
    X, Y = torch.meshgrid(eje[1:-1], eje[1:-1], indexing='ij')
    interior = torch.stack((X.flatten(), Y.flatten()), dim=1)

    # Construimos explícitamente los cuatro lados de la frontera.
    lado_abajo = torch.stack((eje, torch.full_like(eje, -1)), dim=1)
    lado_arriba = torch.stack((eje, torch.full_like(eje, 1)), dim=1)
    lado_izq = torch.stack((torch.full_like(eje, -1), eje), dim=1)
    lado_der = torch.stack((torch.full_like(eje, 1), eje), dim=1)
    frontera = torch.cat((lado_abajo, lado_arriba, lado_izq, lado_der))
    return interior, frontera

class RedPoisson2D(nn.Module):
    def __init__(self, con_datos=False):
        super().__init__()
        # Arquitectura 40-80-40 en el caso con observaciones,
        # y 50-50 en la aproximación solo física.
        anchos = (40,80,40) if con_datos else (50,50)
        capas, anterior = [], 2
        for ancho in anchos:
            capas.extend([nn.Linear(anterior, ancho), nn.Tanh()])
            anterior = ancho
        capas.append(nn.Linear(anterior, 1))
        self.net = nn.Sequential(*capas)

    def forward(self, p):
        return self.net(p)

def entrenar_poisson_2d(N, epocas, con_datos, semilla):
    fijar_semilla(semilla)
    modelo = RedPoisson2D(con_datos).to(device=DEVICE, dtype=DTYPE_2D)
    interior, frontera = crear_puntos_2d(N)
    observaciones = None
    if con_datos:
        # Los mismos 25 puntos interiores del planteamiento original.
        eje_obs = torch.tensor([-.8, -.4, 0., .4, .8],
                               device=DEVICE, dtype=DTYPE_2D)
        Xo, Yo = torch.meshgrid(eje_obs, eje_obs, indexing='ij')
        observaciones = torch.stack((Xo.flatten(), Yo.flatten()), dim=1)

    optimizador = torch.optim.Adam(modelo.parameters(), lr=1e-3)
    historial = []
    comienzo = time.perf_counter()
    for epoca in range(epocas):
        puntos = interior.detach().requires_grad_(True)
        # Ecuación Deltau = -2pi^2 sin(pix) sin(piy).
        residuo = laplaciano_2d(modelo, puntos) + 2*torch.pi**2*solucion_exacta_2d(puntos)
        perdida_pde = residuo.square().mean()
        perdida_bc = modelo(frontera).square().mean()
        perdida_datos = ((modelo(observaciones)-solucion_exacta_2d(observaciones))
                         .square().mean() if con_datos else puntos.new_zeros(()))
        perdida = perdida_pde + 10.0*perdida_bc + perdida_datos
        optimizador.zero_grad(set_to_none=True)
        perdida.backward()
        optimizador.step()
        if epoca == 0 or (epoca+1) % max(1, epocas//20) == 0 or epoca+1 == epocas:
            historial.append({'epoca': epoca+1, 'total': float(perdida.detach()),
                              'pde': float(perdida_pde.detach()),
                              'bc': float(perdida_bc.detach()),
                              'datos': float(perdida_datos.detach())})
    return modelo, historial, time.perf_counter()-comienzo

def puntos_evaluacion_2d(N):
    # Cuadrícula interior común y fija para evaluar FEM, FVM y PINN.
    eje = np.linspace(-1,1,N+2)[1:-1]
    X,Y = np.meshgrid(eje,eje,indexing='ij')
    return np.column_stack((X.ravel(),Y.ravel()))

def predecir_2d(modelo, puntos, lote=5000):
    valores=[]
    for i in range(0,len(puntos),lote):
        p = torch.as_tensor(puntos[i:i+lote], device=DEVICE, dtype=DTYPE_2D)
        with torch.no_grad():
            valores.append(modelo(p).cpu().numpy().ravel())
    return np.concatenate(valores)

def error_l2_2d(prediccion, puntos):
    real = np.sin(np.pi*puntos[:,0])*np.sin(np.pi*puntos[:,1])
    prediccion=np.asarray(prediccion).reshape(-1)
    return float(np.linalg.norm(prediccion-real) / np.linalg.norm(real))

def error_h1_2d(modelo, puntos):
    p=torch.as_tensor(puntos,device=DEVICE,dtype=DTYPE_2D).requires_grad_(True)
    u=modelo(p)
    du=torch.autograd.grad(u,p,torch.ones_like(u))[0]
    exact=solucion_exacta_2d(p)
    x,y=p[:,0:1],p[:,1:2]
    du_exact=torch.cat((torch.pi*torch.cos(torch.pi*x)*torch.sin(torch.pi*y),
                        torch.pi*torch.sin(torch.pi*x)*torch.cos(torch.pi*y)),dim=1)
    error2=(u-exact).square().sum()+(du-du_exact).square().sum()
    norma2=exact.square().sum()+du_exact.square().sum()
    return float(torch.sqrt(error2/norma2).detach().cpu())

# ----------------------------------------------------------
# Poisson 2D con observaciones interiores
# ----------------------------------------------------------
modelo_2d_datos, historial_2d_datos, segundos = entrenar_poisson_2d(
    CFG['n_poisson2d'], CFG['ep_poisson2d'], con_datos=True, semilla=SEMILLA+40
)
puntos_test_2d = puntos_evaluacion_2d(CFG['n_evaluacion'])
prediccion_2d_datos = predecir_2d(modelo_2d_datos, puntos_test_2d)
error_2d_datos = error_l2_2d(prediccion_2d_datos, puntos_test_2d)
error_2d_datos_h1 = error_h1_2d(modelo_2d_datos, puntos_test_2d)
print(f'Con observaciones: L2 = {error_2d_datos:.4e}, H1 = {error_2d_datos_h1:.4e}')
guardar_csv('historial_poisson2d_con_datos.csv', historial_2d_datos)

# Superficies de referencia y aproximación.
N_test=CFG['n_evaluacion']
X=puntos_test_2d[:,0].reshape(N_test,N_test)
Y=puntos_test_2d[:,1].reshape(N_test,N_test)
U=np.sin(np.pi*X)*np.sin(np.pi*Y)
P=prediccion_2d_datos.reshape(N_test,N_test)
fig=plt.figure(figsize=(12,5))
ax1=fig.add_subplot(121,projection='3d')
ax2=fig.add_subplot(122,projection='3d')
ax1.plot_surface(X,Y,U,cmap='viridis'); ax1.set_title('Solución exacta')
ax2.plot_surface(X,Y,P,cmap='viridis'); ax2.set_title('PINN con observaciones')
guardar_figura('poisson_2d_con_datos.png')
# Resultado numérico propio de esta sección (sin depender del caso sin datos).
guardar_csv('metricas_poisson2d_con_datos.csv', [{
    'caso': 'con datos', 'error_L2_rel': error_2d_datos,
    'error_H1_rel': error_2d_datos_h1, 'N_lado': CFG['n_poisson2d'],
    'epocas': CFG['ep_poisson2d']
}])


# ----------------------------------------------------------
# Poisson 2D con datos: pérdidas total, residual y de frontera
# ----------------------------------------------------------
epocas = [fila['epoca'] for fila in historial_2d_datos]
plt.figure(figsize=(9, 5))

# Los valores almacenados no se transforman: solo cambia la escala del eje Y.
plt.semilogy(epocas, [fila['total'] for fila in historial_2d_datos],
             label='Pérdida total')
plt.semilogy(epocas, [fila['pde'] for fila in historial_2d_datos],
             label='Residuo de Poisson')
plt.semilogy(epocas, [10 * fila['bc'] for fila in historial_2d_datos],
             label='10 x frontera')
plt.semilogy(epocas, [fila['datos'] for fila in historial_2d_datos],
             label='Observaciones')
plt.xlabel('Épocas')
plt.ylabel('Pérdida')
plt.title('Poisson 2D con observaciones: entrenamiento')
plt.grid(True, which='both', alpha=0.3)
plt.legend()
guardar_figura('perdida_poisson_2d_con_datos.png')

# Participación de cada término EN LA PÉRDIDA TOTAL (no en el error L2).
# El factor 10 de Dirichlet está incluido en el porcentaje de frontera.
tabla_c = pd.DataFrame(historial_2d_datos)
componentes = np.column_stack([tabla_c['pde'], 10 * tabla_c['bc'], tabla_c['datos']])
total_c = componentes.sum(axis=1)
participacion = 100 * componentes / np.maximum(total_c[:, None], 1e-30)
fig, ax = plt.subplots(figsize=(9,4.5))
ax.stackplot(tabla_c['epoca'], *participacion.T,
             labels=['EDP', 'Frontera x 10', 'Datos'], alpha=.85)
ax.set(xlabel='Épocas', ylabel='Contribución a la pérdida (%)',
       ylim=(0,100), title='Poisson 2D: con observaciones')
ax.legend(loc='upper right')
ax.grid(alpha=.25)
guardar_figura('participacion_perdidas_poisson_2d_con_datos.png')

