# -*- coding: utf-8 -*-
# Comparación FEM, FVM y PINN
# Fuente: Tesis_PUCP_PINN_Poisson_Experimentos.ipynb (ejecución del 29/10/2026)

# Poisson 2D: FEM, FVM y PINN
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
    'n_benchmark': [5,9] if MODO=='demostracion' else [10,20,30,40,60,80],
    'ep_benchmark_pinn': 60 if MODO=='demostracion' else 4000,
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

print('Comparación FEM / FVM / PINN:', DEVICE, '| salida:', SALIDA)

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
# Dependencias adicionales de los métodos tradicionales
# ----------------------------------------------------------
# En Colab se instalan una sola vez; en un entorno local con ambas
# bibliotecas presentes no se modifica la instalación de Python.
paquetes = [('skfem','scikit-fem'), ('fipy','fipy')]
faltantes=[nombre for modulo,nombre in paquetes if importlib.util.find_spec(modulo) is None]
if faltantes:
    print('Instalando:', ', '.join(faltantes))
    subprocess.check_call([sys.executable,'-m','pip','install','-q',*faltantes])

import fipy as fp
from skfem import MeshQuad, Basis, ElementQuad1, BilinearForm, LinearForm, asm, condense, solve
from skfem.models.poisson import laplace

print('FiPy y scikit-fem disponibles.')

# ----------------------------------------------------------
# Método de Elementos Finitos FEM: scikit-fem
# ----------------------------------------------------------
def resolver_fem(N, puntos_test):
    # Malla cuadrilateral sobre [-1,1]^2 con N celdas por dirección.
    eje = np.linspace(-1.0, 1.0, N+1)
    malla = MeshQuad.init_tensor(eje, eje)
    base = Basis(malla, ElementQuad1())

    # Formulación débil: integral grad(u).grad(v) = integral (2pi^2sinpix sinpiy) v.
    @LinearForm
    def carga(v, w):
        x,y = w.x[0], w.x[1]
        return (2*np.pi**2*np.sin(np.pi*x)*np.sin(np.pi*y))*v

    A = asm(laplace, base)
    b = asm(carga, base)
    coeficientes = solve(*condense(A, b, D=base.get_dofs()))

    # Evaluar la solución FEM en los mismos puntos que los demás métodos.
    return np.asarray(base.probes(puntos_test.T) @ coeficientes).reshape(-1)

# ----------------------------------------------------------
# Método de Volúmenes Finitos FVM: FiPy
# ----------------------------------------------------------
def resolver_fvm(N, puntos_test):
    paso = 2.0/N
    # Grid2D genera inicialmente coordenadas en [0,2]^2.
    malla = fp.Grid2D(dx=paso, dy=paso, nx=N, ny=N)
    xc = np.asarray(malla.cellCenters[0])-1.0
    yc = np.asarray(malla.cellCenters[1])-1.0
    fuente = -2.0*np.pi**2*np.sin(np.pi*xc)*np.sin(np.pi*yc)

    # Imponer Dirichlet homogénea sobre TODAS las caras externas.
    phi = fp.CellVariable(mesh=malla, value=0.0)
    phi.constrain(0.0, where=malla.exteriorFaces)
    rhs = fp.CellVariable(mesh=malla, value=fuente)
    (fp.DiffusionTerm() == rhs).solve(var=phi)

    # Las incógnitas de FiPy están en los CENTROS de las celdas.
    # Se interpolan hacia la misma malla de prueba que FEM y PINN.
    centros = -1.0+(np.arange(N)+0.5)*paso
    coordenadas = np.concatenate(([-1.0],centros,[1.0]))
    valores = np.zeros((N+2,N+2))
    valores[1:-1,1:-1] = np.asarray(phi.value).reshape((N,N),order='F')
    interpolador = RegularGridInterpolator((coordenadas,coordenadas),valores)
    return interpolador(puntos_test)

# ----------------------------------------------------------
# Barrido de resolución para FEM, FVM y PINN
# ----------------------------------------------------------
resultados_comparacion = []
# Se conservan las tres predicciones en una resolución de referencia.
# Así todas las superficies y errores se calculan con la misma cuadrícula.
N_FIGURA = max(CFG['n_benchmark'])
campos_benchmark = {}
puntos_comunes = puntos_evaluacion_2d(CFG['n_evaluacion'])

for N in CFG['n_benchmark']:
    print(f'\nResolución N={N}')

    # FEM y FVM: se resuelven directamente con sus propios solvers.
    for metodo, solver in [('FEM',resolver_fem), ('FVM',resolver_fvm)]:
        inicio=time.perf_counter()
        estimacion=solver(N, puntos_comunes)
        segundos=time.perf_counter()-inicio
        error=error_l2_2d(estimacion,puntos_comunes)
        resultados_comparacion.append({
            'metodo':metodo,'N':N,'error_L2_rel':error,'segundos':segundos,
            'puntos_evaluacion':len(puntos_comunes),'protocolo':MODO
        })
        if N == N_FIGURA:
            campos_benchmark[metodo] = np.asarray(estimacion, dtype=float).copy()
        guardar_csv('comparacion_fem_fvm_pinn.csv',resultados_comparacion)
        print(f'  {metodo}: error relativo L2={error:.4e}')

    # PINN: el mismo problema físico, sin datos de observación interiores.
    red_pinn, historial, segundos = entrenar_poisson_2d(
        N, CFG['ep_benchmark_pinn'], con_datos=False, semilla=SEMILLA+100+N
    )
    estimacion=predecir_2d(red_pinn, puntos_comunes)
    error=error_l2_2d(estimacion,puntos_comunes)
    resultados_comparacion.append({
        'metodo':'PINN','N':N,'error_L2_rel':error,'segundos':segundos,
        'puntos_evaluacion':len(puntos_comunes),'protocolo':MODO
    })
    if N == N_FIGURA:
        campos_benchmark['PINN'] = np.asarray(estimacion, dtype=float).copy()
    guardar_csv('comparacion_fem_fvm_pinn.csv',resultados_comparacion)
    print(f'  PINN: error relativo L2={error:.4e}')

# ----------------------------------------------------------
# Gráfica log-log: errores calculados (sin tablas fijas)
# ----------------------------------------------------------
datos = pd.DataFrame(resultados_comparacion)
plt.figure(figsize=(9,6))
for metodo,simbolo in [('FEM','o-'),('FVM','s-'),('PINN','d--')]:
    d=datos[datos['metodo']==metodo].sort_values('N')
    plt.loglog(d['N'],d['error_L2_rel'],simbolo,linewidth=2,label=metodo)
plt.xlabel('Parámetro de resolución $N$')
plt.ylabel('Error relativo $L^2$ en cuadrícula de evaluación común')
plt.title('Comparación de FEM, FVM y PINN para Poisson 2D')
plt.legend()
plt.grid(True,which='both',alpha=.35)
guardar_figura('figura_4_9_comparacion_metodos.png')

# Tabla numérica con el error y el tiempo de cada cálculo.
print(datos.to_string(index=False))

# ----------------------------------------------------------
# Superficies 3D: solución exacta, PINN, FiPy y sus errores
# ----------------------------------------------------------
# Los campos fueron guardados al realizar el barrido comparativo.
# NO se realiza un segundo entrenamiento para elaborar estas figuras.
assert set(campos_benchmark) == {'FEM', 'FVM', 'PINN'}, (
    'Ejecute primero el barrido FEM/FVM/PINN para obtener las tres predicciones.'
)

numero_puntos = len(puntos_comunes)
n_lado = int(np.sqrt(numero_puntos))
assert n_lado * n_lado == numero_puntos, 'La cuadrícula debe ser cuadrada.'

# Misma cuadrícula y solución analítica para los tres métodos.
X_comun = puntos_comunes[:, 0].reshape(n_lado, n_lado)
Y_comun = puntos_comunes[:, 1].reshape(n_lado, n_lado)
U_exacta = np.sin(np.pi * X_comun) * np.sin(np.pi * Y_comun)
U_pinn = campos_benchmark['PINN'].reshape(n_lado, n_lado)
U_fipy = campos_benchmark['FVM'].reshape(n_lado, n_lado)
U_fem = campos_benchmark['FEM'].reshape(n_lado, n_lado)

# Errores ABSOLUTOS (puntuales): magnitudes siempre no negativas.
error_pinn_abs = np.abs(U_pinn - U_exacta)
error_fipy_abs = np.abs(U_fipy - U_exacta)
error_fem_abs = np.abs(U_fem - U_exacta)

# Escalas idénticas para comparar las alturas y el color entre superficies.
limite_solucion = max(1.0, float(np.max(np.abs(U_exacta))),
                      float(np.max(np.abs(U_pinn))), float(np.max(np.abs(U_fipy))))
limite_error = max(1.e-12, float(error_pinn_abs.max()), float(error_fipy_abs.max()))

fig = plt.figure(figsize=(18, 10))
superficies = [
    ('Solución analítica', U_exacta),
    ('Solución PINN', U_pinn),
    ('Solución FiPy (FVM)', U_fipy),
]
for posicion, (titulo, valores) in enumerate(superficies, start=1):
    ax = fig.add_subplot(2, 3, posicion, projection='3d')
    ax.plot_surface(X_comun, Y_comun, valores, cmap='viridis',
                    vmin=-limite_solucion, vmax=limite_solucion,
                    linewidth=0, antialiased=True, rcount=55, ccount=55)
    ax.set_zlim(-limite_solucion, limite_solucion)
    ax.set_title(titulo)
    ax.set_xlabel('x'); ax.set_ylabel('y'); ax.set_zlabel('u(x,y)')

for posicion, (titulo, valores) in enumerate([
    ('Error absoluto PINN', error_pinn_abs),
    ('Error absoluto FiPy', error_fipy_abs),
], start=4):
    ax = fig.add_subplot(2, 3, posicion, projection='3d')
    ax.plot_surface(X_comun, Y_comun, valores, cmap='magma',
                    vmin=0.0, vmax=limite_error,
                    linewidth=0, antialiased=True, rcount=55, ccount=55)
    ax.set_zlim(0, limite_error)
    ax.set_title(titulo)
    ax.set_xlabel('x'); ax.set_ylabel('y'); ax.set_zlabel('|error|')

# El último panel resume el experimento sin mezclar escalas.
ax = fig.add_subplot(2, 3, 6)
ax.axis('off')
ax.text(0.04, 0.83, 'Problema de Poisson 2D', fontsize=13, weight='bold')
ax.text(0.04, 0.65, f'Resolución del barrido: N = {N_FIGURA}', fontsize=12)
ax.text(0.04, 0.49, f'Puntos de evaluación: {numero_puntos}', fontsize=12)
ax.text(0.04, 0.33, 'Error mostrado: |aproximación - exacta|', fontsize=11)
ax.text(0.04, 0.17, 'Escala vertical común para los dos errores', fontsize=10)
fig.suptitle('Poisson 2D: soluciones y errores puntuales (misma cuadrícula)', fontsize=16)
guardar_figura('comparacion_3d_soluciones_errores_Poisson2D.png')


# ----------------------------------------------------------
# Comparación espacial y cuantitativa del error de los tres métodos
# ----------------------------------------------------------
from matplotlib.colors import Normalize

campos = {'FEM': U_fem, 'FVM (FiPy)': U_fipy, 'PINN': U_pinn}
errores = {nombre: np.abs(campo - U_exacta)
           for nombre, campo in campos.items()}
max_comun = max(1.e-12, *(float(e.max()) for e in errores.values()))

# A) Mapas de error absoluto: una única escala de color para FEM/FVM/PINN.
fig, ejes = plt.subplots(1, 3, figsize=(16, 4.8), sharex=True, sharey=True)
for ax, (nombre, e_abs) in zip(ejes, errores.items()):
    im = ax.imshow(e_abs.T, origin='lower', extent=(-1,1,-1,1),
                   vmin=0, vmax=max_comun, cmap='magma', aspect='equal')
    ax.set_title(f'|Error|: {nombre}')
    ax.set_xlabel('x'); ax.set_ylabel('y')
fig.colorbar(im, ax=ejes, label='Error absoluto puntual', fraction=0.03, pad=0.02)
fig.suptitle(f'Distribución espacial del error, N={N_FIGURA}')
# Evitamos tight_layout incompatible con el colorbar común de tres ejes.
fig.subplots_adjust(top=0.82, right=0.89, wspace=0.18)
plt.savefig(SALIDA/'errores_espaciales_FEM_FVM_PINN.png', dpi=180, bbox_inches='tight')
plt.show(); plt.close(fig)

# B) Tabla de errores sobre la misma cuadrícula interior de prueba.
# L2 relativo = ||u_aprox - u*||_2 / ||u*||_2 (norma discreta).
# L-infinito absoluto = máximo puntual de |u_aprox-u*|.
filas_metricas = []
for nombre, campo in campos.items():
    diferencia = campo - U_exacta
    filas_metricas.append({
        'metodo': nombre,
        'N': N_FIGURA,
        'error_L2_rel': float(np.linalg.norm(diferencia.ravel()) /
                              np.linalg.norm(U_exacta.ravel())),
        'error_max_abs': float(np.max(np.abs(diferencia))),
        'error_RMSE': float(np.sqrt(np.mean(diferencia**2))),
        'puntos_evaluacion': numero_puntos,
    })
metricas_visuales = guardar_csv('errores_comparados_2d.csv', filas_metricas)
print(metricas_visuales.to_string(index=False))

# C) Comparación de las dos métricas, sin atribuirlas al costo de cálculo.
fig, ejes = plt.subplots(1, 2, figsize=(12, 4.5))
for ax, columna, titulo in zip(
    ejes,
    ['error_L2_rel', 'error_max_abs'],
    [r'Error relativo $L^2$', r'Error absoluto máximo $L^\infty$'],
):
    ax.bar(metricas_visuales['metodo'], metricas_visuales[columna],
           color=['#4C78A8','#F58518','#54A24B'])
    ax.set_yscale('log')
    ax.set_title(titulo)
    ax.set_ylabel('Error (escala logarítmica)')
    ax.grid(True, axis='y', which='both', alpha=0.3)
    ax.set_axisbelow(True)
fig.suptitle(f'FEM, FiPy y PINN: comparación de errores para N={N_FIGURA}')
guardar_figura('errores_globales_comparados_2d.png')

