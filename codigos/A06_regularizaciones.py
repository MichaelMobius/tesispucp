# -*- coding: utf-8 -*-
# PINN, penalización media y LIPR
# Fuente: Tesis_PUCP_PINN_Poisson_Experimentos.ipynb (ejecución del 29/10/2026)

# PINN y regularización de tercer orden
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
    'n_reg': [6,16] if MODO=='demostracion' else [10,20,40,80,160,320,640],
    'semillas': [SEMILLA] if MODO=='demostracion' else [SEMILLA,SEMILLA+1,SEMILLA+2],
    'adam_reg': 35 if MODO=='demostracion' else 4000,
    'lbfgs_reg': 0 if MODO=='demostracion' else 350,
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

print('PINN / regularización media / LIPR:', DEVICE, '| salida:', SALIDA)

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

# ----------------------------------------------------------
# Comprobación de la identidad usada en LIPR de Shin (4.1)
# ----------------------------------------------------------
# Se trata de una verificación del funcional discreto, no del
# teorema de convergencia ni de la seminorma continua de Holder.
fijar_semilla(SEMILLA)
modelo_comprobacion = RedPoissonRegularizada().to(DEVICE, dtype=DTYPE_REG)
xi = torch.linspace(-1, 1, 9, device=DEVICE,
                    dtype=DTYPE_REG).reshape(-1, 1)
xb = torch.tensor([[-1.0], [1.0]], device=DEVICE, dtype=DTYPE_REG)
lambda_prueba = 9 ** (-1.5)

# Calcular directamente max |u_xxx|^2 a partir de autodiferenciación.
_x = xi.clone().detach().requires_grad_(True)
_, _, _uxx, _uxxx = derivadas_hasta_tercera(modelo_comprobacion, _x)
maximo_manual = _uxxx.square().max()
media_manual = _uxxx.square().mean()

perdida_lipr, _, _, regularizador_lipr = componentes_perdida(
    modelo_comprobacion, xi, xb, 'LIPR-Shin', lambda_prueba)
perdida_media, _, _, regularizador_media = componentes_perdida(
    modelo_comprobacion, xi, xb, 'Media', lambda_prueba)
perdida_pinn, _, _, _ = componentes_perdida(
    modelo_comprobacion, xi, xb, 'PINN', lambda_prueba)

assert torch.allclose(regularizador_lipr, maximo_manual, atol=1e-11, rtol=1e-9)
assert torch.allclose(regularizador_media, media_manual, atol=1e-11, rtol=1e-9)
assert regularizador_lipr >= regularizador_media
assert torch.allclose(perdida_lipr-perdida_pinn,
                      lambda_prueba*maximo_manual, atol=1e-11, rtol=1e-9)
assert torch.allclose(perdida_media-perdida_pinn,
                      lambda_prueba*media_manual, atol=1e-11, rtol=1e-9)
print('Verificación de la pérdida LIPR discreta (Shin, Ec. 4.1): correcta.')
print(f'Regularizador máximo: {regularizador_lipr.item():.6e}')
print(f'Regularizador medio:  {regularizador_media.item():.6e}')


# ----------------------------------------------------------
# Entrenamiento comparable de los tres métodos
# ----------------------------------------------------------
import copy
METODOS = ['PINN', 'Media', 'LIPR-Shin']
registros_regularizacion = []
# Guardamos solo un caso representativo para mostrar la pérdida por época.
# Todos los tamaños y semillas siguen formando parte del barrido de errores.
historial_regularizacion_adam = []

for N_f in CFG['n_reg']:
    # Puntos equiespaciados del problema [-1,1].
    puntos_f = torch.linspace(-1, 1, N_f, device=DEVICE,
                              dtype=DTYPE_REG).reshape(-1, 1)
    puntos_b = torch.tensor([[-1.0], [1.0]], device=DEVICE, dtype=DTYPE_REG)
    lambda_r = N_f ** (-1.5)

    for semilla in CFG['semillas']:
        fijar_semilla(semilla)
        red_inicial = RedPoissonRegularizada().to(DEVICE, dtype=DTYPE_REG)
        estado_inicial = copy.deepcopy(red_inicial.state_dict())

        for metodo in METODOS:
            # MISMA inicialización y MISMOS puntos para comparar los métodos.
            modelo = RedPoissonRegularizada().to(DEVICE, dtype=DTYPE_REG)
            modelo.load_state_dict(estado_inicial)
            optimizador = torch.optim.Adam(modelo.parameters(), lr=1e-3)
            comienzo = time.perf_counter()

            # Fase I: optimización por Adam.
            for epoca in range(CFG['adam_reg']):
                optimizador.zero_grad(set_to_none=True)
                perdida, j_pde, j_frontera, r_sin_peso = componentes_perdida(
                    modelo, puntos_f, puntos_b, metodo, lambda_r
                )
                if not bool(torch.isfinite(perdida).item()):
                    raise FloatingPointError(f'Pérdida no finita en {N_f}/{metodo}')
                # Registrar el proceso Adam para el mayor N_f y la primera semilla.
                # La pérdida de cada método es diferente: sus valores absolutos
                # NO son una comparación directa de precisión entre modelos.
                if (N_f == max(CFG['n_reg']) and semilla == CFG['semillas'][0]
                    and (epoca == 0 or (epoca + 1) % max(1, CFG['adam_reg']//100) == 0
                         or epoca + 1 == CFG['adam_reg'])):
                    historial_regularizacion_adam.append({
                        'epoca': epoca + 1, 'N_f': N_f, 'semilla': semilla,
                        'metodo': metodo, 'perdida_total': float(perdida.detach()),
                        'pde': float(j_pde.detach()),
                        'bc': float(j_frontera.detach()),
                        'regularizacion_ponderada': float((lambda_r*r_sin_peso).detach())
                    })
                perdida.backward()
                optimizador.step()

            # Fase II: refinamiento con L-BFGS (si se ha solicitado).
            if CFG['lbfgs_reg'] > 0:
                optim_lbfgs = torch.optim.LBFGS(
                    modelo.parameters(), lr=1.0,
                    max_iter=CFG['lbfgs_reg'], history_size=20,
                    line_search_fn='strong_wolfe'
                )
                def closure():
                    optim_lbfgs.zero_grad(set_to_none=True)
                    perdida, _, _, _ = componentes_perdida(
                        modelo, puntos_f, puntos_b, metodo, lambda_r
                    )
                    perdida.backward()
                    return perdida
                optim_lbfgs.step(closure)

            segundos = time.perf_counter() - comienzo
            error_l2, error_h1 = errores_relativos_1d(modelo)
            fila = {
                'N_f': N_f, 'semilla': semilla, 'metodo': metodo,
                'lambda_R': lambda_r,
                'error_L2_rel': error_l2, 'error_H1_rel': error_h1,
                'segundos': segundos,
                'adam_epocas': CFG['adam_reg'],
                'lbfgs_max_iter': CFG['lbfgs_reg'],
                'dispositivo': str(DEVICE), 'protocolo': MODO,
            }
            registros_regularizacion.append(fila)
            # Guardado progresivo: no perder los casos ya ejecutados.
            guardar_csv('regularizacion_casos.csv', registros_regularizacion)
            print(f'N={N_f:4d} | {metodo:10s} | semilla={semilla} | '
                  f'L2={error_l2:.3e} | H1={error_h1:.3e} | {segundos:.1f} s')
# Historial SOLO de Adam; si se activa L-BFGS, su fase no se mezcla en este eje.
guardar_csv('historial_regularizacion_adam.csv', historial_regularizacion_adam)


# ----------------------------------------------------------
# Curvas de convergencia de los errores relativos L2 y H1
# ----------------------------------------------------------
df_reg = pd.DataFrame(registros_regularizacion)
resumen = (df_reg.groupby(['N_f', 'metodo'], as_index=False)
           [['error_L2_rel', 'error_H1_rel', 'segundos']].median())
resumen.to_csv(SALIDA/'regularizacion_resumen.csv', index=False)

plt.figure(figsize=(10, 7))
colores = {'PINN': 'tab:blue', 'Media': 'tab:green', 'LIPR-Shin': 'tab:red'}
for metodo in METODOS:
    tabla = resumen[resumen['metodo'] == metodo].sort_values('N_f')
    plt.loglog(tabla['N_f'], tabla['error_L2_rel'], 'o-',
               label=f'{metodo} -- L2', color=colores[metodo])
    plt.loglog(tabla['N_f'], tabla['error_H1_rel'], 's--',
               label=f'{metodo} -- H1', color=colores[metodo])
plt.xlabel('Número de puntos de colocación $N_f$')
plt.ylabel('Error relativo')
plt.title('Poisson 1D: PINN estándar y regularización de orden superior')
plt.grid(True, which='both', alpha=0.35)
plt.legend(ncol=2)
guardar_figura('figura_4_7_regularizacion.png')

# Las medianas son resultados experimentales del optimizador; no tasas demostradas.

# ----------------------------------------------------------
# Pérdidas de entrenamiento: PINN, media cuadrática y LIPR
# ----------------------------------------------------------
tabla_historial = pd.DataFrame(historial_regularizacion_adam)
plt.figure(figsize=(9, 5))

for metodo in METODOS:
    datos_metodo = tabla_historial[tabla_historial['metodo'] == metodo]
    datos_metodo = datos_metodo.sort_values('epoca')
    plt.semilogy(datos_metodo['epoca'], datos_metodo['perdida_total'],
                 label=metodo)

plt.xlabel('Épocas de optimización Adam')
plt.ylabel('Función de pérdida total de cada método')
plt.title(f'Pérdidas de entrenamiento (N_f={max(CFG["n_reg"])})')
plt.grid(True, which='both', alpha=0.3)
plt.legend()
guardar_figura('perdidas_regularizacion_adam.png')

# ----------------------------------------------------------
# Desglose de las tres funciones de pérdida del estudio LIPR
# ----------------------------------------------------------
# No confundimos la magnitud del regularizador con el error L2/H1.
# La contribución regularizada es lambda_R x R, no R sin ponderar.
fig, ejes = plt.subplots(1, 3, figsize=(16, 4.5), sharex=True)
for eje, metodo in zip(ejes, METODOS):
    datos = tabla_historial[tabla_historial['metodo'] == metodo].sort_values('epoca')
    eje.semilogy(datos['epoca'], datos['perdida_total'], color='black',
                 linewidth=2, label='Total')
    eje.semilogy(datos['epoca'], datos['pde'].clip(lower=1e-30), label='EDP')
    eje.semilogy(datos['epoca'], datos['bc'].clip(lower=1e-30), label='Frontera')
    if metodo != 'PINN':
        eje.semilogy(datos['epoca'],
                     datos['regularizacion_ponderada'].clip(lower=1e-30),
                     label=r'$\lambda_R\,R$')
    eje.set_title(metodo)
    eje.set_xlabel('Épocas Adam')
    eje.grid(True, which='both', alpha=.25)
    eje.legend(fontsize=8)
ejes[0].set_ylabel('Componentes de la pérdida (semilog)')
fig.suptitle(f'Contribuciones al objetivo (N_f={max(CFG["n_reg"])})', fontsize=12)
plt.tight_layout()
guardar_figura('desglose_perdidas_regularizacion.png')

