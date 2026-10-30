# -*- coding: utf-8 -*-
# Ecuación logística
# Fuente: Tesis_PUCP_PINN_Poisson_Experimentos.ipynb (ejecución del 29/10/2026)

# Ecuación logística
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
CFG = {'ep_logistica': 200 if MODO == 'demostracion' else 2000}

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

print('Ecuación logística:', DEVICE, '| salida:', SALIDA)

# Red neuronal declarada localmente: NO depende de regresión.
# Definimos una red neuronal simple para la regresión

class simple_NN(nn.Module):
    def __init__(self):
        super(simple_NN, self).__init__()
        self.linear_tanh_stack = nn.Sequential(
            nn.Linear(1, 16),
            nn.Tanh(),
            nn.Linear(16, 32),
            nn.Tanh(),
            nn.Linear(32, 16),
            nn.Tanh(),
            nn.Linear(16, 1),
        )

    def forward(self, x):
        out = self.linear_tanh_stack(x)
        return out
# Dominio y cuadrícula de evaluación propios de la ecuación logística.
domain = [0.0, 1.5]
x_eval = torch.linspace(*domain, steps=100).reshape(-1, 1)

#Definimos el valor de la tasa e indicamos el valor que toma f en la condición inicial.

R = 1.0
ft0 = 0.5

def df(f: simple_NN, x: torch.Tensor = None, order: int = 1) -> torch.Tensor:
    """Calcula la derivada de la red neuronal con respecto a las características de entrada usando el motor autograd de PyTorch"""
    df_value = f(x)
    for _ in range(order):
        df_value = torch.autograd.grad(
            df_value,
            x,
            grad_outputs=torch.ones_like(x),
            create_graph=True,
            retain_graph=True,
        )[0]

    return df_value

#Generar 10 puntos de colocación distribuidos uniformemente

t = torch.linspace(domain[0], domain[1], steps=10, requires_grad=True).reshape(-1, 1)

# Envuelve todo en una función
def compute_loss(nn: simple_NN,
                 t: torch.Tensor = None,
                 x: torch.Tensor = None,
                 y: torch.Tensor = None,
                 devolver_componentes: bool = False) -> torch.float:
    """Calcula la función de pérdida completa como pérdida de la EDP + pérdida de la condición de frontera
Esta función de pérdida está completamente definida con tensores diferenciables, por lo tanto,
se puede aplicar el método .backward() a ella
    """

    pde_loss = df(nn, t) - R * nn(t) * (1 - nn(t))
    pde_loss = pde_loss.pow(2).mean()

    boundary = torch.Tensor([0.0])
    boundary.requires_grad = True
    bc_loss = nn(boundary) - ft0
    bc_loss = bc_loss.pow(2)

    mse_loss = torch.nn.MSELoss()(nn(x), y)

    tot_loss = pde_loss + bc_loss + mse_loss

    if devolver_componentes:
        return tot_loss, pde_loss, bc_loss.mean(), mse_loss
    return tot_loss

# Definimos la base de datos

x_train = torch.tensor([[1.1437e-04],
        [1.4676e-01],
        [3.0233e-01],
        [4.1702e-01],
        [7.2032e-01]], dtype=torch.float32)
y_train = torch.tensor([[0.49769],
    [0.54271],
    [0.58026],
    [0.60909],
    [0.67524]], dtype=torch.float32)

model = simple_NN()
optimizer = torch.optim.Adam(model.parameters(), lr=1e-2)

# Histórico del error para graficar el descenso de la pérdida.
historial_logistica = []

# Entrenamiento
for ep in range(CFG['ep_logistica']):

    loss, j_pde, j_frontera, j_datos = compute_loss(
        model, t, x_train, y_train, devolver_componentes=True)

    # Cada componente se calcula en el mismo paso, antes de actualizar la red.
    historial_logistica.append({
        'epoca': ep + 1, 'perdida': float(loss.detach()),
        'pde': float(j_pde.detach()), 'bc': float(j_frontera.detach()),
        'datos': float(j_datos.detach())})

    # Backpropagation
    optimizer.zero_grad()
    loss.backward()
    optimizer.step()

    if ep % 200 == 0:
        print(f"epoch: {ep}, loss: {loss.item():>7f}")
# Guardamos los datos originales, no sus logaritmos.
guardar_csv('historial_logistica.csv', historial_logistica)


# solución numérica
def logistic_eq_fn(t, f):
    return R * f * (1 - f)

numeric_solution = solve_ivp(
    logistic_eq_fn, domain, [ft0], t_eval=x_eval.squeeze().detach().numpy()
)

f_colloc = solve_ivp(
    logistic_eq_fn, domain, [ft0], t_eval=t.squeeze().detach().numpy()
).y.T

# evaluación del modelo en el dominio [0, 1.5]
with torch.no_grad():
    f_eval = model(x_eval)

# plotting
fig, ax = plt.subplots(figsize=(12, 5))
ax.scatter(t.detach().numpy(), f_colloc, label="Puntos de colocación", color="magenta", alpha=0.75)
ax.scatter(x_train.detach().numpy(), y_train.detach().numpy(), label="Datos observados", color="blue")
ax.plot(x_eval.detach().numpy(), f_eval.detach().numpy(), label="solución NN", color="black")
ax.plot(x_eval.detach().numpy(), numeric_solution.y.T,
        label="solución numérica de referencia", color="magenta", alpha=0.75)
ax.set(title="La ecuación logística resuelta con NNs", xlabel="t", ylabel="f(t)")
ax.legend();

# Guardar la comparación con la solución de la EDO.
fig.savefig(SALIDA/'logistica_edo.png', dpi=180, bbox_inches='tight')
plt.show()

# ----------------------------------------------------------
# Función de pérdida de la ecuación logística: escala semilog
# ----------------------------------------------------------
epocas = [fila['epoca'] for fila in historial_logistica]
perdidas = [fila['perdida'] for fila in historial_logistica]

plt.figure(figsize=(8, 4))
plt.semilogy(epocas, perdidas, label='Pérdida total PINN')
plt.xlabel('Épocas')
plt.ylabel('Pérdida total')
plt.title('Ecuación logística: evolución de la pérdida')
plt.grid(True, which='both', alpha=0.3)
plt.legend()
guardar_figura('perdida_logistica.png')

# ----------------------------------------------------------
# Desglose de la función de pérdida del experimento
# ----------------------------------------------------------
# IMPORTANTE: estas curvas son términos de la función objetivo,
# NO los errores relativos L2/H1 respecto de la solución exacta.
# Los valores se muestran en escala semilogarítmica sin aplicar log a los CSV.
import pandas as pd

tabla = pd.DataFrame(historial_logistica)
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 4.5))
# La línea negra suma los términos registrados, con sus pesos efectivos.
ax1.semilogy(tabla['epoca'], tabla['perdida'], color='black', lw=2,
             label='Pérdida total')
ax1.semilogy(tabla['epoca'], tabla['pde'].clip(lower=1e-30), label='Residuo EDP')
ax1.semilogy(tabla['epoca'], tabla['bc'].clip(lower=1e-30), label='Frontera')
ax1.semilogy(tabla['epoca'], tabla['datos'].clip(lower=1e-30), label='Observaciones')
ax1.set(xlabel='Épocas', ylabel='Pérdida (escala logarítmica)',
        title='Evolución de las componentes')
ax1.grid(True, which='both', alpha=.3)
ax1.legend(fontsize=9)

# Participación porcentual: sirve para ver qué término domina el objetivo.
# Todos los términos se evalúan antes de cada actualización de pesos.
componentes = np.column_stack([tabla['pde'].to_numpy(), tabla['bc'].to_numpy(), tabla['datos'].to_numpy()])
totales = componentes.sum(axis=1)
porcentajes = 100 * componentes / np.maximum(totales[:,None], 1e-30)
ax2.stackplot(tabla['epoca'], *porcentajes.T, labels=['Residuo EDP', 'Frontera', 'Observaciones'], alpha=.85)
ax2.set(xlabel='Épocas', ylabel='Contribución a la pérdida (%)',
        title='Participación de cada término', ylim=(0, 100))
ax2.grid(True, alpha=.2)
ax2.legend(loc='upper right', fontsize=8)
plt.tight_layout()
guardar_figura('desglose_perdidas_logistica.png')



# ----------------------------------------------------------
# Figura didáctica: solución (lineal) y pérdidas (semilog)
# ----------------------------------------------------------
# Se replica la disposición del gráfico de referencia de la tesis.
# Las curvas de pérdidas son penalizaciones entrenadas, no error L2/H1.
fig, (ax_sup, ax_inf) = plt.subplots(2, 1, figsize=(10.5, 8.0))
ax_sup.plot(x_eval.detach().cpu().numpy(), f_eval.detach().cpu().numpy(),
            label='Solución neuronal', linewidth=1.8)
ax_sup.plot(x_eval.detach().cpu().numpy(), numeric_solution.y.T,
            '--', label='Solución de referencia', linewidth=1.8)
ax_sup.scatter(x_train.detach().cpu().numpy(), y_train.detach().cpu().numpy(),
               color='tab:blue', label='Observaciones', zorder=4)
ax_sup.set(xlabel='t', ylabel='u(t)', title='Ecuación logística')
ax_sup.grid(alpha=.25)
ax_sup.legend()
tabla_componentes = pd.DataFrame(historial_logistica)
ax_inf.semilogy(tabla_componentes['epoca'], tabla_componentes['perdida'],
                color='black', linewidth=2, label='Pérdida total')
ax_inf.semilogy(tabla_componentes['epoca'], tabla_componentes['pde'].clip(lower=1e-30),
                label='Pérdida EDP')
ax_inf.semilogy(tabla_componentes['epoca'], tabla_componentes['bc'].clip(lower=1e-30),
                label='Pérdida frontera')
ax_inf.semilogy(tabla_componentes['epoca'], tabla_componentes['datos'].clip(lower=1e-30),
                label='Pérdida datos')
ax_inf.set(xlabel='Épocas', ylabel='Contribución a la pérdida',
           title='Evolución de la función de pérdida y sus componentes')
ax_inf.legend()
ax_inf.grid(True, which='both', alpha=.25)
guardar_figura('solucion_y_componentes_logistica.png')

