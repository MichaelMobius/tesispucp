# -*- coding: utf-8 -*-
# Poisson 1D: tangente hiperbólica con observaciones
# Fuente: Tesis_PUCP_PINN_Poisson_Experimentos.ipynb (ejecución del 29/10/2026)

# Poisson 1D con datos: tangente hiperbólica
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
CFG = {'ep_poisson1d': 220 if MODO == 'demostracion' else 5000}

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

print('Poisson 1D: tanh con observaciones:', DEVICE, '| salida:', SALIDA)

import torch
from torch import nn
import matplotlib.pyplot as plt
import numpy as np

# Definimos el dominio
domain = [-1.0, 1.0]

# Definimos la red neuronal
class SimpleNN(nn.Module):
    def __init__(self):
        super(SimpleNN, self).__init__()
        self.linear_tanh_stack = nn.Sequential(
            nn.Linear(1, 50),
            nn.Tanh(),
            nn.Linear(50, 50),
            nn.Tanh(),
            nn.Linear(50, 1),
        )

    def forward(self, x):
        out = self.linear_tanh_stack(x)
        return out

# Definimos la derivada de 2do orden usando PyTorch autograd
def d2f_dx2(f: SimpleNN, x: torch.Tensor) -> torch.Tensor:
    u = f(x)
    du_dx = torch.autograd.grad(
        u, x, grad_outputs=torch.ones_like(u), create_graph=True
    )[0]
    d2u_dx2 = torch.autograd.grad(
        du_dx, x, grad_outputs=torch.ones_like(du_dx), create_graph=True
    )[0]
    return d2u_dx2

# Generamos los puntos de colocación
x_collocation = torch.linspace(domain[0], domain[1], steps=50, requires_grad=True).reshape(-1, 1)

# Entrenamos los data points
x_train = torch.tensor([[-0.8], [-0.4], [0.0], [0.4], [0.8]], dtype=torch.float32)
y_train = torch.tanh(x_train)

# Definimos la función de pérdida
def compute_loss(nn: SimpleNN, x_collocation: torch.Tensor,
                 x_train: torch.Tensor, y_train: torch.Tensor,
                 devolver_componentes: bool = False) -> torch.float:
    # PDE loss
    pde_loss = d2f_dx2(nn, x_collocation) + 2 * ((1 / torch.cosh(x_collocation)) ** 2) * torch.tanh(x_collocation)
    pde_loss = pde_loss.pow(2).mean()

    # Boundary conditions loss
    bc_loss_1 = (nn(torch.tensor([domain[0]], requires_grad=True))-torch.tanh(torch.tensor([domain[0]], requires_grad=True))).pow(2)
    bc_loss_2 = (nn(torch.tensor([domain[1]], requires_grad=True))-torch.tanh(torch.tensor([domain[1]], requires_grad=True))).pow(2)

    # Data loss (MSE)
    mse_loss = torch.nn.MSELoss()(nn(x_train), y_train)

    # Total loss
    tot_loss = pde_loss + bc_loss_1 + bc_loss_2 + mse_loss

    if devolver_componentes:
        return tot_loss, pde_loss, bc_loss_1 + bc_loss_2, mse_loss
    return tot_loss

model = SimpleNN()
optimizer = torch.optim.Adam(model.parameters(), lr=1e-3)
scheduler = torch.optim.lr_scheduler.StepLR(optimizer, step_size=500, gamma=0.5)

# Histórico de entrenamiento del problema con cinco observaciones.
historial_poisson_tanh_datos = []

# Entrenamos el modelo
for ep in range(CFG['ep_poisson1d']):
    loss, j_pde, j_frontera, j_datos = compute_loss(
        model, x_collocation, x_train, y_train, devolver_componentes=True)

    # Valor de cada componente antes de actualizar los pesos.
    historial_poisson_tanh_datos.append({
        'epoca': ep + 1, 'perdida': float(loss.detach()),
        'pde': float(j_pde.detach()), 'bc': float(j_frontera.detach()),
        'datos': float(j_datos.detach())})

    optimizer.zero_grad()
    loss.backward()
    optimizer.step()
    scheduler.step()

    if ep % 500 == 0:
        print(f"Epoch: {ep}, Loss: {loss.item():.6f}")
# Permite regenerar la curva de convergencia de la pérdida.
guardar_csv('historial_poisson_tanh_con_datos.csv', historial_poisson_tanh_datos)


# Plotting
x_test = torch.linspace(domain[0], domain[1], steps=100).reshape(-1, 1)
with torch.no_grad():
    y_pred = model(x_test)

# Solución analítica y Solución NN
analytical_sol = torch.tanh(x_test)

plt.plot(x_test, y_pred, label="NN Solution")
plt.plot(x_test, analytical_sol, label="Analytical Solution", linestyle='dashed')
plt.scatter(x_train.detach().numpy(), y_train.detach().numpy(), label="Observation Data", color="blue")
plt.xlabel("x")
plt.ylabel("u(x)")
plt.title("Solution to the Poisson Equation with Dirichlet BCs")
plt.legend()
plt.savefig(SALIDA/'poisson_1d_tanh_con_datos.png', dpi=180, bbox_inches='tight')
plt.show()

# ----------------------------------------------------------
# Evolución de la pérdida para Poisson 1D con observaciones
# ----------------------------------------------------------
epocas = [fila['epoca'] for fila in historial_poisson_tanh_datos]
perdidas = [fila['perdida'] for fila in historial_poisson_tanh_datos]

plt.figure(figsize=(8, 4))
plt.semilogy(epocas, perdidas, label='Pérdida total PINN')
plt.xlabel('Épocas')
plt.ylabel('Pérdida total')
plt.title('Poisson 1D: tanh(x) con observaciones')
plt.grid(True, which='both', alpha=0.3)
plt.legend()
guardar_figura('perdida_poisson_tanh_con_datos.png')

# ----------------------------------------------------------
# Desglose de la función de pérdida del experimento
# ----------------------------------------------------------
# IMPORTANTE: estas curvas son términos de la función objetivo,
# NO los errores relativos L2/H1 respecto de la solución exacta.
# Los valores se muestran en escala semilogarítmica sin aplicar log a los CSV.
import pandas as pd

tabla = pd.DataFrame(historial_poisson_tanh_datos)
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
guardar_figura('desglose_perdidas_poisson_tanh_con_datos.png')



# ----------------------------------------------------------
# Figura didáctica: solución (lineal) y pérdidas (semilog)
# ----------------------------------------------------------
# Se replica la disposición del gráfico de referencia de la tesis.
# Las curvas de pérdidas son penalizaciones entrenadas, no error L2/H1.
fig, (ax_sup, ax_inf) = plt.subplots(2, 1, figsize=(10.5, 8.0))
ax_sup.plot(x_test.detach().cpu().numpy(), y_pred.detach().cpu().numpy(),
            label='Solución PINN', linewidth=1.8)
ax_sup.plot(x_test.detach().cpu().numpy(), analytical_sol.detach().cpu().numpy(),
            '--', label='Solución analítica', linewidth=1.8)
ax_sup.scatter(x_train.detach().cpu().numpy(), y_train.detach().cpu().numpy(),
               color='tab:blue', label='Observaciones', zorder=4)
ax_sup.set(xlabel='x', ylabel='u(x)', title='Poisson 1D con observaciones')
ax_sup.grid(alpha=.25)
ax_sup.legend()
tabla_componentes = pd.DataFrame(historial_poisson_tanh_datos)
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
guardar_figura('solucion_y_componentes_poisson_tanh_con_datos.png')

