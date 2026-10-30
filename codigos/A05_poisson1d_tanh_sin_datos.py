# -*- coding: utf-8 -*-
# Poisson 1D: tangente hiperbólica sin observaciones
# Fuente: Tesis_PUCP_PINN_Poisson_Experimentos.ipynb (ejecución del 29/10/2026)

# Poisson 1D sin observaciones interiores
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

print('Poisson 1D: tanh sin observaciones:', DEVICE, '| salida:', SALIDA)

import torch
from torch import nn
import matplotlib.pyplot as plt
import numpy as np

# --- Configuración ---
domain = [-1.0, 1.0]
EPOCHS = CFG['ep_poisson1d']
N_COLLOCATION = 100

# --- Red neuronal ---
class PINN(nn.Module):
    def __init__(self):
        super(PINN, self).__init__()
        self.net = nn.Sequential(
            nn.Linear(1, 50),
            nn.Tanh(),
            nn.Linear(50, 50),
            nn.Tanh(),
            nn.Linear(50, 1)
        )

    def forward(self, x):
        return self.net(x)

# --- Derivada segunda ---
def d2f_dx2(f, x):
    x.requires_grad_(True)
    u = f(x)
    du = torch.autograd.grad(u, x, grad_outputs=torch.ones_like(u), create_graph=True)[0]
    d2u = torch.autograd.grad(du, x, grad_outputs=torch.ones_like(du), create_graph=True)[0]
    return d2u

# --- Función de pérdida ---
def compute_loss(model, x_collocation, devolver_componentes=False):
    # PDE residual
    d2u = d2f_dx2(model, x_collocation)
    f_rhs = -2 * (1 / torch.cosh(x_collocation))**2 * torch.tanh(x_collocation)
    pde_loss = ((d2u - f_rhs) ** 2).mean()

    # Condiciones de frontera
    x_bc = torch.tensor([[-1.0], [1.0]], requires_grad=True)
    u_bc = torch.tanh(x_bc)
    bc_loss = torch.nn.MSELoss()(model(x_bc), u_bc)

    perdida_total = pde_loss + bc_loss
    if devolver_componentes:
        return perdida_total, pde_loss, bc_loss
    return perdida_total

# --- Entrenamiento ---
model = PINN()
optimizer = torch.optim.Adam(model.parameters(), lr=1e-3)
scheduler = torch.optim.lr_scheduler.StepLR(optimizer, step_size=1000, gamma=0.5)

x_collocation = torch.linspace(domain[0], domain[1], N_COLLOCATION).reshape(-1, 1)
x_collocation.requires_grad_(True)

# Registramos la pérdida para analizar el entrenamiento.
historial_poisson_tanh_sin_datos = []

for epoch in range(EPOCHS):
    loss, j_pde, j_frontera = compute_loss(
        model, x_collocation, devolver_componentes=True)
    historial_poisson_tanh_sin_datos.append({
        'epoca': epoch + 1, 'perdida': float(loss.detach()),
        'pde': float(j_pde.detach()), 'bc': float(j_frontera.detach())})
    optimizer.zero_grad()
    loss.backward()
    optimizer.step()
    scheduler.step()

    if epoch % 1000 == 0:
        print(f"Epoch {epoch}, Loss: {loss.item():.4e}")

# --- Comparación visual ---
x_plot = torch.linspace(domain[0], domain[1], 500).reshape(-1, 1)
u_pred = model(x_plot).detach()
u_exact = torch.tanh(x_plot)

plt.figure(figsize=(10, 6))
plt.plot(x_plot, u_exact, label='Solución exacta', linewidth=2)
plt.plot(x_plot, u_pred, '--', label='Solución PINN', linewidth=2)
plt.xlabel('x')
plt.ylabel('u(x)')
plt.title('Solución de la EDP de Poisson 1D con PINN')
plt.legend()
plt.grid(True)
# La solución se representa linealmente, sin transformar u(x).
guardar_figura('poisson_1d_tanh_sin_datos.png')

# --- Cálculo de errores L2 y H1 ---
def compute_l2_and_h1_errors(model, x_grid):
    x_grid = x_grid.clone().detach().requires_grad_(True)
    u_pred = model(x_grid)
    u_true = torch.tanh(x_grid)

    du_pred = torch.autograd.grad(u_pred, x_grid, grad_outputs=torch.ones_like(u_pred), create_graph=True)[0]
    du_true = 1 - torch.tanh(x_grid)**2  # sech^2(x)

    dx = x_grid[1] - x_grid[0]

    l2_num = torch.sqrt(torch.sum((u_pred - u_true) ** 2) * dx)
    l2_den = torch.sqrt(torch.sum((u_true) ** 2) * dx)
    l2_rel_error = (l2_num / l2_den).item()

    h1_num = torch.sqrt(torch.sum((du_pred - du_true) ** 2) * dx)
    h1_den = torch.sqrt(torch.sum((du_true) ** 2) * dx)
    h1_rel_error = torch.sqrt((l2_num**2 + h1_num**2) / (l2_den**2 + h1_den**2)).item()

    return l2_rel_error, h1_rel_error

x_fine = torch.linspace(domain[0], domain[1], 1000).reshape(-1, 1)
l2_err, h1_err = compute_l2_and_h1_errors(model, x_fine)

print(f"\nOK Error relativo L2: {l2_err:.4e}")
print(f"OK Error relativo H1: {h1_err:.4e}")


# Guardar las métricas del experimento sin datos interiores.
guardar_csv('errores_poisson_1d_sin_datos.csv', [{'error_L2_rel': l2_err, 'error_H1_rel': h1_err, 'epocas': EPOCHS, 'semilla': SEMILLA}])
# Guardamos la historia original de pérdidas junto con los errores.
guardar_csv('historial_poisson_tanh_sin_datos.csv', historial_poisson_tanh_sin_datos)


# ----------------------------------------------------------
# Evolución de la pérdida para Poisson 1D sin observaciones
# ----------------------------------------------------------
epocas = [fila['epoca'] for fila in historial_poisson_tanh_sin_datos]
perdidas = [fila['perdida'] for fila in historial_poisson_tanh_sin_datos]

plt.figure(figsize=(8, 4))
plt.semilogy(epocas, perdidas, label='Pérdida total PINN')
plt.xlabel('Épocas')
plt.ylabel('Pérdida total')
plt.title('Poisson 1D: tanh(x) sin observaciones')
plt.grid(True, which='both', alpha=0.3)
plt.legend()
guardar_figura('perdida_poisson_tanh_sin_datos.png')

# ----------------------------------------------------------
# Desglose de la función de pérdida del experimento
# ----------------------------------------------------------
# IMPORTANTE: estas curvas son términos de la función objetivo,
# NO los errores relativos L2/H1 respecto de la solución exacta.
# Los valores se muestran en escala semilogarítmica sin aplicar log a los CSV.
import pandas as pd

tabla = pd.DataFrame(historial_poisson_tanh_sin_datos)
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 4.5))
# La línea negra suma los términos registrados, con sus pesos efectivos.
ax1.semilogy(tabla['epoca'], tabla['perdida'], color='black', lw=2,
             label='Pérdida total')
ax1.semilogy(tabla['epoca'], tabla['pde'].clip(lower=1e-30), label='Residuo EDP')
ax1.semilogy(tabla['epoca'], tabla['bc'].clip(lower=1e-30), label='Frontera')
ax1.set(xlabel='Épocas', ylabel='Pérdida (escala logarítmica)',
        title='Evolución de las componentes')
ax1.grid(True, which='both', alpha=.3)
ax1.legend(fontsize=9)

# Participación porcentual: sirve para ver qué término domina el objetivo.
# Todos los términos se evalúan antes de cada actualización de pesos.
componentes = np.column_stack([tabla['pde'].to_numpy(), tabla['bc'].to_numpy()])
totales = componentes.sum(axis=1)
porcentajes = 100 * componentes / np.maximum(totales[:,None], 1e-30)
ax2.stackplot(tabla['epoca'], *porcentajes.T, labels=['Residuo EDP', 'Frontera'], alpha=.85)
ax2.set(xlabel='Épocas', ylabel='Contribución a la pérdida (%)',
        title='Participación de cada término', ylim=(0, 100))
ax2.grid(True, alpha=.2)
ax2.legend(loc='upper right', fontsize=8)
plt.tight_layout()
guardar_figura('desglose_perdidas_poisson_tanh_sin_datos.png')



# ----------------------------------------------------------
# Figura didáctica: solución (lineal) y pérdidas (semilog)
# ----------------------------------------------------------
# Se replica la disposición del gráfico de referencia de la tesis.
# Las curvas de pérdidas son penalizaciones entrenadas, no error L2/H1.
fig, (ax_sup, ax_inf) = plt.subplots(2, 1, figsize=(10.5, 8.0))
ax_sup.plot(x_plot.detach().cpu().numpy(), u_pred.detach().cpu().numpy(),
            label='Solución PINN', linewidth=1.8)
ax_sup.plot(x_plot.detach().cpu().numpy(), u_exact.detach().cpu().numpy(),
            '--', label='Solución analítica', linewidth=1.8)
ax_sup.set(xlabel='x', ylabel='u(x)', title='Poisson 1D sin observaciones interiores')
ax_sup.grid(alpha=.25)
ax_sup.legend()
tabla_componentes = pd.DataFrame(historial_poisson_tanh_sin_datos)
ax_inf.semilogy(tabla_componentes['epoca'], tabla_componentes['perdida'],
                color='black', linewidth=2, label='Pérdida total')
ax_inf.semilogy(tabla_componentes['epoca'], tabla_componentes['pde'].clip(lower=1e-30),
                label='Pérdida EDP')
ax_inf.semilogy(tabla_componentes['epoca'], tabla_componentes['bc'].clip(lower=1e-30),
                label='Pérdida frontera')
ax_inf.set(xlabel='Épocas', ylabel='Contribución a la pérdida',
           title='Evolución de la función de pérdida y sus componentes')
ax_inf.legend()
ax_inf.grid(True, which='both', alpha=.25)
guardar_figura('solucion_y_componentes_poisson_tanh_sin_datos.png')

