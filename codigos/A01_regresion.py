# -*- coding: utf-8 -*-
# Regresión simple
# Fuente: Tesis_PUCP_PINN_Poisson_Experimentos.ipynb (ejecución del 29/10/2026)

# Regresión simple
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
CFG = {'ep_regresion': 150 if MODO == 'demostracion' else 1000}

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

print('Regresión simple:', DEVICE, '| salida:', SALIDA)

#Librerías

import torch
from torch import nn
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib.pyplot as plt
from matplotlib import cm

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

# Definimos la base de datos

x_train = torch.tensor([[1.1437e-04],
        [1.4676e-01],
        [3.0233e-01],
        [4.1702e-01],
        [7.2032e-01]], dtype=torch.float32)
y_train = torch.tensor([[1.0000],
        [1.0141],
        [1.0456],
        [1.0753],
        [1.1565]], dtype=torch.float32)

# Inicializamos el modelo
model = simple_NN()

# definimos la función de pérdida y el optimizador
loss_fn = nn.MSELoss()
optimizer = torch.optim.Adam(model.parameters(), lr=1e-2)

# Guardamos la pérdida para estudiar el aprendizaje en escala semilogarítmica.
historial_regresion = []

# Entrenamiento
for ep in range(CFG['ep_regresion']):

    # Calcula el error
    pred = model(x_train)
    loss = loss_fn(pred, y_train)

    # Guardamos la pérdida SIN transformarla a logaritmos.
    historial_regresion.append({'epoca': ep + 1, 'perdida': float(loss.detach())})

    # Backpropagation
    optimizer.zero_grad()
    loss.backward()
    optimizer.step()

    if ep % 200 == 0:
        print(f"epoch: {ep}, loss: {loss.item():>7f}")
# CSV con los valores reales de la función de pérdida.
guardar_csv('historial_regresion.csv', historial_regresion)


# evaluamos el modelo en todos los data points del dominio
domain = [0.0, 1.5]
x_eval = torch.linspace(domain[0], domain[1], steps=100).reshape(-1, 1)
with torch.no_grad():
    f_eval = model(x_eval)

# plotting
fig, ax = plt.subplots(figsize=(12, 5))
ax.scatter(x_train.detach().numpy(), y_train.detach().numpy(), label="Training data", color="blue")
ax.plot(x_eval.detach().numpy(), f_eval.detach().numpy(), label="NN approximation", color="black")
ax.set(title="Neural Network Regression", xlabel="$x$", ylabel="$y$")
ax.legend();

# Guardar la aproximación de regresión.
fig.savefig(SALIDA/'regresion_simple.png', dpi=180, bbox_inches='tight')
plt.show()

# ----------------------------------------------------------
# Evolución del error cuadrático medio durante la regresión
# ----------------------------------------------------------
# semilogy cambia únicamente la escala de visualización.
# Los valores guardados en el CSV siguen siendo los errores originales.
epocas = [fila['epoca'] for fila in historial_regresion]
perdidas = [fila['perdida'] for fila in historial_regresion]

plt.figure(figsize=(8, 4))
plt.semilogy(epocas, perdidas, label='MSE de entrenamiento')
plt.xlabel('Épocas')
plt.ylabel('Error cuadrático medio (MSE)')
plt.title('Regresión: evolución de la función de pérdida')
plt.grid(True, which='both', alpha=0.3)
plt.legend()
guardar_figura('perdida_regresion.png')
