# -*- coding: utf-8 -*-
# Reproducción Shin: Dirichlet fuerte
# Versión corregida, solo para nuevas ejecuciones. El original se conserva como *_historico.py.

# Problemas elípticos de Shin
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
SALIDA = SALIDA / "shin_oscilatorio_objetivo_Nf_corregido_v1"  # no reutilizar CSV anteriores
SALIDA.mkdir(parents=True, exist_ok=True)

def guardar_csv(nombre, filas):
    tabla = pd.DataFrame(filas)
    if len(tabla):
        tabla.to_csv(SALIDA / nombre, index=False)
    return tabla

def guardar_figura(nombre):
    fig = plt.gcf()
    if fig.get_layout_engine() is None:
        fig.tight_layout()
    fig.savefig(SALIDA / nombre, dpi=180, bbox_inches='tight')
    plt.show()
    plt.close(fig)

print('Reproducciones de Shin, Figuras 3 y 4:', DEVICE, '| salida:', SALIDA)

# Protocolo de reproducción publicado frente a exploración reducida.
SHIN_PROTOCOLO = 'articulo'  # 'exploracion' o 'articulo'
SHIN_GUARDAR_CADA_ADAM = 250
SHIN_GUARDAR_CADA_LBFGS = 25
SHIN_REANUDAR = True

# ----------------------------------------------------------
# Red residual y funciones exactas de los ejemplos de Shin
# ----------------------------------------------------------
from torch.autograd import grad
import copy

class RedResidualShin(nn.Module):
    """Red residual de dos capas ocultas y ancho 50, según la sección 4.1."""
    def __init__(self):
        super().__init__()
        self.capa1 = nn.Linear(1, 50)
        self.capa2 = nn.Linear(50, 50)
        self.salida = nn.Linear(50, 1)
        for modulo in [self.capa1, self.capa2, self.salida]:
            nn.init.xavier_uniform_(modulo.weight)
            nn.init.zeros_(modulo.bias)

    def forward(self, x):
        z1 = torch.tanh(self.capa1(x))
        # 1*x replica la entrada escalar en las 50 neuronas.
        z2 = x.expand(-1, 50) + z1
        return self.salida(torch.tanh(self.capa2(z2)))

class RedShinDirichletFuerte(nn.Module):
    """Cumple h(-1)=h(1)=0 exactamente para todo theta."""
    def __init__(self):
        super().__init__()
        self.base = RedResidualShin()

    def forward(self, x):
        return (1.0 - x.square()) * self.base(x)


def exacta_shin(x, caso):
    if caso == 'tanh':
        return torch.tanh(x)
    if caso == 'oscilatorio':
        return (1.0-x.square())*torch.sin(6.0*torch.pi*x)
    raise ValueError(caso)


def derivada_exacta_shin(x, caso):
    if caso == 'tanh':
        return 1.0-torch.tanh(x).square()
    if caso == 'oscilatorio':
        k = 6.0*torch.pi
        return -2.0*x*torch.sin(k*x) + k*(1.0-x.square())*torch.cos(k*x)
    raise ValueError(caso)


def fuente_shin(x, caso):
    # Definimos L[h]=-h'' y por tanto f=-u*''.
    if caso == 'tanh':
        return 2*torch.tanh(x)/torch.cosh(x).square()
    k = 6.0*torch.pi
    return (2+k*k*(1-x.square()))*torch.sin(k*x) + 4*k*x*torch.cos(k*x)


def perdida_shin(modelo, x_interior, caso, metodo, n_total):
    """Devuelve J_TOTAL, J_PDE, J_BC y R_LIPR."""
    x = x_interior.detach().clone().requires_grad_(True)
    pred = modelo(x)
    ux = grad(pred, x, torch.ones_like(pred), create_graph=True)[0]
    uxx = grad(ux, x, torch.ones_like(ux), create_graph=True)[0]
    residuo = -uxx-fuente_shin(x,caso)
    jpde = residuo.square().mean()

    if caso == 'tanh':
        frontera = torch.tensor([[-1.0],[1.0]],device=DEVICE,dtype=DTYPE_REG)
        jbc = (modelo(frontera)-torch.tanh(frontera)).square().mean()
    else:
        # Dirichlet fuerte: el contorno está satisfecho exactamente.
        jbc = jpde.new_zeros(())

    regularizador = jpde.new_zeros(())
    if metodo == 'LIPR':
        uxxx = grad(uxx, x, torch.ones_like(uxx), create_graph=True)[0]
        cuadrados = uxxx.square().reshape(-1)
        indice = cuadrados.detach().argmax()
        regularizador = cuadrados[indice]
    elif metodo != 'PINN':
        raise ValueError(metodo)
    # El peso se calcula con el N_f TOTAL y no con el tamaño del minilote.
    lambda_r = int(n_total)**(-1.5)
    return jpde + jbc + lambda_r*regularizador, jpde, jbc, regularizador


def errores_shin_discretos(modelo, caso, puntos=2000, bloque=400):
    """Errores absolutos discretos L2 y H1; evaluación independiente por bloques."""
    eu, ed, em = [], [], []
    for inicio in range(0,puntos,bloque):
        fin = min(inicio+bloque,puntos)
        x = torch.linspace(-1,1,puntos,device=DEVICE,dtype=DTYPE_REG)[inicio:fin].reshape(-1,1)
        x = x.detach().requires_grad_(True)
        u = modelo(x)
        ux = grad(u,x,torch.ones_like(u),create_graph=False)[0]
        eu.extend((u-exacta_shin(x,caso)).detach().cpu().flatten().numpy())
        ed.extend((ux-derivada_exacta_shin(x,caso)).detach().cpu().flatten().numpy())
    eu,ed=np.asarray(eu),np.asarray(ed)
    return float(np.sqrt(np.mean(eu**2))), float(np.sqrt(np.mean(eu**2+ed**2))), float(np.max(np.abs(eu)))

# Verificación de la fuente: u*'' + f = 0 en ambos ejemplos.
for _caso in ('tanh','oscilatorio'):
    _x=torch.linspace(-0.98,0.98,19,device=DEVICE,dtype=DTYPE_REG).reshape(-1,1).requires_grad_(True)
    _u=exacta_shin(_x,_caso)
    _ux=grad(_u,_x,torch.ones_like(_u),create_graph=True)[0]
    _uxx=grad(_ux,_x,torch.ones_like(_ux),create_graph=False)[0]
    _desfase=float((_uxx+fuente_shin(_x,_caso)).abs().max().detach().cpu())
    assert _desfase<1e-8,(_caso,_desfase)
print('Funciones fuente y soluciones exactas: comprobadas.')

# ----------------------------------------------------------
# Protocolo computacional reproducible (Shin, figuras 3 y 4)
# ----------------------------------------------------------
if SHIN_PROTOCOLO == 'articulo':
    SHIN_CFG = {
        'tanh': {'n':[1,2,4,8,10,20,40,80,160,320,640,1280,2500,5000,10000],
                 'adam':25000,'lbfgs':250,'eval':10000,'batch':None},
        'oscilatorio': {'n':[50,100,200,500,1000,2000,3500,5000],
                       'adam':5000,'lbfgs':250,'eval':10000,'batch':100},
    }
else:
    SHIN_CFG = {
        'tanh': {'n':[1,4,10,40,160,640],
                 'adam':(25 if MODO=='demostracion' else 750),
                 'lbfgs':(0 if MODO=='demostracion' else 65),
                 'eval':(301 if MODO=='demostracion' else 2001),'batch':None},
        'oscilatorio': {'n':[50,100,250,500],
                       'adam':(25 if MODO=='demostracion' else 900),
                       'lbfgs':(0 if MODO=='demostracion' else 65),
                       'eval':(301 if MODO=='demostracion' else 2001),'batch':100},
    }
# Los valores concretos se guardan para poder repetir resultados.
(SALIDA/'protocolo_shin.json').write_text(
    json.dumps({'modo_shin':SHIN_PROTOCOLO,'opciones':SHIN_CFG,
                'xavier':'uniforme','adam_lr':1e-3,
                'lbfgs_lr':1.0,'lbfgs_tol':None,
                'semilla':SEMILLA,'dtype':'float64',
                'checkpoint_adam_cada':SHIN_GUARDAR_CADA_ADAM,
                'checkpoint_lbfgs_cada':SHIN_GUARDAR_CADA_LBFGS,
                'nota':'El artículo no publica todas las tolerancias/semillas ni cada tamaño de muestra.'},
               indent=2,ensure_ascii=False),encoding='utf8')

# Las ejecuciones largas pueden reanudarse si se guardan en Google Drive.
def rejilla_shin(n):
    if n==1:
        return torch.zeros((1,1),device=DEVICE,dtype=DTYPE_REG)
    return torch.linspace(-1,1,n,device=DEVICE,dtype=DTYPE_REG).reshape(-1,1)

def perdida_shin_por_bloques_y_gradiente(modelo, x_full, caso, metodo, bloque=256):
    """Computa el objetivo FULL-BATCH y acumula gradientes sin grafo gigante.

    Para LIPR busca el máximo en todos los puntos y calcula el gradiente
    únicamente en el punto que alcanza ese máximo. Es el subgradiente
    del máximo discreto cuando el punto maximizador es único.
    Debe llamarse DESPUÉS de optim.zero_grad().
    """
    n_total=len(x_full)
    pde_total=0.0
    indice_maximo=None
    valor_maximo=-1.0
    for ini in range(0,n_total,bloque):
        x=x_full[ini:ini+bloque].detach().clone().requires_grad_(True)
        u=modelo(x)
        ux=grad(u,x,torch.ones_like(u),create_graph=True)[0]
        uxx=grad(ux,x,torch.ones_like(ux),create_graph=True)[0]
        residuo=-uxx-fuente_shin(x,caso)
        loss=(residuo.square().sum()/n_total)
        pde_total+=float(loss.detach().cpu())
        loss.backward()
        if metodo=='LIPR':
            # Nueva evaluación para buscar el máximo sin conservar
            # los grafos de todos los bloques simultáneamente.
            z=x_full[ini:ini+bloque].detach().clone().requires_grad_(True)
            uz=modelo(z)
            du=grad(uz,z,torch.ones_like(uz),create_graph=True)[0]
            d2u=grad(du,z,torch.ones_like(du),create_graph=True)[0]
            d3u=grad(d2u,z,torch.ones_like(d2u),create_graph=False)[0]
            zvalores=d3u.detach().square().flatten()
            valor_local,ind_local=zvalores.max(dim=0)
            if float(valor_local)>valor_maximo:
                valor_maximo=float(valor_local)
                indice_maximo=ini+int(ind_local)

    total=pde_total
    if caso=='tanh':
        borde=torch.tensor([[-1.0],[1.0]],device=DEVICE,dtype=DTYPE_REG)
        condicion=(modelo(borde)-torch.tanh(borde)).square().mean()
        total+=float(condicion.detach().cpu())
        condicion.backward()

    if metodo=='LIPR':
        punto=x_full[indice_maximo:indice_maximo+1].detach().clone().requires_grad_(True)
        uv=modelo(punto)
        dv=grad(uv,punto,torch.ones_like(uv),create_graph=True)[0]
        d2v=grad(dv,punto,torch.ones_like(dv),create_graph=True)[0]
        d3v=grad(d2v,punto,torch.ones_like(d2v),create_graph=True)[0]
        regularizacion=n_total**(-1.5)*d3v.square().sum()
        total+=float(regularizacion.detach().cpu())
        regularizacion.backward()
    return torch.tensor(total,dtype=DTYPE_REG,device=DEVICE)


# ----------------------------------------------------------
# Guardado y recuperación de entrenamientos largos de Shin
# ----------------------------------------------------------
# Se guarda después de completar una época de Adam o un bloque de L-BFGS.
# Al reiniciar Colab, los archivos .pt se leen desde el mismo directorio
# persistente del que se recuperan los CSV ya finalizados.
import shutil

CARPETA_CHECKPOINTS_SHIN = SALIDA / 'checkpoints_shin'
CARPETA_CHECKPOINTS_SHIN.mkdir(parents=True, exist_ok=True)


def ruta_checkpoint_shin(caso, n, metodo, cfg):
    identificador = f'{SHIN_PROTOCOLO}_{caso}_{metodo}_N{n}_A{cfg["adam"]}'
    return CARPETA_CHECKPOINTS_SHIN / f'{identificador}.pt'


def contexto_checkpoint_shin(caso, n, metodo, cfg):
    # Impide restaurar por accidente otro experimento o protocolo.
    return {
        'caso': caso, 'N_f': int(n), 'metodo': metodo,
        'semilla': int(SEMILLA), 'protocolo': SHIN_PROTOCOLO,
        'cfg': dict(cfg), 'dtype': str(DTYPE_REG),
        'modelo': ('RedResidualShin' if caso == 'tanh'
                   else 'RedShinDirichletFuerte'),
        'lbfgs_bloque': int(SHIN_GUARDAR_CADA_LBFGS),
        'version_objetivo': 'Nf_total_LIPR_v1',
    }


def estados_aleatorios_shin():
    # Guardar también el muestreo aleatorio de minilotes del ejemplo oscilatorio.
    return {
        'python': random.getstate(),
        'numpy': np.random.get_state(),
        'torch_cpu': torch.get_rng_state(),
        'torch_cuda': torch.cuda.get_rng_state_all()
                      if torch.cuda.is_available() else None,
    }


def recuperar_aleatoriedad_shin(estados):
    random.setstate(estados['python'])
    np.random.set_state(estados['numpy'])
    torch.set_rng_state(estados['torch_cpu'].cpu())
    if estados.get('torch_cuda') is not None and torch.cuda.is_available():
        if len(estados['torch_cuda']) == torch.cuda.device_count():
            torch.cuda.set_rng_state_all(estados['torch_cuda'])
        else:
            print('Aviso: cantidad de GPU diferente; no se garantiza el mismo muestreo.')


def guardar_checkpoint_shin(ruta, contenido):
    """Guardado por archivo temporal y copia de respaldo, útil en Drive montado."""
    ruta.parent.mkdir(parents=True, exist_ok=True)
    temporal = ruta.with_suffix('.temporal.pt')
    respaldo = ruta.with_suffix('.anterior.pt')
    # No sobrescribir la última copia válida sin conservar una alternativa.
    torch.save(contenido, temporal)
    if ruta.exists():
        shutil.copy2(ruta, respaldo)
    os.replace(temporal, ruta)


def leer_checkpoint_shin(ruta, contexto):
    if not SHIN_REANUDAR:
        return None
    # El respaldo se utiliza si el guardado más reciente quedó incompleto.
    for candidato in [ruta, ruta.with_suffix('.anterior.pt')]:
        if not candidato.exists():
            continue
        try:
            # weights_only=False: incluye estados de NumPy/Python.
            # Abrir ÚNICAMENTE checkpoints generados por este notebook.
            estado = torch.load(candidato, map_location='cpu', weights_only=False)
        except Exception as exc:
            print('Checkpoint ilegible:', candidato.name, repr(exc))
            continue
        if estado.get('version') != 1 or estado.get('contexto') != contexto:
            print('Checkpoint incompatible, no se utilizará:', candidato.name)
            continue
        if candidato != ruta:
            print('Recuperado desde la copia de respaldo:', candidato.name)
        return estado
    return None


def eliminar_checkpoint_shin(caso, n, metodo, cfg):
    """Se ejecuta solo DESPUÉS de que el resultado final figure en el CSV."""
    ruta = ruta_checkpoint_shin(caso, n, metodo, cfg)
    for objetivo in [ruta, ruta.with_suffix('.anterior.pt'),
                     ruta.with_suffix('.temporal.pt')]:
        if objetivo.exists():
            objetivo.unlink()


def entrenar_shin(caso, n, metodo, cfg, estado):
    # 1. Preparar red y puntos según el protocolo original.
    modelo = (RedResidualShin() if caso == 'tanh'
              else RedShinDirichletFuerte()).to(DEVICE, dtype=DTYPE_REG)
    modelo.load_state_dict(estado)
    x_full = rejilla_shin(n)
    optim_adam = torch.optim.Adam(modelo.parameters(), lr=1e-3)
    ruta = ruta_checkpoint_shin(caso, n, metodo, cfg)
    contexto = contexto_checkpoint_shin(caso, n, metodo, cfg)

    # 2. Recuperar un entrenamiento incompleto, si existe.
    anterior = leer_checkpoint_shin(ruta, contexto)
    epoca_inicial = 0
    etapa = 'adam'
    historia = []
    segundos_anteriores = 0.0
    estado_lbfgs = None
    iteraciones_lbfgs = 0

    if anterior is not None:
        modelo.load_state_dict(anterior['modelo'])
        etapa = anterior['etapa']
        epoca_inicial = int(anterior['epocas_adam'])
        iteraciones_lbfgs = int(anterior['iteraciones_lbfgs'])
        historia = list(anterior['historia'])
        segundos_anteriores = float(anterior['segundos_acumulados'])
        estado_lbfgs = anterior.get('optim_lbfgs')
        if anterior.get('optim_adam') is not None:
            optim_adam.load_state_dict(anterior['optim_adam'])
        recuperar_aleatoriedad_shin(anterior['rng'])
        print(f'REANUDADO {caso} N={n} {metodo}: '
              f'Adam={epoca_inicial}/{cfg["adam"]}, '
              f'L-BFGS={iteraciones_lbfgs}/{cfg["lbfgs"]}, etapa={etapa}')

        # Si terminó el entrenamiento, pero Colab cayó antes de guardar el CSV:
        if etapa == 'completado':
            return modelo, anterior['fila_final'], historia

    inicio_tramo = time.perf_counter()

    def checkpoint(etapa_actual, epocas, lbfgs_realizadas, optim_lbfgs=None,
                   fila_final=None):
        # Guardar un estado consistente al FINAL de un paso de optimización.
        total_segundos = segundos_anteriores + (time.perf_counter() - inicio_tramo)
        paquete = {
            'version': 1, 'contexto': contexto,
            'etapa': etapa_actual,
            'epocas_adam': int(epocas),
            'iteraciones_lbfgs': int(lbfgs_realizadas),
            'modelo': modelo.state_dict(),
            'optim_adam': optim_adam.state_dict(),
            'optim_lbfgs': (optim_lbfgs.state_dict()
                            if optim_lbfgs is not None else estado_lbfgs),
            'historia': historia, 'segundos_acumulados': total_segundos,
            'rng': estados_aleatorios_shin(),
            'fila_final': fila_final,
        }
        guardar_checkpoint_shin(ruta, paquete)

    # 3. Entrenamiento Adam (reanuda desde la última época completada).
    if etapa == 'adam':
        for ep in range(epoca_inicial, cfg['adam']):
            # En el caso oscilatorio se usan minilotes de 100 puntos.
            if cfg['batch'] is not None and len(x_full) > cfg['batch']:
                indices = torch.randperm(len(x_full), device=DEVICE)[:cfg['batch']]
                x = x_full[indices]
            else:
                x = x_full

            optim_adam.zero_grad(set_to_none=True)
            if len(x) == len(x_full) and len(x_full) > 1024:
                loss = perdida_shin_por_bloques_y_gradiente(
                    modelo, x_full, caso, metodo)
            else:
                loss, lpde, lbc, reg = perdida_shin(modelo, x, caso, metodo, n_total=len(x_full))
                if not torch.isfinite(loss):
                    raise FloatingPointError((caso, metodo, n, ep))
                loss.backward()
            if not torch.isfinite(loss):
                raise FloatingPointError((caso, metodo, n, ep))
            optim_adam.step()

            epocas_hechas = ep + 1
            if (ep == 0 or epocas_hechas == cfg['adam'] or
                    epocas_hechas % max(1, cfg['adam']//100) == 0):
                historia.append({'epoca': epocas_hechas,
                                'perdida': float(loss.detach().cpu()),
                                'metodo': metodo, 'N_f': n, 'caso': caso})

            if (epocas_hechas % SHIN_GUARDAR_CADA_ADAM == 0 or
                    epocas_hechas == cfg['adam']):
                checkpoint('adam', epocas_hechas, 0)
                print(f'  Checkpoint Adam: {caso} N={n} {metodo} '
                      f'({epocas_hechas}/{cfg["adam"]})')

        epoca_inicial = cfg['adam']
        etapa = 'lbfgs'

    # 4. L-BFGS con estado de curvatura persistente. Los bloques permiten
    #    guardar un checkpoint ENTRE llamadas al optimizador.
    if cfg['lbfgs']:
        optim = torch.optim.LBFGS(
            modelo.parameters(), lr=1.0,
            max_iter=max(1, min(SHIN_GUARDAR_CADA_LBFGS, cfg['lbfgs'])),
            history_size=20, line_search_fn='strong_wolfe')
        if estado_lbfgs is not None:
            optim.load_state_dict(estado_lbfgs)

        def cierre():
            optim.zero_grad(set_to_none=True)
            if len(x_full) > 1024:
                return perdida_shin_por_bloques_y_gradiente(
                    modelo, x_full, caso, metodo)
            loss, _, _, _ = perdida_shin(modelo, x_full, caso, metodo, n_total=len(x_full))
            loss.backward()
            return loss

        while iteraciones_lbfgs < cfg['lbfgs']:
            pendientes = cfg['lbfgs'] - iteraciones_lbfgs
            optim.param_groups[0]['max_iter'] = min(
                SHIN_GUARDAR_CADA_LBFGS, pendientes)
            optim.step(cierre)
            # PyTorch conserva n_iter dentro del estado del primer parámetro.
            estado_interno = optim.state[optim._params[0]]
            nuevo_total = int(estado_interno.get('n_iter', 0))
            if nuevo_total <= iteraciones_lbfgs:
                print('L-BFGS sin nuevos pasos: detenido por tolerancia.')
                break
            iteraciones_lbfgs = nuevo_total
            checkpoint('lbfgs', cfg['adam'], iteraciones_lbfgs, optim)
            print(f'  Checkpoint L-BFGS: {caso} N={n} {metodo} '
                  f'({iteraciones_lbfgs}/{cfg["lbfgs"]})')

        # Si L-BFGS se detuvo por convergencia, conservar el estado final.
        checkpoint('lbfgs', cfg['adam'], iteraciones_lbfgs, optim)

    # 5. Evaluación independiente y checkpoint de finalización antes del CSV.
    segundos = segundos_anteriores + (time.perf_counter() - inicio_tramo)
    l2, h1, linf = errores_shin_discretos(modelo, caso, puntos=cfg['eval'])
    fila = {
        'caso': caso, 'metodo': metodo, 'N_f': n, 'semilla': SEMILLA,
        'error_L2_discreto': l2, 'error_H1_discreto': h1,
        'error_C0_evaluado': linf, 'segundos': segundos,
        'adam_epocas': cfg['adam'], 'lbfgs_max_iter': cfg['lbfgs'],
        'lbfgs_iteraciones_reales': iteraciones_lbfgs,
        'K_eval': cfg['eval'], 'protocolo_shin': SHIN_PROTOCOLO,
        'checkpoint_adam_cada': SHIN_GUARDAR_CADA_ADAM,
        'checkpoint_lbfgs_cada': SHIN_GUARDAR_CADA_LBFGS,
        'version_objetivo': 'Nf_total_LIPR_v1',
    }
    checkpoint('completado', cfg['adam'], iteraciones_lbfgs, fila_final=fila)
    return modelo, fila, historia

# Comprobación adicional: la frontera fuerte es exactamente nula.
_xb=torch.tensor([[-1.0],[1.0]],dtype=DTYPE_REG,device=DEVICE)
assert RedShinDirichletFuerte().to(DEVICE,dtype=DTYPE_REG)(_xb).abs().max().item()==0.0
print('Configuración y contorno fuerte: comprobados.')

# ----------------------------------------------------------
# Reproducción computacional: Figura 3 y Figura 4 de Shin
# ----------------------------------------------------------
# El emparejamiento de PINN y LIPR se hace con la misma inicialización.
from pathlib import Path

for caso in ['oscilatorio']:
    cfg=SHIN_CFG[caso]
    nombre_csv=f'resultados_shin_{caso}.csv'
    anterior=SALIDA/nombre_csv
    if anterior.exists():
        existentes=pd.read_csv(anterior).to_dict('records')
        # Evitar mezclar protocolos y tamaños tras modificar la configuración.
        existentes=[r for r in existentes if (r.get('protocolo_shin')==SHIN_PROTOCOLO
                    and int(r.get('adam_epocas',-1))==cfg['adam']
                    and int(r.get('K_eval',-1))==cfg['eval']
                    and r.get('version_objetivo')=='Nf_total_LIPR_v1')]
    else:
        existentes=[]
    realizados={(int(f['N_f']),f['metodo']) for f in existentes}
    resultados_shin=list(existentes)
    for n in cfg['n']:
        # La misma inicialización para los dos métodos en un N dado.
        fijar_semilla(SEMILLA+n+(0 if caso=='tanh' else 50000))
        nuevo=(RedResidualShin() if caso=='tanh' else RedShinDirichletFuerte()).to(DEVICE,dtype=DTYPE_REG)
        base=copy.deepcopy(nuevo.state_dict())
        for metodo in ['PINN','LIPR']:
            if (n,metodo) in realizados:
                print('Se conserva el caso ya ejecutado:',caso,n,metodo)
                continue
            fijar_semilla(SEMILLA+n+(0 if caso=='tanh' else 50000))
            _,fila,historia=entrenar_shin(caso,n,metodo,cfg,base)
            resultados_shin.append(fila)
            # Registrar primero el historial: el CSV global se escribe al final.
            guardar_csv(f'historial_shin_{caso}_{metodo}_N{n}.csv',historia)
            guardar_csv(nombre_csv,resultados_shin)
            # Solo retirar el checkpoint tras conservar ambos CSV.
            eliminar_checkpoint_shin(caso,n,metodo,cfg)
            print(f'{caso:11s} N={n:5d} {metodo:5s}: '
                  f'L2={fila["error_L2_discreto"]:.3e}, '
                  f'H1={fila["error_H1_discreto"]:.3e}, '
                  f'{fila["segundos"]:.1f}s')
    print('Total',caso,len(resultados_shin),'filas.')

# ----------------------------------------------------------
# Figuras comparables con la Figura 3 y la Figura 4 de Shin
# ----------------------------------------------------------
# Ambas usan errores discretos no normalizados y ejes log-log.
for caso,nombre in [('oscilatorio','reproduccion_shin_figura4.png')]:
    tabla=pd.read_csv(SALIDA/f'resultados_shin_{caso}.csv')
    plt.figure(figsize=(9.2,6))
    for metodo,color,estilo in [('PINN','tab:blue','-.'),('LIPR','tab:red','-')]:
        filas=tabla[tabla.metodo==metodo].sort_values('N_f')
        plt.loglog(filas.N_f,filas.error_L2_discreto,estilo+'x',color=color,
                   label=r'$L^2$ '+metodo,linewidth=1.8,markersize=7)
        plt.loglog(filas.N_f,filas.error_H1_discreto,estilo+'o',color=color,
                   label=r'$H^1$ '+metodo,linewidth=1.8,markersize=5)
    # Guía visual de pendiente -1: su altura SÍ se fija usando la mediana de los errores.
    eje=np.array([min(SHIN_CFG[caso]['n']),max(SHIN_CFG[caso]['n'])],dtype=float)
    positivos=tabla[['error_L2_discreto','error_H1_discreto']].to_numpy().ravel()
    positivos=positivos[np.isfinite(positivos)&(positivos>0)]
    constante=(float(np.median(positivos))*np.sqrt(eje.prod())) if len(positivos) else 1.0
    plt.loglog(eje,constante/eje,':',color='black',label=r'Guía visual $N_f^{-1}$ (escala por mediana)')
    plt.xlabel(r'Número de puntos residuales $N_f$')
    plt.ylabel(r'Error RMS discreto no relativo')
    cond=r'Dirichlet débil; $u^*=\tanh(x)$' if caso=='tanh' else r'Dirichlet fuerte; $u^*=(1-x^2)\sin(6\pi x)$'
    plt.title('Poisson 1D: '+cond)
    plt.grid(True,which='both',alpha=.3)
    plt.legend(ncol=2,fontsize=9)
    plt.suptitle(f'Protocolo de Shin: {SHIN_PROTOCOLO}',y=1.03,fontsize=10)
    guardar_figura(nombre)
print('Figuras de Shin creadas en:',SALIDA)
