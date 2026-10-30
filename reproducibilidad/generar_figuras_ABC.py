"""Regenera cuatro figuras desde los CSV individuales originales del Colab.
No certifica tasas asintoticas.
Ejecutar desde la carpeta Tesis_PUCP: python reproducibilidad/generar_figuras_ABC.py
"""
from pathlib import Path
import pandas as pd
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path(__file__).resolve().parents[1]
orig=pd.read_csv(root/'resultados'/'tanh_ABC_ejecuciones_originales_20261030.csv')
data=orig.groupby(['protocolo','ancho','N','m_r'],as_index=False).agg(
    mediana_eps=('eps_final','median'),
    mediana_ratio=('razon_eps_a','median'),
    mediana_eps_test=('eps_test','median'),
    mediana_holder=('holder_residuo','median'),
    mediana_holder_denso=('holder_residuo_denso','median'),
    mediana_H1_integral=('H1_integral_aprox','median'),
)

out=root/'imagenes'
plt.rcParams.update({'font.size':10,'savefig.dpi':180,'axes.grid':True,'grid.alpha':.23})

def save(fig,name):
    fig.tight_layout();fig.savefig(out/name);plt.close(fig)

b=data[data.protocolo=='B'].sort_values('ancho')
c=data[data.protocolo=='C'].sort_values('m_r').copy()
c['a_m']=c.m_r.map({1521:0.00123219,5476:0.00047144,11881:0.000263715})

fig,ax=plt.subplots(figsize=(6.6,3.6))
ax.plot(b.ancho,b.mediana_eps_test,'o-',label='MSE residual de prueba')
ax.plot(b.ancho,b.mediana_H1_integral,'s-',label=r'Error $H^1$ integral estimado')
ax.set(xlabel='Anchura W (N=40 fijo)',ylabel='Magnitud estimada (escalas distintas)',title='Protocolo B: muestreo fijo')
ax.legend(fontsize=9);save(fig,'abc_B_anchuras.png')

# Graficas independientes: MSE (cuadratica) y H1 (norma integral estimada)
# No compartir eje para magnitudes heterogeneas.
fig,ax=plt.subplots(figsize=(6.6,3.6))
ax.plot(b.ancho,b.mediana_eps_test,'o-')
ax.set(xlabel='Anchura W (N=40 fijo)',ylabel='MSE residual de prueba',title='Protocolo B: residuo de prueba')
save(fig,'abc_B_mse_test.png')

fig,ax=plt.subplots(figsize=(6.6,3.6))
ax.plot(b.ancho,b.mediana_H1_integral,'s-')
ax.set(xlabel='Anchura W (N=40 fijo)',ylabel=r'Error H$^1$ integral estimado',title='Protocolo B: error de solucion')
save(fig,'abc_B_H1_integral.png')

fig,ax=plt.subplots(figsize=(6.6,3.6))
ax.loglog(c.m_r,c.mediana_eps,'o-',label='MSE residual empírico')
ax.loglog(c.m_r,c.mediana_eps_test,'s--',label='MSE residual de prueba')
ax.loglog(c.m_r,c.a_m,'^:',label=r'$a_m^{\rm int}$ (referencia)')
ax.set(xlabel=r'Número de puntos interiores $m_r$',ylabel='Pérdida o peso',title='Protocolo C: escala del residuo')
ax.legend(fontsize=9);save(fig,'abc_C_escala.png')

fig,ax=plt.subplots(figsize=(6.6,3.6))
ax.plot(c.m_r,c.mediana_ratio,'o-')
ax.set(xlabel=r'Número de puntos interiores $m_r$',ylabel='Cociente (adimensional)',title='Protocolo C: diagnóstico de comparadores')
save(fig,'abc_C_cociente.png')

fig,ax=plt.subplots(figsize=(6.6,3.6))
ax.plot(c.m_r,c.mediana_holder,'o-',label='1200 pares (aprox.)')
ax.plot(c.m_r,c.mediana_holder_denso,'s-',label='4800 pares (aprox.)')
ax.set(xlabel=r'Número de puntos interiores $m_r$',ylabel='Seminorma Hölder discreta',title='Protocolo C: sensibilidad al número de pares')
ax.legend(fontsize=9);save(fig,'abc_C_holder_pares.png')
