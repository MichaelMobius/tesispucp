# PINN / Poisson — material computacional reproducible

Repositorio de **código, datos, notebooks y resultados computacionales** relacionados con los experimentos de PINN para problemas de Poisson 1D/2D.

**El manuscrito de la tesis no forma parte de este repositorio.** Los teoremas, interpretaciones y conclusiones deben consultarse en el texto académico correspondiente. Los resultados aquí presentados son numéricos, no pruebas de convergencia asintótica.

## Contenido

- `Tesis_PUCP_PINN_Poisson_Experimentos.ipynb`: cuaderno histórico conservado de la rama principal.
- `codigos/`: scripts de regresión, clasificación, problemas 1D/2D, regularización, aproximación numérica y métricas.
- `reproducibilidad/Tesis_PUCP_PINN_Tanh_Colab_Definitivo_Jurado.ipynb`: protocolo A+B+C usado para evaluar redes `tanh` en Poisson 2D con Dirichlet fuerte.
- `reproducibilidad/checkpoints_origen_A/`: cuatro checkpoints de partida del protocolo A.
- `reproducibilidad/entorno_y_protocolo_original.json`: versiones, parámetros y semillas registrados en Colab.
- `resultados/`: CSV originales por corrida, resúmenes y experimentos 2D.
- `imagenes/abc_*.png`: figuras de B y C generadas a partir de datos.
- `reproducibilidad/PROCEDENCIA_DATOS_ABC.md`: explicación de la procedencia, repetición de ensayos y limitaciones.

## Comprobación de los resultados A+B+C

Entorno recomendado: Google Colab con PyTorch, NumPy, pandas y Matplotlib. Para verificar los CSV y reconstruir las figuras localmente:

```bash
python -m pip install numpy pandas matplotlib
python reproducibilidad/verificar_resultados_ABC.py
python reproducibilidad/generar_figuras_ABC.py
```

Para entrenar y evaluar redes, ejecutar el notebook en un entorno Colab con GPU; en el experimento original se utilizó una NVIDIA A100 y doble precisión.

## Tres protocolos y sus límites

- **A:** continuación de L-BFGS a partir de cuatro checkpoints refinados; contiene dos anchuras y dos semillas.
- **B:** anchuras 32, 64 y 128, con (N=40) fijo y dos semillas por anchura.
- **C:** escalamiento conjunto de anchura y número de puntos; reutiliza los ensayos `B W64 N40` sin contarlos como independientes. Los tres tamaños tienen solo dos semillas cada uno.

Se optimizó **MSE del residuo**; esto **no equivale** a minimizar la función objetivo regularizada con seminorma Hölder analizada en la parte teórica. Las estimaciones Hölder proceden de muestras finitas de pares y el error `H1_integral_aprox` procede de cuadratura: ninguno es una cota matemática continua certificada. La pendiente exploratoria del protocolo C no es una ley asintótica demostrada.

En el entrenamiento L-BFGS de B/C se utilizó un subconjunto de hasta 512 puntos por etapa, incluso cuando aumentó el número total de puntos. Debe considerarse al interpretar el escalamiento.

## Reproducibilidad e integridad

```bash
python reproducibilidad/verificar_resultados_ABC.py
python reproducibilidad/verificar_deposito.py --crear
python reproducibilidad/verificar_deposito.py
```

El segundo comando **genera localmente** un inventario SHA-256 de los archivos presentes; no es un certificado independiente de los resultados de entrenamiento. Los historiales por etapa y checkpoints finales completos de todas las corridas pueden no estar en este repositorio. No se deben afirmar reproducidas las ejecuciones solo porque se hayan validado sus tablas.

Código histórico conservado con sus nombres originales para facilitar la trazabilidad. No se publica ningún archivo `.tex`, `.bib` ni PDF del manuscrito.
