# Tesis PUCP — PINNs para Poisson 2D

Repositorio de trabajo para *Análisis de Convergencia de Soluciones de EDPs con Redes Neuronales PINN: Poisson 2D*.

## Estado de la rama de revisión (30 de octubre de 2026)

Esta rama contiene los **fuentes matemáticos revisados**, los scripts Python referidos en el apéndice, datos individuales y agregados de los experimentos A–C, la libreta de Colab para el jurado y cuatro checkpoints de **inicio** del experimento A. El cuaderno histórico de la raíz de `main` se ha conservado sin cambios.

**Alcance de este envío:** no es todavía el depósito autónomo íntegro de las 212 páginas. Esta rama incluye las figuras principales del protocolo A–C y el logotipo, pero **faltan otras figuras históricas y modelos finales de entrenamiento**. El archivo PDF final y el manifiesto SHA-256 del ZIP completo no se han publicado aquí. Por tanto, no debe afirmarse que un `pdflatex main.tex` limpio compila sin esos recursos adicionales.

## Contenido principal

- `main.tex`, `resumen.tex`, `introduccion.tex`, `capitulo1_13_07_26_shin.tex`, `capitulo2_13_07_26_shin.tex`, `capitulo3_13_07_26_shin.tex`, `Capitulo_IV_Resultados_2026.tex`, `capitulo_conclusiones.tex`, `apendice.tex`: fuentes revisados.
- `bib/biblio.bib`: referencias.
- `codigos/A01_*.py` a `A15_*.py`: experimentos y diagnósticos, incluida la variante histórica del caso oscilatorio.
- `reproducibilidad/Tesis_PUCP_PINN_Tanh_Colab_Definitivo_Jurado.ipynb`: protocolos A (continuación), B (anchura fija) y C (escalamiento exploratorio).
- `resultados/tanh_ABC_ejecuciones_originales_20261030.csv`: observaciones individuales (A: 4, B: 6, C: 6, incluidas dos filas reutilizadas de B).
- `resultados/tanh_ABC_resumen_original_Colab_20261030.csv`: resumen original de las ejecuciones.
- `reproducibilidad/checkpoints_origen_A/`: cuatro archivos de estado empleados para iniciar A, **no** los modelos finales de A/B/C.
- `reproducibilidad/verificar_resultados_ABC.py` y `reproducibilidad/generar_figuras_ABC.py`: comprobaciones y generación de figuras A–C.

## Reproducción de los resultados presentes

En la raíz de esta rama:

```bash
python reproducibilidad/verificar_resultados_ABC.py
python reproducibilidad/generar_figuras_ABC.py
```

El Colab requiere un entorno con PyTorch; las ejecuciones originales utilizaron GPU NVIDIA A100 y `torch.float64`. Se registraron únicamente dos semillas y tres escalas muestrales en C: **no constituye certificación de una ley asintótica**.

Los resultados analizan la reducción del residuo y estimaciones discretas de regularidad, **no** prueban la minimización global de la pérdida regularizada, ni las condiciones Hölder continuas o la tasa `O(a_m)` para toda sucesión de redes.

## Compilación de la tesis completa

El proyecto integral, disponible como paquete ZIP de la revisión post-auditoría, incluye además `imagenes/` completo y material histórico. Una vez reunidas esas figuras en sus rutas, la secuencia es:

```bash
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

Consulte `INFORME_CORRECCIONES_POST_AUDITORIA_20261030.md` para limitaciones y cambios de la revisión.

## Relación con Shin

La tesis reconstruye resultados de Shin, Darbon y Karniadakis bajo hipótesis explícitas. La variante para pesos iguales y comparadores aproximados es **condicional**; las experiencias numéricas no verifican sus requisitos asintóticos.
