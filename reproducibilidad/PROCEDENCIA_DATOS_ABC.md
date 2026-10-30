# Procedencia verificada del estudio A--C (30-10-2026)

Fuente original recuperada mediante la conexión de Google Drive del autor:
`MyDrive/Tesis_PUCP/Colab_Jurado_Convergencia_Tanh`, carpeta de Drive
https://drive.google.com/drive/folders/17ubryZ1OBZTECVeDTqpfhB6t_lyBrG5U

En este depósito:

* `resultados/tanh_ABC_ejecuciones_originales_20261030.csv`: 16 registros originales
  (A: 4; B: 6; C: 6, contando reutilización explícita de B W64); NO son
  registros sintéticos.
* `resultados/tanh_ABC_resumen_original_Colab_20261030.csv`: medianas/rangos originales.
* `resultados/tanh_ABC_resumen_reportado_20261030.csv`: tabla histórica redondeada.
* `reproducibilidad/entorno_y_protocolo_original.json`: configuración exportada.
* `reproducibilidad/checkpoints_origen_A/*.pt`: cuatro modelos refinados desde los
  que empieza A. Las huellas SHA-256 coinciden con el campo `sha256_fuente`
  del CSV individual.
* `reproducibilidad/verificar_resultados_ABC.py`: comprobador automático
  que regenera agregados y contrasta los valores de las tablas.

Los historiales por etapa y los modelos *finales* de A/B/C están en las carpetas
privadas `A`, `B`, `C` de Google Drive; no se afirman incluidos todos en este ZIP.
Los revisores sin acceso a Drive necesitarán una exportación completa adicional
o ejecutar desde el cuaderno. La reproducción de A a partir de sus cuatro
checkpoints iniciales es posible con este depósito si se dispone de Colab/GPU.

El protocolo A continúa redes optimizadas previamente, y B inicia modelos nuevos
con el mismo `N=40` por semilla. C cambia W y m_r y reutiliza B W64 N40, por
lo que no se cuenta como réplica independiente. Los entrenamientos minimizan la
MSE de residuo, NO el objetivo regularizado del Teorema 2. Las evaluaciones
Hölder (1200/4800 pares) son estimadores discretos, y el cálculo de H1 es una
cuadratura numérica, no una norma certificada.

La pendiente -0.283774 es descriptiva y se obtiene de tres medianas C con
900 pasos Adam de lote 128 y cuatro etapas L-BFGS de hasta 512 puntos; no
identifica una ley asintótica intrínseca.
