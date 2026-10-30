# Procedencia y limitaciones del estudio A–C

La fuente de los CSV y métricas fue la ejecución de Google Colab del 30 de octubre de 2026, con semillas 7 y 17, redes `tanh`, Poisson 2D y Dirichlet fuerte. Se conservan sus archivos en `resultados/` y la configuración en `reproducibilidad/entorno_y_protocolo_original.json`.

**Datos depositados**

- `resultados/tanh_ABC_ejecuciones_originales_20261030.csv`: 16 filas (A: 4; B: 6; C: 6, incluyendo las dos reutilizaciones de B W64 N40).
- `resultados/tanh_ABC_resumen_original_Colab_20261030.csv`: agregados originales (medianas y rangos).
- `resultados/tanh_ABC_resumen_reportado_20261030.csv`: tabla redondeada usada en la presentación.
- `reproducibilidad/checkpoints_origen_A/*.pt`: cuatro estados iniciales de A. Sus huellas SHA-256 se comparan con `sha256_fuente` en el CSV individual.
- `reproducibilidad/verificar_resultados_ABC.py`: compara todas las filas con los agregados y comprueba los cuatro checkpoints.
- `imagenes/abc_*.png`: figuras generadas de los datos anteriores con `generar_figuras_ABC.py`.

**No depositado en su totalidad:** los historiales completos por etapa y los checkpoints *finales* individuales de todos los ensayos A, B y C. Los revisores pueden volver a ejecutar los entrenamientos mediante el Colab; para la repetición numérica exacta se requieren el entorno y los checkpoints correspondientes. No se presentan los CSV agregados como sustitutos de esos archivos.

**Comparación teoría/experimento:** los entrenamientos optimizan MSE de residuo, no la pérdida regularizada Hölder del teorema. Las seminormas Hölder son estimadas sobre 1200/4800 pares finitos, sin certificado continuo. El error H¹ es una estimación por cuadratura. La pendiente -0.283774 de C se obtiene con tres medianas y no constituye tasa asintótica.

**Presupuesto de optimización:** 900 pasos Adam con lote 128 y cuatro etapas L-BFGS con hasta 512 puntos por etapa; a tamaños mayores L-BFGS cubre una fracción menor de los puntos. La muestra de prueba se reserva para la evaluación final. B W64 N40 se reutiliza en C, sin nueva réplica.

El repositorio se limita al componente **computacional**. El texto íntegro de la tesis no está publicado aquí.
