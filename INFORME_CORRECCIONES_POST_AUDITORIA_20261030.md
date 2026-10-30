# Correcciones tras auditoría adversarial hostil

Documento: *Análisis de Convergencia de Soluciones de EDPs con Redes Neuronales PINN: Poisson 2D*.
Fecha de intervención: 30-10-2026.

## Reparaciones aplicadas y comprobadas

1. **Proveniencia A–C:** se recuperó desde Drive el CSV original de 16 filas de ejecuciones A (4), B (6), C (6, incluyendo la reutilización de B W64), más el CSV original de resumen y la configuración del entorno. Un verificador automatizado compara las medianas, mínimos y máximos con las tablas redondeadas de la tesis: **sin discrepancias**.
2. **Checkpoints de origen A:** se incorporaron los cuatro `tanh_refinado_W*.pt`; sus valores SHA-256 coinciden exactamente con los identificadores `sha256_fuente` registrados en el CSV original. Esto permite iniciar A desde los estados guardados, sin necesidad de acceder a Drive para recuperar estos cuatro archivos.
3. **Integridad del paquete:** el manifiesto histórico, incompatible con esta versión, se conserva bajo el prefijo `HISTORICO_`. Se generó un nuevo `MANIFIESTO_DEPOSITO_SHA256.csv` sobre la versión entregada, con script de creación y verificación.
4. **Teoría vs experimento:** la nueva tabla de IV.5 distingue explícitamente la pérdida MSE entrenada de la pérdida regularizada con seminorma Hölder del Teorema 2, y aclara que no se ha medido la brecha de optimalidad global ni una seminorma continua uniforme.
5. **Protocolo C:** se documentó que utiliza 900 pasos Adam de lotes 128 y L-BFGS sobre 512 puntos para 1 521, 5 476 y 11 881 puntos totales; las fracciones respectivas son 33.7%, 9.3%, 4.3%. La pendiente -0.284 se presenta como descriptiva y no como tasa intrínseca/asintótica de la arquitectura.
6. **Notación y atribución:** se conservó el operador elíptico matemáticamente correcto, pero se retiró la posible errata de índices de Shin del inventario de contribuciones propias.
7. **Consistencia editorial:** se actualizó el Resumen y Abstract con comparadores aproximados y el estudio A–C; se corrigió el sesgo en el dibujo neuronal y se homogeneizó el signo del residuo de Poisson en el Capítulo II.
8. **Teorema 4:** se reparó el pasaje que decía que la cota inferior de densidad era una hipótesis adicional, pues está ya incluida en la Hipótesis 1 de esta tesis.
9. **Gráficas:** su generador ahora toma las medianas del CSV individual recuperado del Colab, no una transcripción de la consola.

## Comprobaciones efectuadas

- `python reproducibilidad/verificar_resultados_ABC.py`: **16 ejecuciones, 8 filas agregadas y 4 SHA de origen A comprobados**.
- `python reproducibilidad/verificar_deposito.py`: debe dar **0 discrepancias** para el directorio publicado.
- LaTeX/BibTeX: PDF compilado con bibliografía y referencias resueltas; 212 páginas; revisión visual de la tabla teórica/numerical y figuras IV.5.

## Limitaciones que permanecen (no ocultadas)

- Los **modelos finales y los historiales por etapa** de A/B/C están disponibles en la carpeta original de Google Drive del autor, pero no todos forman parte de este ZIP. Para una auditoría autónoma integral debe exportarse también ese directorio y añadir un inventario nuevo; sus metadatos no se suplirán con cifras reconstruidas.
- El experimento C mantiene una cobertura variable por actualización y no identifica una tasa asintótica. Repetirlo con presupuestos escalados o con convergencia a meseta requeriría nuevos entrenamientos, que no se realizaron en esta intervención.
- Ningún experimento certifica las hipótesis sobre cota Hölder continua, comparadores `O(a_m)` para toda la sucesión, ni la brecha de minimización global `delta_m`.
- La extensión teórica se mantiene condicional y el resultado para pesos iguales no cubre todos los pesos de Shin.
- No se realizó auditoría formal en Lean ni comprobación experimental completa con GPU de los 16 entrenamientos originales.
- Los archivos antiguos en `HISTORICO_...` son evidencia histórica, no certificaciones válidas del depósito final.

## Reproducción y trazabilidad

```
cd Tesis_PUCP
python reproducibilidad/verificar_resultados_ABC.py
python reproducibilidad/generar_figuras_ABC.py
python reproducibilidad/verificar_deposito.py
```

El último comando puede señalar diferencias si se regeneran las figuras o se modifica el archivo LaTeX, en cuyo caso es indispensable crear un nuevo manifiesto con `--crear` **solo al preparar una nueva versión depositada**.

Carpeta original en Drive (acceso sujeto a permisos del titular):
https://drive.google.com/drive/folders/17ubryZ1OBZTECVeDTqpfhB6t_lyBrG5U