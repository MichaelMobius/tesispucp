# Estado verificable de la formalización del capítulo III

## Etapa 17

La referencia matemática de esta etapa es el capítulo III del PDF del ZIP `Tesis_PUCP_Resumen_Conectores_20261108.zip`. La [matriz del capítulo](INVENTARIO_FORMAL_CAPITULO_III.md) registra el hash, las 27 entradas numeradas, las 94 ecuaciones, los desarrollos sin número y sus dependencias. La [auditoría de la base](AUDITORIA_MATEMATICA_PR18.md) distingue los alcances de las pruebas heredadas. Los conteos describen el material inventariado.

| Nivel | Resultados y evidencia |
|---|---|
| Verificados en el alcance de la declaración | Comparación variacional exacta y aproximada, Voronoi medible, ocupación de celdas y piezas de energía, regularidad y pérdida. Las ecuaciones (3.38)–(3.40) de P3.10 se formalizan mediante `ProblemaPINN.minimizadorAproximado_iff_le_infimo` y `ProblemaPINN.cotas_minimizador_aproximado`. |
| Verificados bajo hipótesis o en instancias | `teorema38_dim2` da (3.26)–(3.28) para residuos escalares y exponentes de masa 2 y 1. Los puentes de 3.20 dan las tasas en el cuadrado con candidatos suaves `ψq` o `G+ψq`. Las hipótesis de muestreo, selección y la ecuación de la solución exacta se especifican en cada declaración. |
| Parcialmente formalizados | P3.10 tiene además (3.41) bajo cobertura con exponentes de masa 2 y 1, mediante `perdidaPoblacional_aproximada_bajo_cobertura`. Quedan la tasa a.s. de (3.43) con candidatos subóptimos, la versión de dimensión general y la conclusión uniforme. La matriz registra también las piezas disponibles de L3.3–T3.8, P3.11–P3.15, T3.18–T3.20 y L3.24–P3.27. |
| Pendientes de infraestructura o instanciación | Existencia clásica y estabilidad general, trazas Sobolev y dimensiones generales, geometría de las leyes uniformes del cuadrado, escala logarítmica, Poincaré óptima y base seno, clases MLP concretas, construcción de Hermite/Taylor y selección de mínimos. |

## Reproducción

- Base fijada en `cf182d9edde2a21d385193958ee7a880b996e865`, cabeza de la [PR #18](https://github.com/MichaelMobius/tesispucp/pull/18).
- Lean `4.35.0`, Mathlib `v4.35.0` y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
- Ejecutar `lake build` en `PUCP_PINN_Lean4/`. El nuevo módulo contiene sus tres comprobaciones `#check` y sus correspondientes `#print axioms`.
- La revisión y la ejecución de CI de esta etapa se registran en la [PR de la etapa 17](https://github.com/MichaelMobius/tesispucp/pull/19).

## Siguientes obligaciones

1. Reusar (3.41) para obtener (3.43) sobre un evento conull, y generalizar la transferencia de regularidad a partir de una cota explícita, de modo que pueda tratar tanto mínimos exactos como subóptimos.
2. Empaquetar el lema de ocupación con parámetro y cerrar la escala logarítmica. Verificar la geometría uniforme del cuadrado antes de instanciar las constantes.
3. Separar los dos primeros puentes de aproximación. Para Taylor, demostrar extensión entera, estimación de coeficientes y cola diferenciada. Para Hermite, probar existencia y unicidad en los nodos distintos, resto uniforme e identificación boreliana de los coeficientes.
