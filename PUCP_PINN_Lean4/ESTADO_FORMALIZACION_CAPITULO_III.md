# Estado verificable de la formalización del capítulo III

## Etapa 18

La referencia matemática de esta etapa es el capítulo III del PDF del ZIP `Tesis_PUCP_Resumen_Conectores_20261108.zip`. La [matriz del capítulo](INVENTARIO_FORMAL_CAPITULO_III.md) registra el hash, las 27 entradas numeradas, las 94 ecuaciones, los desarrollos sin número y sus dependencias. La [auditoría de la base](AUDITORIA_MATEMATICA_PR18.md) distingue los alcances de las pruebas heredadas. Los conteos describen el material inventariado.

| Nivel | Resultados y evidencia |
|---|---|
| Verificados en el alcance de la declaración | Comparación variacional exacta y aproximada, Voronoi medible, ocupación de celdas y piezas de energía, regularidad y pérdida. `ComparadoresAproximados` establece (3.38)–(3.41) para la instancia escalar 2D. |
| Verificados bajo hipótesis o en instancias | `proposicion310_dim2` usa (3.42) para demostrar la regularidad eventual, (3.43), y la convergencia y las tasas uniformes para minimizadores aproximados. `teorema38_dim2` da (3.26)–(3.28) para mínimos exactos. Los puentes de 3.20 dan las tasas en el cuadrado con candidatos suaves `ψq` o `G+ψq`. |
| Parcialmente formalizados | Queda la versión en dimensión general de P3.10 y su instanciación en clases neuronales concretas. La matriz registra las piezas disponibles de L3.3–T3.8, P3.11–P3.15, T3.18–T3.20 y L3.24–P3.27. |
| Pendientes de infraestructura o instanciación | Existencia clásica y estabilidad general, trazas Sobolev y dimensiones generales, geometría de las leyes uniformes del cuadrado, escala logarítmica, Poincaré óptima y base seno, clases MLP concretas, construcción de Hermite/Taylor y selección de mínimos. |

## Reproducción

- Base fijada en `4ce560996873ebe701af34abeb30e04d590acaa6`, cabeza de la [PR #19](https://github.com/MichaelMobius/tesispucp/pull/19).
- Lean `4.35.0`, Mathlib `v4.35.0` y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
- Ejecutar `lake build` en `PUCP_PINN_Lean4/`. El nuevo módulo contiene sus tres comprobaciones `#check` y sus correspondientes `#print axioms`.
- La auditoría de hipótesis, mensurabilidad y alcance consta en el [informe de la etapa 18](INFORME_ETAPA18.md).

## Siguientes obligaciones

1. Especializar la cota de ocupación al parámetro logarítmico del Lema 3.13.
2. Separar el funcional interior y verificar la geometría uniforme del cuadrado para la Proposición 3.11.
3. Separar los dos primeros puentes de aproximación. Para Taylor, demostrar extensión entera, estimación de coeficientes y cola diferenciada. Para Hermite, probar existencia y unicidad en los nodos distintos, resto uniforme e identificación boreliana de los coeficientes.
