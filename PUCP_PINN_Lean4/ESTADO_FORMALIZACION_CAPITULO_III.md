# Estado verificable de la formalización del capítulo III

## Etapa 20

La referencia matemática de esta etapa es el capítulo III del PDF del ZIP `Tesis_PUCP_Resumen_Conectores_20261108.zip`. La [matriz del capítulo](INVENTARIO_FORMAL_CAPITULO_III.md) registra el hash, las 27 entradas numeradas, las 94 ecuaciones, los desarrollos sin número y sus dependencias. La [auditoría de la base](AUDITORIA_MATEMATICA_PR18.md) distingue los alcances de las pruebas heredadas. Los conteos describen el material inventariado.

| Nivel | Resultados y evidencia |
|---|---|
| Verificados en el alcance de la declaración | `lema313_cobertura_logaritmica` demuestra (3.57)–(3.58) y la cobertura eventual casi segura para prefijos con $m(n)\ge n$ eventualmente. `ComparadoresAproximados` establece (3.38)–(3.41) para la instancia escalar 2D. |
| Verificados bajo hipótesis o en instancias | `proposicion314_dim2` establece (3.59)–(3.63) en 2D escalar. `proposicion310_dim2` usa (3.42) para demostrar (3.43) y las tasas uniformes para mínimos aproximados. `teorema38_dim2` da (3.26)–(3.28) para mínimos exactos. Los puentes de 3.20 dan tasas en el cuadrado con candidatos suaves `ψq` o `G+ψq`. |
| Parcialmente formalizados | Quedan las versiones en dimensión general de P3.10 y P3.14 y las instancias en clases neuronales concretas. La matriz registra las piezas disponibles de L3.3–T3.8, P3.11, P3.15, T3.18–T3.20 y L3.24–P3.27. |
| Pendientes de infraestructura o instanciación | Existencia clásica y estabilidad general, trazas Sobolev y dimensiones generales, geometría de las leyes uniformes del cuadrado, pesos y pérdidas interiores de P3.15, Poincaré óptima y base seno, clases MLP concretas, construcción de Hermite/Taylor y selección de mínimos. |

## Reproducción

- Base fijada en `24bdd251953f0c526a7e84aaef9dc7a28ad3e1bb`, cabeza de la [PR #21](https://github.com/MichaelMobius/tesispucp/pull/21).
- Lean `4.35.0`, Mathlib `v4.35.0` y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
- Ejecutar `lake build` en `PUCP_PINN_Lean4/`. El módulo `Proposicion314` contiene las comprobaciones `#check` y `#print axioms`.
- La auditoría de hipótesis, mensurabilidad y alcance consta en el [informe de la etapa 20](INFORME_ETAPA20.md).

## Siguientes obligaciones

1. Separar el funcional interior, verificar la geometría uniforme del cuadrado y certificar el umbral de la Proposición 3.15.
2. Parametrizar ambos exponentes en la cota integral poblacional para generalizar la Proposición 3.14.
3. Separar los dos primeros puentes de aproximación. Para Taylor, demostrar extensión entera, estimación de coeficientes y cola diferenciada. Para Hermite, probar existencia y unicidad en los nodos distintos, resto uniforme e identificación boreliana de los coeficientes.
