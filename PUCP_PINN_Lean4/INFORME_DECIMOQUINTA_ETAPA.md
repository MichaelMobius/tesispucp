# Puente entre los Teoremas 3.8 y 3.20

El Teorema 3.20 usa `L = Δ` y `e = u* − h`, con residuo `f − Δh` (páginas impresas 100–103). El puente usa `h − u*` y `Δh − f`. En los dos espacios normados, invertir el orden de la resta conserva la norma. La ecuación distribucional de la solución conserva el signo `Δu* = f`.

## Resultado en la clase homogénea exacta

| Identificación | Declaración |
|---|---|
| Multiplicar un candidato globalmente suave por `ψ` y representarlo en el grafo Sobolev | `CandidatoPoisson`, `aproximacionPoisson`, `grafoPoisson` |
| La evaluación de `ψq` en la frontera topológica coincide con el dato cero | `psiCuadrado_cero_frontera`, `operadorPoisson_frontera` |
| Representante de `f` y del residuo en Lebesgue restringida al cuadrado | `datoPoissonLp_ae`, `residuoPoisson_ae` |
| Identidad de la pérdida residual por cambio de medida | `medidaResidualPoisson`, `perdidaResidualPoisson_eq` |
| Cota de energía por la raíz de la pérdida | `energia_de_perdidaPoisson` |
| Paso de tasa poblacional a convergencia y tasa energética casi seguras | `transferencia_energiaPoisson_ae`, `teorema320_poisson_de_teorema38` |

`operadoresPoisson` usa el laplaciano clásico de la aproximación y la evaluación de su función ambiente como operador de frontera. La anulación se prueba en toda la frontera, incluidos los vértices, usando que un punto fronterizo tiene ambas coordenadas en `[-1,1]` y alguna coordenada igual a un extremo. El término de pérdida de frontera se anula bajo la medida concentrada en esa frontera.

La medida residual es `(volume.restrict cuadrado).withDensity (ENNReal.ofReal ∘ D.rho)`. El dato puntual `f` con `MemLp f 2` se convierte mediante `MemLp.toLp`. La igualdad casi en todas partes del residuo puntual y el residuo del grafo se usa al cambiar de medida. La cota `rho0 ≤ rho` asegura que la conversión de la densidad a reales conserva su valor casi en todas partes. La integrabilidad ponderada se obtiene de la integrabilidad del residuo cuadrático bajo la medida de muestreo. En la instancia integrada, esta última se deriva de las cotas Hölder, los soportes acotados y la mensurabilidad espacial. La mensurabilidad casi en todas partes de `f` se transporta a la medida residual por absoluta continuidad. La comparación no exige cota superior de densidad.

La constante que multiplica `sqrt(loss)` es `constanteEnergiaCuadrado / sqrt(rho0 * lr)`. La proporciona la estimación uniforme previa para `u* ∈ H01` con `Δu* = f` distribucional. Es fija respecto del índice y de la realización. El coeficiente de la cota asintótica puede depender de la realización a través de (3.26). La raíz de la pérdida transforma el exponente `−α/2` en `−α/4`, con el índice residual `mr(n)`. Esto da (3.72) y (3.73) en la clase `ψq`.

## Premisas heredadas y alcance

- El teorema integrado invoca `teorema38_dim2` sobre una única familia `problemaMuestral` y obtiene la tasa poblacional como conclusión intermedia. Recibe la normalización de la medida residual, los datos de masa y particiones, el muestreo i.i.d., el crecimiento y relación de tamaños, las cotas Hölder y las selecciones mensurables con minimalidad global, interpolación exacta y regularidad uniforme. La seminorma interior se suministra como dato de la clase y se identifica con la seminorma exacta al instanciar el funcional literal de la tesis.
- La elección de `ψq` garantiza la condición de Dirichlet y la pertenencia al subespacio Sobolev correspondiente por la construcción previa del grafo. La existencia de clases neuronales concretas, minimizadores y comparadores compatibles sigue siendo una premisa. La convergencia está formulada en el filtro casi seguro.
- La instancia supone directamente `u* ∈ H01`. El paso general desde coincidencia de trazas a pertenencia del error a `H01`, el caso no homogéneo y las penalizaciones finitas de frontera requieren resultados distintos. La ruta alternativa (3.75) no interviene en la tasa de esta instancia.

## Verificación

Las directivas `#print axioms` se ejecutan con `lake build` y quedan registradas en el [CI de la PR #17](https://github.com/MichaelMobius/tesispucp/pull/17/checks). Las versiones son Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
