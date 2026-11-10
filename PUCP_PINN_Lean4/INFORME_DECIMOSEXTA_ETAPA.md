# Teorema 3.20 con Dirichlet no homogéneo exacto

`teorema320_levantado_de_teorema38` especializa (3.72) y (3.73) al cuadrado `U=(-1,1)²`, con dato de frontera que admite un levantamiento globalmente suave `G` y candidatos `h_n=G+ψq_n` con `q_n` globalmente suave. La solución se representa por un grafo `u` y se supone `u−G ∈ H01` y `Δu=f` en distribuciones, donde el dato puntual tiene representante `L²` en Lebesgue restringida al cuadrado.

## Identificaciones verificables

| Paso | Declaraciones Lean |
|---|---|
| Valor y gradiente de `G` en `L²`. Su derivada de Fréchet clásica satisface la identidad de derivada débil. | `grafoSuaveCuadrado`, `grafoSuaveCuadrado_mem_W12` |
| Sumar el grafo de `ψq`, que pertenece a `H01 ≤ W12`. | `grafoLevantado_mem_W12`, `grafoLevantado_fnL_ae` |
| Igualdad con el dato en la frontera topológica, incluidos los vértices. | `aproximacionLevantada_frontera` |
| El error es `ψq − (u−G)` y pertenece a `H01`. | `errorLevantado_eq`, `errorLevantado_mem_H01` |
| El residuo puntual y su representante `L²` coinciden casi en todas partes. Es el laplaciano distribucional del error. | `residuoLevantado_ae`, `laplaciano_errorLevantado` |
| El residuo `Δ(G+ψq)−f` coincide con `Δ(ψq)−(f−ΔG)`. Esta igualdad reutiliza el cambio de medida de la instancia homogénea. | `perdidaResidualLevantada_eq` |
| La estimación uniforme de energía controla el error por `K_E sqrt(loss)`. | `energia_de_perdidaLevantada` |
| Aplicar `teorema38_dim2` y reutilizar la transferencia de raíz cuadrada de la etapa anterior. | `teorema320_levantado_de_teorema38` |

La ecuación de la tesis tiene `L=Δ`. La orientación Lean es `h−u` y su residuo es `Δh−f`. La tesis escribe `u−h` y `f−Δh`. Invertir ambas restas conserva las normas. La constante `K_E = constanteEnergiaCuadrado / sqrt(rho0 * lr)` es independiente de la realización y del tamaño. La tasa poblacional obtenida de (3.26) es `O(mr(n)^(-α/2))` y su raíz da `O(mr(n)^(-α/4))`. No se identifica `mr(n)` con `n` ni con `mb(n)`.

## Datos de la instancia estadística

`operadoresLevantados` usa `L[q]=Δ(G+ψq)` y `B[q](x)=(G+ψq)(x)`. El dato de frontera es la restricción de `G` al soporte `Γ=frontier cuadrado`. La entrada `SG` se usa tanto para la cota Hölder de ese dato como para la seminorma asignada a cada candidato, y `CotasHolder` exige que sea válida. Se puede tomar la seminorma exacta de la restricción de `G` para representar literalmente el regularizador. El término cuadrático de frontera se anula por igualdad puntual bajo la medida concentrada en `Γ`.

La medida residual se fija como `medidaResidualPoisson D = (volume.restrict U).withDensity (ENNReal.ofReal ∘ D.rho)`. La normalización es la premisa `IsProbabilityMeasure (medidaResidualPoisson D)`, independiente de la cota esencial inferior. La prueba usa la cota inferior positiva y deriva la integrabilidad ponderada a partir de integrabilidad espacial bajo esa medida. La integrabilidad espacial de la instancia sale de los soportes acotados, `CotasHolder` y la mensurabilidad espacial de los residuos. No se requiere cota superior de la densidad como hipótesis de la comparación energética.

Las cotas de masa, particiones, leyes i.i.d., tamaños positivos, crecimiento y relación de tamaños vienen del Teorema 3.8. Se presupone una familia de clases con selecciones mensurables que satisfacen la minimalidad global, interpolación exacta y cota uniforme de comparadores. El levantamiento garantiza la condición de frontera. La existencia de tales selecciones para clases neuronales concretas sigue siendo una premisa.

## Mensurabilidad y obligaciones pendientes

`measurable_grafoLevantado` usa la estructura de Borel del espacio de grafos. Basta que la trayectoria `ω ↦ grafoPoisson(q(ω))` sea medible, por ejemplo si la aplicación de candidatos al grafo es medible para la estructura elegida en los candidatos y la selección también lo es. La traslación por el grafo fijo de `G` es continua. `prob_uno_convergenciaLevantada` reduce el evento exacto a la convergencia de una sucesión de normas reales medibles y demuestra que tiene probabilidad uno. La conclusión integrada se da en el filtro casi seguro sin suponer mensurabilidad automática de la aplicación de candidatos al grafo.

La instancia usa un levantamiento globalmente `C∞` y supone directamente `u−G∈H01`. Quedan pendientes el paso general desde una traza Sobolev prescrita a esa pertenencia, levantamientos para datos de frontera de regularidad inferior, el caso con penalización finita y la verificación de las hipótesis variacionales para arquitecturas neuronales explícitas.

Las directivas `#print axioms` se ejecutan en `lake build`. El historial de verificación está en los [controles de la PR #18](https://github.com/MichaelMobius/tesispucp/pull/18/checks). Se conservan Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
