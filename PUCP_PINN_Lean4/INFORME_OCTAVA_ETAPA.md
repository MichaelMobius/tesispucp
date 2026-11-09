# Octava etapa: pérdida poblacional ponderada

## Fuente y correspondencia

Se revisó la tesis `Tesis_PUCP_Revision_Ortotipografica_20261107-2.pdf`. La Hipótesis 3.2 (página PDF 56, impresa 43) exige muestreo interior y de frontera i.i.d. e independiente, densidades de medidas de probabilidad con ínfimos esenciales positivos, particiones con masas mínimas y cotas superiores de masa de bolas (3.4). La Hipótesis 3.7 (páginas PDF 77–78, impresas 64–65) exige clases `H_m`, comparadores que interpolan exactamente (3.24), seminormas Hölder uniformes (3.25) y selecciones mensurables en el marco aleatorio.

El Teorema 3.8 (páginas PDF 79–80, impresas 66–67) presupone minimizadores globales mensurables, pesos residuales positivos fijos, pesos de regularización (3.23), compatibilidad de los tamaños `mr`, `mb` y un espacio de probabilidad común. En el evento de cobertura concluye `LossPINN(h_m;λ)=O(mr^(-α/d))` (3.26); casi seguramente concluye convergencia `C⁰` de los residuos interior y de frontera (3.27), con las tasas `C⁰` de (3.28).

El Teorema 3.20 (páginas PDF 113–115, impresas 100–102) considera Poisson `L=Δ`, Dirichlet exacto, `u*∈H¹(U)∩C⁰(U)`, `Δu*=f∈L²(U)`, candidatos de traza igual a la de `u*`, y laplacianos en `L²`. La tesis obtiene convergencia `H¹` casi segura (3.72), tasa `O(mr^(-α/(2d)))` bajo `ρr≥ρ₀>0` (3.73), y cota energética determinista (3.74). En el cuadrado `d=2`, la pérdida tiene exponente `-α/2` y el error `H¹` tiene `-α/4`. El índice `n` que enumera realizaciones de los tamaños no se identifica con `mr(n)`.

## Código y pruebas compiladas

El módulo `TesisPINN/PerdidaPoblacional.lean` define `DensidadResidual` y `perdidaResidualPoblacional D λr r = λr ∫_U ρr(x)·r(x)² dx` para `r : Lp ℝ 2 (volume.restrict cuadrado)`. La densidad es medible, satisface `ρ₀>0` y `ρ₀≤ρr≤ρMax` casi en todas partes. La cota superior **no aparece como tal en la Hipótesis 3.2**: es una premisa adicional visible que permite demostrar `ρr²∈L¹`, y debe descargarse o sustituirse por integrabilidad ponderada para alcanzar el enunciado general de la tesis. El módulo no codifica aún `∫ρr=1`; la normalización no se usa en esta desigualdad.

`residuo_norm_sq_eq_integral` usa la estructura Hilbert de `L²` para demostrar `‖r‖²=∫r²`. `integrable_residuo_ponderado` demuestra la finitud de la integral. `cota_residuo_por_densidad` obtiene `ρ₀‖r‖²≤∫ρr²`. Si una pérdida real total domina el término residual, `cota_residuo_por_perdida` obtiene `‖r‖²≤Loss/(ρ₀λr)` y `cota_norma_residuo_por_perdida` justifica la raíz cuadrada y el signo de `Loss`. La dominación de la pérdida es una premisa explícita; no se ha definido todavía la pérdida PINN completa con sus términos de frontera y regularización.

`estimacion_error_por_perdida` combina la comparación con `estimacion_uniforme_psi_solucion_exacta` y obtiene `‖ψq−u*‖H¹≤K/√(ρ₀λr)·√Loss`. Requiere `u*∈H1Graph.H01`, `Δu*=f` en distribuciones y `q` globalmente `C∞`. `tendsto_psiGraph_de_perdida` transfiere `Loss_n→0` a `H¹`. `tasa_error_de_perdida_mr` transfiere la cota supuesta `Loss_n≤A·mr(n)^(-α/2)` a `‖ψq_n−u*‖H¹≤K√A/√(ρ₀λr)·mr(n)^(-α/4)`. La cota de pérdida no se demuestra.

`tendsto_psiGraph_de_perdida_ae` usa un espacio de probabilidad y aplica la implicación determinista casi en todas partes. `prob_uno_tendsto_psiGraph_de_perdida` exige mensurabilidad de cada pérdida y aproximante como funciones de `ω`; prueba que ambos eventos de convergencia son mensurables y transfiere la probabilidad uno. La mensurabilidad del grafo se trata con la topología boreliana y la segunda numerabilidad de `EllipticPdes.Sobolev.GraphDense`. La convergencia de la pérdida con probabilidad uno es una **premisa**, no una conclusión nueva de i.i.d. o minimalidad.

La tesis escribe `e_m=u*−h_m`, `r_m=f−Δh_m`; Lean usa `h_m−u*` y `Δh_m−f`, cuya norma coincide. La conclusión nueva se limita al caso homogéneo `h_m=ψq_m`, `u*∈H01` en `(-1,1)²`; no demuestra el Teorema 3.20 general ni el caso de penalización finita de frontera.

## Estado pendiente

- Formalizar las medidas de probabilidad interior y de frontera, la normalización de `ρ`, muestreo i.i.d., independencia, particiones, cobertura y cotas probabilísticas de la Hipótesis 3.2.
- Formalizar clases neuronales, comparadores de interpolación exacta, regularidad uniforme, selección mensurable de comparadores y minimizadores globales de la Hipótesis 3.7.
- Derivar (3.26) de esas hipótesis. Solo entonces la transferencia probabilística nueva puede aplicarse sin una premisa de convergencia de la pérdida.
- Descargar la cota superior esencial de `ρ` o formular el término ponderado con una hipótesis explícita de integrabilidad que siga del control de pérdida; demostrar la normalización probabilística `∫ρ=1`.
- Pasar del caso `ψq` homogéneo a candidatos generales con Dirichlet exacto mediante trazas. La penalización de frontera requiere un argumento diferente.

## Verificación

- Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae` permanecen fijados.
- `lake build` local: éxito, 3197 trabajos, tras importar `GraphDense` y el módulo nuevo.
- `#print axioms` de todos los teoremas nuevos: únicamente `propext`, `Classical.choice`, `Quot.sound`.
- Sin `sorry`, `admit` ni axiomas nuevos en el módulo nuevo. Los módulos previos y el PDF no se modificaron.
- CI de la base PR #9: éxito, ejecución [42561412158](https://github.com/MichaelMobius/tesispucp/actions/runs/42561412158). CI Lean 4 / Mathlib de la PR borrador #10: éxito, ejecución [42563330773](https://github.com/MichaelMobius/tesispucp/actions/runs/42563330773).

