# Séptima etapa: constante uniforme y transferencia determinista

## Fuente y alcance exacto

La tesis, en el Teorema 3.8 (páginas PDF 79–80; impresas 66–67), supone las Hipótesis 3.2 y 3.7, pesos residuales positivos fijos, comparadores exactos con regularidad uniforme, minimizadores globales mensurables, tamaños de muestras i.i.d. compatibles y un evento de cobertura. Concluye una tasa de pérdida poblacional (3.26) en ese evento y convergencia `C⁰` de los residuos interior y de frontera con probabilidad uno (3.27), además de tasas uniformes (3.28).

El Teorema 3.20 (páginas PDF 113–115; impresas 100–102) añade Dirichlet fuerte, `u*∈H¹∩C⁰`, `Δu*=f∈L²`, candidatos `h_m∈H¹∩C⁰` con la misma traza y `Δh_m∈L²`. La tesis obtiene convergencia `H¹` casi segura (3.72) y, bajo `ρ_r≥ρ₀>0`, la tasa `O(m_r^{-α/(2d)})` (3.73). El paso energético determinista es (3.74), con `L=Δ` y `‖f−Δh_m‖_{L²}`.

La formalización nueva se limita al cuadrado `U=(-1,1)²`, dato homogéneo `g=0`, candidatos `h_m=ψq_m` con `q_m` globalmente `C∞` y solución exacta fija `u*∈H1Graph.H01` que satisface `Δu*=f` en distribuciones. La premisa `u*∈H01` es más fuerte que la igualdad de trazas de `h_m,u*` en el Teorema 3.20 general. No se formaliza el teorema de trazas ni la selección aleatoria de minimizadores.

## Resultados compilados

| Teorema Lean | Conclusión y relación con la tesis |
|---|---|
| `constanteEnergiaCuadrado_pos`, `energia_cuadrado_uniforme` | Existe una elección fija `K=Cₚ√(1+Cₚ²)>0` que sirve para **todos** los errores `e∈H01(U)` con `Δe=r∈L²`. Uniformiza (3.71); `K` depende solo de `U` y de la medida fijada. |
| `laplaciano_error_psi_solucion_exacta` | Identifica en distribuciones `Δ(ψq−u*)=Δ(ψq)−f`, conservando la convención `L=Δ`. |
| `estimacion_uniforme_psi_solucion_exacta` | Demuestra `‖ψq−u*‖_{H¹}≤K‖Δ(ψq)−f‖_{L²}` para cada `q` suave con **la misma** `K`: instancia homogénea de (3.74). |
| `cota_error_de_cota_residuo` | De `‖r_m‖≤ε_m` deduce `‖h_m−u*‖≤Kε_m` para todo `m`; no supone forma especial de `ε_m`. |
| `tendsto_psiGraph_de_residuo_l2` | Si `r_m→0` en la topología de `L²`, entonces `h_m→u*` en la topología de la norma del grafo `H¹`. Es el paso **determinista** previo a (3.72). |
| `tendsto_psiGraph_de_cota_residuo` | Si `ε_m→0` y `‖r_m‖≤ε_m`, concluye la misma convergencia `H¹`. |
| `tasa_potencia_psi` | Transfiere una cota residual **supuesta** `A(m+1)^(-β)` a `KA(m+1)^(-β)`. Para (3.73) falta obtener `β=α/(2d)` de la pérdida y la densidad. |
| `cota_error_en_evento` | La desigualdad vale para cada realización de cualquier `A:Set S` donde se tenga la cota residual. No hay medida sobre `S` ni afirmación de probabilidad uno. |

La definición fija de `K` usa elección clásica de una constante de Poincaré que EllipticPDE obtiene de la acotación del cuadrado. Esta elección antecede a todos los cuantificadores sobre errores y residuos. No se obtiene el valor óptimo del Corolario 3.23.

## Auditoría de coherencia de las PR #3–#8

| PR | Puente verificado | Hipótesis visibles y límite |
|---|---|---|
| #3 | Núcleo algebraico de Green, Poincaré y norma energética. | `hWeak` y `hPoincare` eran premisas explícitas; no se afirmó (3.71) incondicional. |
| #4 | `H1Graph.H01`, Poincaré desde EllipticPDE y Green por densidad. | La igualdad `Δe=r` seguía como identidad sobre pruebas; `Cₚ=√(C+1)>0`, no óptima. |
| #5 | `Δ=∂₁²+∂₂²` distribucional y `Δe=r ⇒ HasTestLaplacian` en `ℝ²`. | El signo es `∫∇e·∇φ=−∫rφ`. Se requieren `e∈H01`, `r∈L²`; el enunciado es plano, aunque la tesis usa `ℝᵈ`. |
| #6 | Especialización al cuadrado y cota para diferencia de grafos. | `h−u*∈H01` y la igualdad distribucional aún eran premisas; el primer caso `ψq` exigía soporte interior de `q`. |
| #7 | Recorte de `ψq` y convergencia de valor y gradiente en `L²`, luego `ψq∈H01`. | `q` globalmente `C∞`, sin soporte compacto. La igualdad distribucional del residuo seguía explícita. |
| #8 | Laplaciano clásico = distribucional para suaves; `Δ(ψq_h−ψq_u)` tiene representante `L²`. | La cota para dos `ψq` elimina `hΔ` y `he`; frente a `u*` general aún exige `u*∈H01` y `Δu*=f`. |

Las ramas #3–#8 forman la cadena apilada `main → #3 → #4 → #5 → #6 → #7 → #8` y permanecen borradores sin fusionar. Los enunciados no introducen hipótesis ocultas: el dominio, regularidad, pertenencia a `H01` y ecuación distribucional aparecen en sus tipos. La orientación del error en #8 y esta etapa es `h−u*`, mientras la tesis usa `u*−h`; ambos residuos y errores difieren por signo, y sus normas son iguales. `H1Graph.norm_sq_eq` identifica la norma usada con la norma `H¹` de valor y gradiente. La constante positiva elegida en #4 y fijada ahora depende del dominio; no es la constante explícita `√2/π` del Corolario 3.23.

## Trabajo probabilístico y analítico pendiente

1. Formalizar el evento de cobertura y las hipótesis 3.2 y 3.7 del Teorema 3.8, junto con comparadores, minimizadores globales mensurables y la pérdida (3.26).
2. Sobre un espacio de probabilidad común, demostrar en un evento de probabilidad uno la convergencia `C⁰` del residuo (3.27) y pasar a `L²(U)` usando `U` de medida finita. `cota_error_en_evento` podrá aplicarse trayectoria por trayectoria en ese evento, pero no demuestra que el evento sea casi seguro.
3. Para (3.73), formalizar `ρ_r≥ρ₀>0` y `λ_r>0`, la comparación `‖r_m‖²_{L²}≤(ρ₀λ_r)^{-1}LossPINN(h_m;λ)` y la tasa de pérdida (3.26), para deducir la cota residual de exponente `α/(2d)`.
4. Formalizar el puente de trazas `ker(Tr)=H01` y la igualdad de traza de `h_m,u*` en el caso general, así como datos de frontera no homogéneos. La penalización finita de frontera es un caso separado.
5. La clase neuronal polinómica concreta de los comparadores de Hermite, los tamaños de muestra y la constante óptima de Poincaré siguen pendientes.

## Verificación

- `lake build`: éxito local (3190 trabajos).
- `#print axioms`: solo `propext`, `Classical.choice`, `Quot.sound` en los teoremas nuevos.
- No hay `sorry`, `admit` ni axiomas nuevos en el módulo nuevo.
- Lean 4.35.0, Mathlib v4.35.0, EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`; pruebas anteriores y PDF intactos.
- CI de la PR borrador apilada: pendiente de ejecución remota.
