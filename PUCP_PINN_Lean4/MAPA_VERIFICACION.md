# Mapa de dependencias matemáticas — tercera etapa

Fuente: Lema 3.19 de la tesis (estimación determinista (3.71)) y Teorema 3.20 (resultado PINN posterior). El código nuevo se limita al caso `Plano := EuclideanSpace ℝ (Fin 2)`.

## Cadena formal del Lema 3.19 en ℝ²

| Paso | Declaración Lean | Estado |
|---|---|---|
| Error en `H₀¹(Ω)` como cierre de grafos de prueba, con `fnL U` y `gradL U` | `H1Graph.H01` de EllipticPDE | Definición de biblioteca |
| `gradL U` es la derivada distribucional de `fnL U` | `h01_gradiente_distribucional`; `H01_le_W12`; `mem_W12_iff_hasWeakFDerivOn` | Compilado |
| `Δ = ∂₁² + ∂₂²` en distribuciones sobre `Ω` abierto | `laplacianoDistribucional`, `laplacianoDistribucional_eq_suma` | Compilado |
| Una derivada direccional de prueba conserva suavidad, soporte compacto y `tsupport ⊆ Ω` | `derivadaPrueba` | Compilado |
| `Δ fnL U = div gradL U` en `𝓓′(Ω)` | `laplaciano_ofFun_eq_div_grad` | Compilado |
| Signo: `⟨ΔU,φ⟩ = -∫ gradL U · ∇φ` | `laplaciano_eval_suma`, `suma_derivadas_eq_producto`, `laplaciano_eval_producto` | Compilado |
| Integrales globales = productos internos `L²(Ω)` | `inner_gradiente_prueba_eq_integral`, `inner_residuo_prueba_eq_integral` | Compilado |
| `ΔU=r` en `𝓓′(Ω)` implica `HasTestLaplacian U r` | `laplaciano_distribucional_implica_prueba` | Compilado |
| Representante `r ∈ L²` único | `laplaciano_distribucional_l2_unico` | Compilado |
| Identidad de Green con prueba `U` por densidad | `green_por_densidad` | Compilado |
| Poincaré con `Cₚ=√(C+1)>0` | `exists_poincare_constant`; `poincare_H01_of_bounded` | Compilado |
| `‖U‖² = ‖fnL U‖² + ‖gradL U‖²` | `norma_sobolev_cuadratica`; `H1Graph.norm_sq_eq` | Compilado |
| `‖U‖ ≤ Cₚ√(1+Cₚ²)‖r‖` | `energia_sobolev_de_laplaciano_distribucional`, `energia_sobolev_plano_volumen` | Compilado |

El enunciado final usa `Ω : Opens Plano` acotado, `U : H1Graph.H01 volume Ω`, `r : Lp ℝ 2 (volume.restrict Ω)` y la igualdad `laplacianoDistribucional Ω (Distribution.ofFun Ω (fnL U) volume ⊤) = Distribution.ofFun Ω r volume ⊤`. Esta igualdad representa con precisión `Δe = r ∈ L²`. La cota usa el `r` único. No requiere hipótesis adicional de Lipschitz: el resultado es válido para el `H01` definido por cierre en cualquier abierto acotado. La tesis asume un dominio Lipschitz, que satisface estas condiciones.

## Dependencias aún pendientes para el Teorema 3.20

- Demostrar que la igualdad de trazas de las funciones PINN concretas implica que su diferencia pertenece al `H01` de EllipticPDE. Esto requiere una caracterización por traza en el dominio Lipschitz o una aproximación directa por pruebas.
- Formalizar las funciones `u*`, `hₘ`, su laplaciano residual y la cota determinista (3.74) en sus tipos concretos.
- Formalizar las hipótesis de muestreo, comparadores, minimizadores, densidad y peso residual del Teorema 3.8 para obtener la convergencia y tasa probabilística de 3.20.
- Extender el nuevo puente a dimensión finita general si se desea fuera de `ℝ²`; la prueba actual usa la base ortonormal de dos elementos.

Otros resultados: Teorema 3.8, Lema 3.24, Teoremas 3.4 y 3.18, Proposiciones 3.15 y 3.25 y Corolario 3.26 siguen pendientes como resultados completos. Sus pasos parciales de `Minimalidad.lean` y `RedCuadratica.lean` permanecen compilados.

