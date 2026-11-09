# Mapa de dependencias matemáticas — segunda etapa

Fuente: tesis adjunta, Lema 3.19 (ecuación 3.71, PDF pp. 111–113) y Teorema 3.20 (PDF pp. 113–115). La primera es una estimación determinista para el error `e ∈ H₀¹(U)` con `Δe ∈ L²(U)`; el segundo incorpora además la estructura probabilística y de residuos del PINN.

## Cadena Lean comprobada

| Nodo | Fuente Lean | Estado |
|---|---|---|
| Error `U ∈ H₀¹` representado por el cierre de grafos de prueba, con `fnL U` y `gradL U` | `EllipticPdes.Sobolev.Graph`, `H1Graph.H01` | Compilado |
| `gradL U` es el gradiente distribucional de `fnL U` para `Ω` abierto | `H01_le_W12`, `mem_W12_iff_hasWeakFDerivOn`, `h01_gradiente_distribucional` | Compilado |
| Poincaré cuadrático `‖fnL U‖² ≤ C‖gradL U‖²`, `C ≥ 0` | `poincare_H01_of_bounded` | Compilado |
| Constante de tesis `Cₚ > 0`: tomar `Cₚ = √(C+1)`, por lo que `C ≤ Cₚ²` | `exists_poincare_constant` | Compilado |
| Norma Sobolev del grafo `‖U‖² = ‖fnL U‖² + ‖gradL U‖²` | `H1Graph.norm_sq_eq`, `norma_sobolev_cuadratica` | Compilado |
| Green para `U` a partir de la identidad sobre funciones de prueba | `HasTestLaplacian`, `H01_subset_of_isClosed`, `green_por_densidad` | Compilado, condicionado a la identidad distribucional sobre pruebas |
| Estimación `‖U‖ ≤ Cₚ√(1+Cₚ²)‖r‖` | `energia_norma_par_debil`, `energia_sobolev_de_laplaciano_de_prueba` | Compilado, condicionado a `HasTestLaplacian U r` |

## Puente analítico pendiente para el Lema 3.19 literal

Formalizar un operador laplaciano en distribuciones `𝓓'(Ω)` para el dominio abierto `Ω` y demostrar, para `U : H1Graph.H01 μ Ω` y `r : Lp ℝ 2 (μ.restrict Ω)`, el siguiente puente:

`Distribution.laplacian (Distribution.ofFun Ω (fnL U) μ ⊤) = Distribution.ofFun Ω r μ ⊤` **implica** `HasTestLaplacian U r`.

La formulación de `HasTestLaplacian` es exactamente `⟪gradL U, gradCls φ⟫ = -⟪r, fnCls φ⟫` para toda función de prueba `φ`. La demostración del puente requiere: (1) definir el laplaciano distribucional como suma finita de segundas derivadas direccionales en una base ortonormal; (2) aplicar la identidad de derivada distribucional de `HasWeakFDerivOn` a las derivadas de `φ`; (3) convertir las integrales a productos internos `L²`. `EllipticPDE/Sobolev/WeakDeriv.lean` proporciona la primera derivada distribucional, pero no expone el lema de segunda derivada/laplaciano abierto con esta conclusión. No se introdujo como axioma. Por ello el Lema 3.19, con su premisa literal `Δe ∈ L²`, sigue **pendiente**; la estimación bajo la formulación de prueba está **demostrada condicionalmente**.

También falta probar que la igualdad de trazas del Teorema 3.20 coloca el error en este `H01` definido por cierre; esto puede requerir la caracterización por traza en dominios Lipschitz. La desigualdad energética en `H01` solo requiere que `Ω` sea acotado; la condición Lipschitz de la tesis no se añadió como hipótesis Lean.

## Otros resultados del Capítulo III

| Resultado | Estado |
|---|---|
| Teorema 3.8 | Pendiente; `Minimalidad.lean` compila dos pasos condicionales |
| Teorema 3.20 | Pendiente; requiere además trazas, Teorema 3.8 y cotas de densidad/peso residual |
| Lema 3.24 | Pendiente; `RedCuadratica.lean` compila tres identidades algebraicas |
| Teoremas 3.4 y 3.18; Proposiciones 3.15 y 3.25; Corolario 3.26 | Pendientes |

