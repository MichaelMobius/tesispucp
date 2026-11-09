# Mapa de dependencias matemáticas — cuarta etapa

## Cuadrado y condición de Dirichlet exacta

Fuente: Lema 3.19, estimación (3.71), y Teorema 3.20, paso determinista (3.74), de la tesis. La constante óptima `Cₚ = √2/π` se afirma posteriormente en el **Corolario 3.23**, ecuación (3.80); no es una hipótesis del Teorema 3.20.

| Paso | Declaración Lean | Estado y alcance |
|---|---|---|
| `U=(-1,1)²` abierto y acotado | `cuadrado`, `cuadrado_abierto`, `cuadrado_acotado` | Compilado |
| Factor `ψ=(1-x²)(1-y²)` y anulación cuando alguna coordenada tiene cuadrado 1 | `psiCuadrado`, `psiCuadrado_cero_coord0`, `psiCuadrado_cero_coord1` | Compilado; no sustituye una caracterización de la frontera |
| `ψ q` para `q` suave con soporte compacto **interior** | `psiPorPrueba`, `psiPorPrueba_mem_H01` | Compilado; clase más estrecha que la arquitectura PINN de la tesis |
| Convergencia en `L²` de función y gradiente implica pertenencia a `H01`; y recíprocamente un elemento `H01` admite tal aproximación por pruebas | `mem_H01_de_aproximacion_l2`, `existe_aproximacion_l2_de_H01`, `psiPorPrueba_aproximacion_l2` | Compilado. Para `ψ q` con soporte interior la aproximación existe; no se ha construido el recorte para `q` no nula hasta la frontera |
| Cota energética en el cuadrado para `e∈H01`, `Δe=r∈L²` | `energia_dirichlet_cuadrado` | Compilado, por especialización del Lema 3.19 plano |
| Cota (3.74) para la diferencia de grafos `h-u*` | `estimacion_error_dirichlet_exacto` | Compilado **condicionalmente** a `h-u*∈H01` y a la identidad distribucional del residuo |
| Cota para dos candidatos `ψ q` con `q` de soporte interior | `estimacion_psi_por_pruebas` | Compilado; pertenencia `H01` demostrada, identificación de `r` todavía como hipótesis |

## Puentes pendientes

1. **Arquitectura completa `ψ q`.** Para `q` suave hasta la frontera, construir `χ_δ∈C_c^∞(U)` igual a uno fuera de una franja de ancho `O(δ)`, con `‖∇χ_δ‖∞≤C/δ`; demostrar que `χ_δ ψ q→ψ q` y `∇(χ_δ ψ q)→∇(ψ q)` en `L²(U)`. La estimación crítica es `ψ q=O(δ)` en la franja, por lo que el término `(∇χ_δ)ψ q` tiene norma `L²` de orden `O(√δ)`. El lema de EllipticPDE `H1Graph.mem_H01_of_hasCompactSupport` mollifica funciones ya soportadas dentro del abierto, pero no construye este recorte de frontera.
2. **Funciones suaves `h,u*` con igual valor en toda la frontera.** Falta demostrar directamente que `h-u*∈H01`, sin postular factorización por `ψ`. Con regularidad `C¹` hasta la frontera, la cota `|h-u*|≤d(x,∂U) sup‖∇(h-u*)‖` permite el mismo recorte. Hay que formalizarla en el cuadrado y establecer la convergencia de ambos componentes. Para funciones meramente `H¹` con igual traza se necesita la caracterización `ker(trace)=H01` en este dominio Lipschitz; no se encontró ese puente para `H1Graph.H01` en la revisión fijada de EllipticPDE/Mathlib.
3. **Residuo concreto.** Probar que `Δ(h-u*)=Δh-f` en distribuciones y que el residuo está en `L²`, a partir de las regularidades del Teorema 3.20. El teorema actual lo recibe como igualdad distribucional explícita.
4. **Constante óptima.** `Poincare.BoxSlice` da en el cuadrado una cota cuadrática no óptima `(2)²/2=2` por dirección. Para `Cₚ=√2/π` se necesita la desigualdad de Wirtinger de Dirichlet con constante `(2/π)²` en cada intervalo `(-1,1)`, aplicar Fubini en las dos direcciones y pasar de pruebas a `H01` por densidad. Equivalentemente, formalizar la primera autofrecuencia `λ₁=π²/2` y la expansión espectral usada en el Corolario 3.23.
5. **Teorema 3.20 completo.** Siguen sin formalizarse las clases de redes con Dirichlet exacto, los comparadores/minimizadores y las hipótesis probabilísticas de muestreo. Una penalización finita de frontera no implica traza nula ni permite aplicar esta cota sin un término de frontera adicional.

## Cadena formal previa del Lema 3.19 en ℝ²

Fuente: Lema 3.19 de la tesis (estimación determinista (3.71)) y Teorema 3.20 (resultado PINN posterior). El código nuevo se limita al caso `Plano := EuclideanSpace ℝ (Fin 2)`.

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

## Dependencias restantes del Teorema 3.20

- Demostrar que la igualdad de trazas de las funciones PINN concretas implica que su diferencia pertenece al `H01` de EllipticPDE. En el cuadrado, se propone la aproximación directa por pruebas descrita arriba.
- Formalizar las funciones `u*`, `hₘ` y la igualdad de su laplaciano residual en los tipos concretos. La forma abstracta de la cota determinista (3.74) para `h-u*` ya compila con las dos premisas analíticas explícitas.
- Formalizar las hipótesis de muestreo, comparadores, minimizadores, densidad y peso residual del Teorema 3.8 para obtener la convergencia y tasa probabilística de 3.20.
- Extender el nuevo puente a dimensión finita general si se desea fuera de `ℝ²`; la prueba actual usa la base ortonormal de dos elementos.

Otros resultados: Teorema 3.8, Lema 3.24, Teoremas 3.4 y 3.18, Proposiciones 3.15 y 3.25 y Corolario 3.26 siguen pendientes como resultados completos. Sus pasos parciales de `Minimalidad.lean` y `RedCuadratica.lean` permanecen compilados.

