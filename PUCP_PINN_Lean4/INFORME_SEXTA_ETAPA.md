# Sexta etapa: residuo laplaciano concreto

## Correspondencia con la tesis

La fuente es el Lema 3.19, ecuación (3.71), y el paso determinista del Teorema 3.20, ecuación (3.74), en las páginas PDF 111–116 de `Tesis_PUCP_Revision_Ortotipografica_20261107-2.pdf` (páginas impresas 98–103). La tesis fija `L=Δ`, `Δu*=f` y residuo interior `r_h=Δh−f`. En la demostración escribe `e_m=u*−h_m`, por lo que `Δe_m=f−Δh_m`. Nuestro código usa `e=h−u*` y `r=Δh−f`; la norma del error y del residuo no cambian al invertir ambos signos. La variante `−Δu=f_num` se interpreta con `f=−f_num`, de acuerdo con la observación de signo de la tesis.

## Resultados formales completos

| Declaración Lean | Afirmación |
|---|---|
| `laplacianoClásico_eq_mathlib` | La suma de dos segundas derivadas direccionales en `basePlano` coincide con `Laplacian.laplacian` de Mathlib. |
| `laplaciano_distribucional_eq_clásico` | Para `f` globalmente `C∞`, el laplaciano distribucional de `Distribution.ofFun f` es la distribución del laplaciano clásico. Se usa `hasWeakFDerivOn_fderiv` dos veces; no hay cambio de signo. |
| `laplacianoClásico_memLp`, `laplacianoLp_ae` | El laplaciano clásico continuo pertenece a `L²((-1,1)²)`; `laplacianoLp` es su clase canónica. |
| `laplaciano_distribucional_errorPsi` | Para `q_h,q_u` globalmente `C∞`, la distribución `Δ(ψq_h−ψq_u)` es la distribución de `residuoPsi q_h q_u∈L²`. |
| `estimacion_psi_suave_residuo_concreto` | Obtiene `‖psiGraph q_h−psiGraph q_u‖ ≤ Cₚ√(1+Cₚ²)‖residuoPsi q_h q_u‖` para algún `Cₚ>0`, sin premisas `hΔ` ni `he`. |

La última fila es una instancia determinista de la estimación energética (3.71)/(3.74) para **dos candidatos suaves de la forma `ψq`**. No es el Teorema 3.20 completo.

## Solución exacta general: resultado condicional

`estimacion_psi_frente_solucion_exacta` permite que `u*` sea un grafo Sobolev arbitrario y no exige `u*=ψq`. Sus premisas visibles son `u*∈H1Graph.H01` y `Δu*=f` en distribuciones, con `f∈L²(U)`. Concluye la cota para `psiGraph q−u*` con residuo `laplacianoLp (ψq)−f`. La ecuación residual ya se deduce dentro de la prueba por linealidad; no se postula como axioma.

La tesis, para frontera general `g`, supone que `h` y `u*` tienen la misma traza y deduce `h−u*∈H₀¹` mediante el teorema de trazas. Ese puente no está en la formalización. Nuestra premisa `u*∈H01` corresponde al caso homogéneo y es más fuerte que la hipótesis general del Teorema 3.20. La construcción de un levantamiento de frontera para `g≠0` queda pendiente.

## Otros pendientes

- Formalizar el paso de igualdad de trazas a pertenencia del error a `H1Graph.H01` para `h,u*` generales; para el cuadrado homogéneo ya se probó directamente para `ψq`.
- Conectar comparadores de Hermite y redes PINN concretas con las funciones `q` de esta etapa.
- Formalizar las hipótesis de muestreo, minimización global y tasas de convergencia (3.72)–(3.73).
- Recuperar la constante óptima `√2/π` del Corolario 3.23. La cota actual utiliza una constante de Poincaré positiva existente.
- El caso de penalización de frontera requiere una estimación con defecto de frontera; no se deduce del caso de Dirichlet exacto.

## Verificación

- `lake build`: éxito local (3189 trabajos).
- `#print axioms` de los teoremas nuevos: solo `propext`, `Classical.choice`, `Quot.sound`.
- Sin `sorry`, `admit` ni axiomas nuevos en el módulo nuevo.
- Lean 4.35.0, Mathlib v4.35.0, EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`; pruebas anteriores y PDF intactos.
- CI de la PR borrador apilada: pendiente de ejecución remota.
