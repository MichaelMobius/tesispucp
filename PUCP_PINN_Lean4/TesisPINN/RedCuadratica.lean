import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Capitulo III, Lema 3.24: identidades algebraicas de la red cuadratica

Esto formaliza las identidades de registro, multiplicacion y factor de
frontera. La existencia de una arquitectura comun para todo m necesita
ademas formalizar la red parametrizada y la induccion sobre monomios.
-/

namespace TesisPINN

/-- Una combinación afín decodifica `((v+1)^2,(v-1)^2)`. -/
theorem decodificar_registro (v : ℝ) :
    ((v + 1) ^ 2 - (v - 1) ^ 2) / 4 = v := by
  ring

/-- El producto se obtiene combinando dos activaciones cuadráticas. -/
theorem multiplicacion_cuadratica (u v : ℝ) :
    ((u + v) ^ 2 - (u - v) ^ 2) / 4 = u * v := by
  ring

/-- Identidad del factor de frontera para Dirichlet fuerte. -/
theorem factor_frontera (x y : ℝ) :
    (1 - x ^ 2) * (1 - y ^ 2) =
      1 - x ^ 2 - y ^ 2 + x ^ 2 * y ^ 2 := by
  ring

#print axioms TesisPINN.decodificar_registro
#print axioms TesisPINN.multiplicacion_cuadratica
#print axioms TesisPINN.factor_frontera

end TesisPINN
