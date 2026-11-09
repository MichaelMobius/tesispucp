import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Capitulo III: paso algebraico del Teorema 3.8

La perdida empírica y la regularizacion son no negativas, y los pesos
son iguales y positivos. No se afirma aquí la existencia de un minimizador
ni la validez de la hipotesis de comparadores; se usan como premisas.
-/

namespace TesisPINN

/-- Si `L + a * R <= a * Rstar` y `L >= 0`, la regularidad del
    minimizador no excede la del comparador. -/
theorem regularidad_controlada
    (a L R Rstar : ℝ)
    (ha : 0 < a) (hL : 0 ≤ L)
    (hcomparacion : L + a * R ≤ a * Rstar) :
    R ≤ Rstar := by
  have hproducto : a * R ≤ a * Rstar := by
    linarith
  exact (mul_le_mul_iff_of_pos_left ha).mp hproducto

/-- El término de perdida se controla por el mismo comparador si
    la regularización es no negativa. -/
theorem perdida_empirica_controlada
    (a L R Rstar : ℝ)
    (ha : 0 < a) (hR : 0 ≤ R)
    (hcomparacion : L + a * R ≤ a * Rstar) :
    L ≤ a * Rstar := by
  have hno_neg : 0 ≤ a * R := mul_nonneg ha.le hR
  linarith

#print axioms TesisPINN.regularidad_controlada
#print axioms TesisPINN.perdida_empirica_controlada

end TesisPINN
