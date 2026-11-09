import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Capitulo III, Teorema 3.20: núcleo algebraico de la estimación de energía

Los argumentos analíticos de PDE (traza nula, Green, Cauchy-Schwarz,
Poincaré, interpretacion L2 y H1) no están definidos aquí; su resultado
se representa exactamente mediante `hGreen` y `hPoincare`.

`e`, `g`, `r` representan las normas L2 del error, del gradiente y del
residuo laplaciano. Son no negativas.
-/

namespace TesisPINN

open scoped RealInnerProductSpace

/-- El paso `||grad e|| <= C_P * ||Delta e||`, condicionado a Green,
    Cauchy-Schwarz y Poincaré, con cantidades no negativas. -/
theorem gradiente_controlado
    (c e g r : ℝ)
    (hc : 0 < c) (he : 0 ≤ e) (hg : 0 ≤ g) (hr : 0 ≤ r)
    (hGreen : g ^ 2 ≤ r * e)
    (hPoincare : e ≤ c * g) :
    g ≤ c * r := by
  have hmult : r * e ≤ r * (c * g) :=
    mul_le_mul_of_nonneg_left hPoincare hr
  have hcuadrado : g ^ 2 ≤ r * (c * g) :=
    le_trans hGreen hmult
  by_cases hz : g = 0
  · rw [hz]
    exact mul_nonneg hc.le hr
  · have hgp : 0 < g := lt_of_le_of_ne hg (Ne.symm hz)
    have hscaled : g * g ≤ (c * r) * g := by
      nlinarith [hcuadrado]
    exact (mul_le_mul_iff_of_pos_right hgp).mp hscaled

/-- Cota L2 del error: `||e|| <= C_P^2 * ||Delta e||`. -/
theorem error_l2_controlado
    (c e g r : ℝ)
    (hc : 0 < c) (he : 0 ≤ e) (hg : 0 ≤ g) (hr : 0 ≤ r)
    (hGreen : g ^ 2 ≤ r * e)
    (hPoincare : e ≤ c * g) :
    e ≤ c ^ 2 * r := by
  have hgrad := gradiente_controlado c e g r hc he hg hr hGreen hPoincare
  have hmul : c * g ≤ c * (c * r) :=
    (mul_le_mul_iff_of_pos_left hc).mpr hgrad
  have hres : e ≤ c * (c * r) := le_trans hPoincare hmul
  nlinarith [hres]

/-- Forma al cuadrado de la cota H1 de Poisson:
    `||e||_L2^2 + ||grad e||_L2^2 <= (C_P^4 + C_P^2) * ||Delta e||_L2^2`.
    El lado izquierdo se convertirá en la norma H1 tras definir Sobolev. -/
theorem energia_cuadratica_controlada
    (c e g r : ℝ)
    (hc : 0 < c) (he : 0 ≤ e) (hg : 0 ≤ g) (hr : 0 ≤ r)
    (hGreen : g ^ 2 ≤ r * e)
    (hPoincare : e ≤ c * g) :
    e ^ 2 + g ^ 2 ≤ (c ^ 4 + c ^ 2) * r ^ 2 := by
  have hgrad := gradiente_controlado c e g r hc he hg hr hGreen hPoincare
  have hl2 := error_l2_controlado c e g r hc he hg hr hGreen hPoincare
  have hc2 : 0 ≤ c ^ 2 * r := mul_nonneg (sq_nonneg c) hr
  have hcr : 0 ≤ c * r := mul_nonneg hc.le hr
  have heSq : e ^ 2 ≤ (c ^ 2 * r) ^ 2 := by
    have hprod : 0 ≤ (c ^ 2 * r - e) * (c ^ 2 * r + e) :=
      mul_nonneg (sub_nonneg.mpr hl2) (add_nonneg hc2 he)
    nlinarith [hprod]
  have hgSq : g ^ 2 ≤ (c * r) ^ 2 := by
    have hprod : 0 ≤ (c * r - g) * (c * r + g) :=
      mul_nonneg (sub_nonneg.mpr hgrad) (add_nonneg hcr hg)
    nlinarith [hprod]
  calc
    e ^ 2 + g ^ 2 ≤ (c ^ 2 * r) ^ 2 + (c * r) ^ 2 := add_le_add heSq hgSq
    _ = (c ^ 4 + c ^ 2) * r ^ 2 := by ring

/-! La identidad débil se escribe con el signo de Δe de la tesis. -/

/-- Cauchy-Schwarz convierte la formulación débil de Green en la cota usada
    por el núcleo algebraico. `e` y `r` son clases L² escalares y `g` es
    un campo gradiente L² en una aplicación posterior. -/
theorem green_cauchy_schwarz
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (e r : E) (g : G)
    (hWeak : inner ℝ g g = -(inner ℝ r e)) :
    ‖g‖ ^ 2 ≤ ‖r‖ * ‖e‖ := by
  calc
    ‖g‖ ^ 2 = inner ℝ g g := (real_inner_self_eq_norm_sq g).symm
    _ = -(inner ℝ r e) := hWeak
    _ ≤ |inner ℝ r e| := by simpa only [abs_neg] using (le_abs_self (-(inner ℝ r e)))
    _ ≤ ‖r‖ * ‖e‖ := abs_real_inner_le_norm r e

/-- Cota energética cuadrática desde Green débil y Poincaré. La pertenencia
    efectiva a H₀¹ y la ecuación distribucional aún deben suministrar estas
    dos premisas para obtener el Lema 3.19 de la tesis. -/
theorem energia_cuadratica_debil
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (c : ℝ) (e r : E) (g : G) (hc : 0 < c)
    (hWeak : inner ℝ g g = -(inner ℝ r e))
    (hPoincare : ‖e‖ ≤ c * ‖g‖) :
    ‖e‖ ^ 2 + ‖g‖ ^ 2 ≤ (c ^ 4 + c ^ 2) * ‖r‖ ^ 2 := by
  exact energia_cuadratica_controlada c ‖e‖ ‖g‖ ‖r‖ hc
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (green_cauchy_schwarz e r g hWeak) hPoincare

/-- Forma no cuadrática para la norma hilbertiana del par `(e, g)`, cuya
    igualdad con la norma Sobolev H¹ requiere que `g` sea el gradiente débil
    de `e`. -/
theorem energia_norma_par_debil
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (c : ℝ) (e r : E) (g : G) (hc : 0 < c)
    (hWeak : inner ℝ g g = -(inner ℝ r e))
    (hPoincare : ‖e‖ ≤ c * ‖g‖) :
    ‖WithLp.toLp 2 (e, g)‖ ≤ c * Real.sqrt (1 + c ^ 2) * ‖r‖ := by
  have harg : 0 ≤ 1 + c ^ 2 := by nlinarith [sq_nonneg c]
  have hcoeff : (c * Real.sqrt (1 + c ^ 2)) ^ 2 = c ^ 4 + c ^ 2 := by
    rw [mul_pow, Real.sq_sqrt harg]
    ring
  have hsq : ‖WithLp.toLp 2 (e, g)‖ ^ 2 ≤
      (c ^ 4 + c ^ 2) * ‖r‖ ^ 2 := by
    calc
      ‖WithLp.toLp 2 (e, g)‖ ^ 2 = ‖e‖ ^ 2 + ‖g‖ ^ 2 :=
        WithLp.prod_norm_sq_eq_of_L2 _
      _ ≤ (c ^ 4 + c ^ 2) * ‖r‖ ^ 2 :=
        energia_cuadratica_debil c e r g hc hWeak hPoincare
  have hbound : ‖WithLp.toLp 2 (e, g)‖ ^ 2 ≤
      (c * Real.sqrt (1 + c ^ 2) * ‖r‖) ^ 2 := by
    calc
      ‖WithLp.toLp 2 (e, g)‖ ^ 2 ≤ (c ^ 4 + c ^ 2) * ‖r‖ ^ 2 := hsq
      _ = (c * Real.sqrt (1 + c ^ 2) * ‖r‖) ^ 2 := by
        rw [mul_pow, hcoeff]
  have hrhs : 0 ≤ c * Real.sqrt (1 + c ^ 2) * ‖r‖ :=
    mul_nonneg (mul_nonneg hc.le (Real.sqrt_nonneg _)) (norm_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) hrhs).mp hbound

#print axioms TesisPINN.energia_norma_par_debil
#print axioms TesisPINN.green_cauchy_schwarz
#print axioms TesisPINN.energia_cuadratica_debil
#print axioms TesisPINN.gradiente_controlado
#print axioms TesisPINN.error_l2_controlado
#print axioms TesisPINN.energia_cuadratica_controlada

end TesisPINN
