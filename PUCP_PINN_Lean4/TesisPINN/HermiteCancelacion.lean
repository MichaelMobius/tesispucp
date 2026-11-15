import TesisPINN.HermiteRestoComplejo
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Cancelación del interpolante polinómico en la fórmula de Hermite. -/

noncomputable section

namespace TesisPINN

open Polynomial Filter
open scoped Polynomial Topology

private theorem norma_eval_grado {p : ℂ[X]} {d : ℕ} (hd : p.natDegree ≤ d)
    {w : ℂ} {R : ℝ} (hR : 1 ≤ R) (hw : ‖w‖ = R) :
    ‖p.eval w‖ ≤ (∑ j ∈ Finset.range (d + 1), ‖p.coeff j‖) * R ^ d := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [norm_mul, norm_pow, hw]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hR (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (norm_nonneg _)

private theorem productoNodosHermite_radio {n : ℕ} (t : Fin n → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1) {w : ℂ} {R : ℝ}
    (hR : 2 ≤ R) (hw : ‖w‖ = R) :
    (R / 2) ^ (4 * n) ≤ ‖productoNodosHermite t w‖ := by
  simp only [productoNodosHermite, norm_prod, norm_pow, pow_mul]
  calc
    _ = ∏ _ : Fin n, (R / 2) ^ (4 : ℕ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => by
      apply pow_le_pow_left₀ (by positivity)
      have h := norm_sub_norm_le w (t j : ℂ)
      rw [hw, Complex.norm_real, Real.norm_eq_abs] at h
      linarith [abs_le.mpr (ht j)])

private theorem denominador_ne {n : ℕ} (t : Fin n → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1)
    {z w : ℂ} (hz : ‖z‖ < 4) (hw : 4 ≤ ‖w‖) :
    productoNodosHermite t w * (w - z) ≠ 0 := by
  apply mul_ne_zero
  · have h := productoNodosHermite_radio t ht (show 2 ≤ ‖w‖ by linarith) rfl
    intro he
    rw [he, norm_zero] at h
    exact (not_le_of_gt (show 0 < (‖w‖ / 2) ^ (4 * n) by positivity)) h
  · intro he
    have h := sub_eq_zero.mp he
    rw [h] at hw
    exact hz.not_ge hw

theorem restoContornoHermite_polinomio_cero {n : ℕ} (t : Fin n → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1) (p : ℂ[X]) (hp : p.degree < 4 * n)
    {z : ℂ} (hz : ‖z‖ < 4) :
    restoContornoHermite t p.eval z = 0 := by
  by_cases hp0 : p = 0
  · subst p
    simp [restoContornoHermite, circleIntegral]
  let d := 4 * n - 1
  have hn : p.natDegree < 4 * n := (natDegree_lt_iff_degree_lt hp0).mpr hp
  have hd : p.natDegree ≤ d := by
    omega
  have hd' : d + 2 = 4 * n + 1 := by dsimp [d] at *; omega
  let C := ∑ j ∈ Finset.range (d + 1), ‖p.coeff j‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let f : ℂ → ℂ := fun w => p.eval w * productoNodosHermite t z /
    (productoNodosHermite t w * (w - z))
  have hc (w : ℂ) (hw : 4 ≤ ‖w‖) : DifferentiableAt ℂ f w := by
    have hp' : DifferentiableAt ℂ p.eval w := (p.hasDerivAt w).differentiableAt
    have hQ : DifferentiableAt ℂ (productoNodosHermite t) w := by
      unfold productoNodosHermite
      exact DifferentiableAt.fun_finsetProd (fun j _ => by fun_prop)
    exact (hp'.mul_const _).div (hQ.mul (by fun_prop)) (denominador_ne t ht hz hw)
  have hR (R : ℝ) (hR : 8 ≤ R) :
      circleIntegral f 0 R = circleIntegral f 0 4 := by
    apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (by norm_num) (by linarith) Set.countable_empty
    · intro w hw
      have hw' : 4 ≤ ‖w‖ := by simpa [Metric.mem_ball, dist_zero_right, not_lt] using hw.2
      exact (hc w hw').continuousAt.continuousWithinAt
    · intro w hw
      have hw' : 4 < ‖w‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hw.1.2
      exact hc w hw'.le
  let K := C * ‖productoNodosHermite t z‖ * (2 : ℝ) ^ (4 * n + 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbound (R : ℝ) (hR8 : 8 ≤ R) :
      ‖circleIntegral f 0 4‖ ≤ (2 * Real.pi * K) / R := by
    have hr : 0 < R := by linarith
    rw [← hR R hR8]
    refine (circleIntegral.norm_integral_le_of_norm_le_const hr.le (C := K / R ^ 2) ?_).trans ?_
    · intro w hw
      have hw' : ‖w‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hw
      have hden : R / 2 ≤ ‖w - z‖ := by linarith [norm_sub_norm_le w z]
      have hden' := mul_le_mul (productoNodosHermite_radio t ht (by linarith) hw') hden
        (by positivity) (norm_nonneg _)
      have hnum := mul_le_mul_of_nonneg_right (norma_eval_grado hd (by linarith) hw')
        (norm_nonneg (productoNodosHermite t z))
      change ‖p.eval w * productoNodosHermite t z /
        (productoNodosHermite t w * (w - z))‖ ≤ _
      rw [norm_div, norm_mul, norm_mul]
      refine (div_le_div₀ (by positivity) hnum (by positivity) hden').trans ?_
      change C * R ^ d * ‖productoNodosHermite t z‖ / ((R / 2) ^ (4 * n) * (R / 2)) ≤ K / R ^ 2
      have hEq : (R / 2) ^ (4 * n) * (R / 2) = R ^ d * R ^ 2 / 2 ^ (4 * n + 1) := by
        rw [← pow_succ, div_pow, ← pow_add]
        rw [hd']
      rw [hEq]
      dsimp [K]
      have hPow : 0 < R ^ d := pow_pos hr _
      have hTwo : 0 < (2 : ℝ) ^ (4 * n + 1) := by positivity
      apply le_of_eq
      field_simp <;> ring
    · apply le_of_eq
      field_simp <;> ring
  have hi : circleIntegral f 0 4 = 0 := by
    by_contra hn
    have hnorm : 0 < ‖circleIntegral f 0 4‖ := norm_pos_iff.mpr hn
    let R := max 8 ((2 * Real.pi * K) / ‖circleIntegral f 0 4‖ + 1)
    have h8 : 8 ≤ R := le_max_left _ _
    have hr : 0 < R := by linarith
    have hLt : (2 * Real.pi * K) / ‖circleIntegral f 0 4‖ < R :=
      (lt_add_one _).trans_le (le_max_right _ _)
    have hContr := (div_lt_iff₀ hnorm).mp hLt
    have hb := (le_div_iff₀ hr).mp (hbound R h8)
    linarith [mul_comm R ‖circleIntegral f 0 4‖]
  unfold restoContornoHermite
  change _ * circleIntegral f 0 4 = 0
  rw [hi, mul_zero]

private theorem eval_analitica_hermite (p : ℂ[X]) (z : ℂ) : AnalyticAt ℂ p.eval z := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h : (p + q).eval = p.eval + q.eval := funext (fun _ => eval_add)
    rw [h]
    exact hp.add hq
  | monomial n a =>
    rw [show (monomial n a).eval = fun w => a * w ^ n from funext (fun _ => eval_monomial)]
    fun_prop

/-- Fórmula (3.89), con el numerador original y sin contribución polinómica. -/
theorem restoContornoHermite_formula {n : ℕ} (t : Fin n → ℝ)
    (ht : Function.Injective t) (hI : ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1)
    (a : ℂ → ℂ) (ha : ∀ z, AnalyticAt ℂ a z)
    (p : ℂ[X]) (hp : p.degree < 4 * n)
    (hjet : ∀ j k, k < 4 → iteratedDeriv k (a - p.eval) (t j : ℂ) = 0)
    {z : ℂ} (hz : ‖z‖ < 4) :
    restoContornoHermite t a z = a z - p.eval z := by
  have h := restoContornoHermite_diferencia t ht hI a p.eval ha (eval_analitica_hermite p) hjet hz
  have h0 := restoContornoHermite_polinomio_cero t hI p hp hz
  let A (w : ℂ) := a w * productoNodosHermite t z / (productoNodosHermite t w * (w - z))
  let B (w : ℂ) := p.eval w * productoNodosHermite t z / (productoNodosHermite t w * (w - z))
  have hint (b : ℂ → ℂ) (hb : Continuous b) :
      CircleIntegrable (fun w => b w * productoNodosHermite t z /
        (productoNodosHermite t w * (w - z))) 0 4 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    refine (hb.mul continuous_const).continuousOn.div (by unfold productoNodosHermite; fun_prop) ?_
    intro w hw
    have he : ‖w‖ = 4 := by simpa [Metric.mem_sphere, dist_zero_right] using hw
    exact denominador_ne t hI hz he.ge
  have he : restoContornoHermite t (a - p.eval) z =
      restoContornoHermite t a z - restoContornoHermite t p.eval z := by
    have hf : (fun w => (a - p.eval) w * productoNodosHermite t z /
        (productoNodosHermite t w * (w - z))) = fun w => A w - B w := by
      funext w
      simp [A, B, sub_mul, sub_div]
    unfold restoContornoHermite
    rw [hf, circleIntegral.integral_sub (hint a (continuous_iff_continuousAt.mpr
      fun w => (ha w).continuousAt)) (hint p.eval (continuous_iff_continuousAt.mpr
      fun w => (eval_analitica_hermite p w).continuousAt)), mul_sub]
  rwa [he, h0, sub_zero] at h

#check restoContornoHermite_formula
#print axioms restoContornoHermite_polinomio_cero
#print axioms restoContornoHermite_formula

end TesisPINN
