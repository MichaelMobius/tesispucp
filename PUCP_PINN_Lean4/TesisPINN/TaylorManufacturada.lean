import TesisPINN.HermiteRegularidad
import Mathlib.Analysis.Complex.TaylorSeries

/-! Desarrollo de Taylor de la prolongación entera y cota (3.92). -/

noncomputable section

namespace TesisPINN

open Polynomial Set Filter
open scoped Polynomial Topology

def coefTaylorManufacturada (j : ℕ) : ℝ :=
  iteratedDeriv j aManufacturada 0 / j.factorial

def taylorManufacturada (N : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (N + 1), monomial j (coefTaylorManufacturada j)

theorem taylorManufacturada_coef (N k : ℕ) :
    (taylorManufacturada N).coeff k =
      if k ≤ N then coefTaylorManufacturada k else 0 := by
  rw [taylorManufacturada, finsetSum_coeff]
  simp [coeff_monomial, Finset.sum_ite_eq', Nat.lt_succ_iff]


theorem taylorManufacturada_grado (N : ℕ) : (taylorManufacturada N).natDegree ≤ N := by
  unfold taylorManufacturada
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

private def coefTaylorComplejo (j : ℕ) : ℂ :=
  iteratedDeriv j aManufacturadaCompleja 0 / j.factorial

private theorem aManufacturadaCompleja_suave : ContDiff ℂ ⊤ aManufacturadaCompleja :=
  contDiff_iff_contDiffAt.mpr fun z => (aManufacturadaCompleja_entera z).contDiffAt

theorem coefTaylorManufacturada_complejo (j : ℕ) :
    (coefTaylorManufacturada j : ℂ) =
      iteratedDeriv j aManufacturadaCompleja 0 / (j.factorial : ℂ) := by
  have h := iteratedDeriv_eje_real _ _ aManufacturadaCompleja_suave
    (aManufacturada_suave _) aManufacturada_extension j 0
  simp only [Complex.ofReal_zero] at h
  rw [h]
  simp [coefTaylorManufacturada]

private def taylorComplejo (N : ℕ) : ℂ[X] :=
  (taylorManufacturada N).map Complex.ofRealHom

private theorem taylorComplejo_eval (N : ℕ) (z : ℂ) :
    (taylorComplejo N).eval z = ∑ j ∈ Finset.range (N + 1), coefTaylorComplejo j * z ^ j := by
  unfold taylorComplejo taylorManufacturada
  rw [Polynomial.map_sum, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  simp [coefTaylorComplejo, coefTaylorManufacturada_complejo]

private theorem coefTaylorComplejo_cota :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ, ‖coefTaylorComplejo j‖ ≤ M / 2 ^ j := by
  have hc := aManufacturadaCompleja_suave.continuous
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) 2).exists_bound_of_continuousOn hc.continuousOn
  let M := max B 0
  refine ⟨M, le_max_right _ _, fun j => ?_⟩
  have he := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (by norm_num : (0 : ℝ) < 2)
    (aManufacturadaCompleja_suave.differentiable (by simp)).differentiableOn.diffContOnCl
    (fun z hz => (hB z hz).trans (le_max_left B 0))
  unfold coefTaylorComplejo
  rw [norm_div, Complex.norm_natCast]
  have hj : 0 < (j.factorial : ℝ) := by positivity
  apply (div_le_iff₀ hj).mpr
  exact he.trans_eq (by ring)

private theorem taylorComplejo_cola (M : ℝ) (hM : 0 ≤ M)
    (hcoef : ∀ j : ℕ, ‖coefTaylorComplejo j‖ ≤ M / 2 ^ j)
    (N : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 3 / 2) :
    ‖aManufacturadaCompleja z - (taylorComplejo N).eval z‖ ≤
      4 * M * (‖z‖ / 2) ^ (N + 1) := by
  let q := ‖z‖ / 2
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq : q < 1 := by dsimp [q]; linarith
  let f (j : ℕ) := coefTaylorComplejo j * z ^ j
  have hs : HasSum f (aManufacturadaCompleja z) := by
    have he := Complex.hasSum_taylorSeries_of_entire
      (aManufacturadaCompleja_suave.differentiable (by simp)) 0 z
    convert he using 1
    funext j
    simp only [f, coefTaylorComplejo, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  have he : aManufacturadaCompleja z - (taylorComplejo N).eval z = ∑' k, f (k + (N + 1)) := by
    rw [← hs.tsum_eq, taylorComplejo_eval, ← hs.summable.sum_add_tsum_nat_add (N + 1)]
    change (∑ j ∈ Finset.range (N + 1), f j) + _ - (∑ j ∈ Finset.range (N + 1), f j) = _
    ring
  have hmajor (k : ℕ) : ‖f (k + (N + 1))‖ ≤ (M * q ^ (N + 1)) * q ^ k := by
    rw [show ‖f (k + (N + 1))‖ = ‖coefTaylorComplejo (k + (N + 1))‖ *
        ‖z‖ ^ (k + (N + 1)) by simp [f, norm_mul, norm_pow]]
    calc
      _ ≤ (M / 2 ^ (k + (N + 1))) * ‖z‖ ^ (k + (N + 1)) :=
        mul_le_mul_of_nonneg_right (hcoef _) (by positivity)
      _ = M * q ^ (k + (N + 1)) := by dsimp [q]; rw [div_pow]; ring
      _ = (M * q ^ (N + 1)) * q ^ k := by rw [pow_add]; ring
  have hg := (hasSum_geometric_of_lt_one hq0 hq).mul_left (M * q ^ (N + 1))
  have habs : Summable (fun k => ‖f (k + (N + 1))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hmajor hg.summable
  have hq4 : (1 - q)⁻¹ ≤ 4 := by
    rw [← one_div]
    apply (div_le_iff₀ (sub_pos.mpr hq)).2
    dsimp [q]
    linarith
  rw [he]
  calc
    _ ≤ ∑' k, ‖f (k + (N + 1))‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' k, (M * q ^ (N + 1)) * q ^ k := habs.tsum_le_tsum hmajor hg.summable
    _ = _ := hg.tsum_eq
    _ ≤ _ := (mul_le_mul_of_nonneg_left hq4 (mul_nonneg hM (pow_nonneg hq0 _))).trans_eq (by ring)

theorem potencia_uno_mas_inverso (N : ℕ) :
    (1 + 1 / ((N : ℝ) + 2)) ^ (N + 1) ≤ Real.exp 1 := by
  have hN : 0 < (N : ℝ) + 2 := by positivity
  have hdiv : (↑(N + 1) : ℝ) * (1 / ((N : ℝ) + 2)) ≤ 1 := by
    rw [mul_one_div]
    apply (div_le_one hN).mpr
    push_cast
    linarith
  calc
    _ ≤ (Real.exp (1 / ((N : ℝ) + 2))) ^ (N + 1) :=
      pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp (1 / ((N : ℝ) + 2))) _
    _ = Real.exp ((↑(N + 1) : ℝ) * (1 / ((N : ℝ) + 2))) := by rw [Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr hdiv

/-- Cauchy en una circunferencia de radio `1 / (N + 2)` para órdenes hasta tres. -/
theorem cota_cauchy_radio_grado (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (N k : ℕ) (hk : k ≤ 3) (t : ℂ) (B : ℝ) (hB0 : 0 ≤ B)
    (hb : ∀ z ∈ Metric.sphere t (1 / ((N : ℝ) + 2)), ‖F z‖ ≤ B) :
    ‖iteratedDeriv k F t‖ ≤ 48 * B * ((N : ℝ) + 1) ^ 3 := by
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (show 0 < (1 : ℝ) / ((N : ℝ) + 2) by positivity)
    hF.differentiableOn.diffContOnCl hb
  have hkfac : (k.factorial : ℝ) ≤ 6 := by interval_cases k <;> norm_num [Nat.factorial]
  have hp : ((N : ℝ) + 2) ^ k ≤ (2 * ((N : ℝ) + 1)) ^ 3 := by
    exact (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N] :
      (1 : ℝ) ≤ (N : ℝ) + 2) hk).trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
  rw [one_div, inv_pow, div_inv_eq_mul] at hC
  refine hC.trans ?_
  calc
    _ = B * ((k.factorial : ℝ) * ((N : ℝ) + 2) ^ k) := by ring
    _ ≤ B * (6 * (2 * ((N : ℝ) + 1)) ^ 3) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hkfac hp (by positivity) (by norm_num)) hB0
    _ = _ := by ring


/-- Cota (3.92) para todos los truncamientos, incluidos los índices iniciales. -/
theorem resto_taylorManufacturada_c3 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N k : ℕ, k ≤ 3 → ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv k (aManufacturada - (taylorManufacturada N).eval) t‖ ≤
        C * ((N : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ N := by
  obtain ⟨M, hM, hcoef⟩ := coefTaylorComplejo_cota
  refine ⟨192 * M * Real.exp 1, by positivity, fun N k hk t ht => ?_⟩
  let F := aManufacturadaCompleja - (taylorComplejo N).eval
  let δ := 1 / ((N : ℝ) + 2)
  let B := 4 * M * Real.exp 1 * (1 / 2 : ℝ) ^ N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    dsimp [δ]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hF : ContDiff ℂ ⊤ F :=
    aManufacturadaCompleja_suave.sub (eval_polynomial_contDiff _ _)
  have hB (z : ℂ) (hz : z ∈ Metric.sphere (t : ℂ) δ) : ‖F z‖ ≤ B := by
    have hzt : ‖z - (t : ℂ)‖ = δ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have ht' : ‖(t : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, Real.norm_eq_abs] using abs_le.mpr ht
    have hzn : ‖z‖ ≤ 1 + δ := by linarith [norm_sub_norm_le z (t : ℂ)]
    have hsmall : ‖z‖ ≤ 3 / 2 := by linarith
    have h2 : (‖z‖ / 2) ^ (N + 1) ≤ Real.exp 1 * (1 / 2 : ℝ) ^ N := by
      calc
        _ ≤ ((1 + δ) / 2) ^ (N + 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = (1 + δ) ^ (N + 1) * (1 / 2 : ℝ) ^ (N + 1) := by rw [div_eq_mul_inv, mul_pow, one_div]
        _ ≤ Real.exp 1 * (1 / 2 : ℝ) ^ (N + 1) :=
          mul_le_mul_of_nonneg_right (potencia_uno_mas_inverso N) (by positivity)
        _ ≤ _ := by rw [pow_succ]; nlinarith [mul_nonneg (Real.exp_pos 1).le (show 0 ≤ (1 / 2 : ℝ) ^ N by positivity)]
    exact (taylorComplejo_cola M hM hcoef N z hsmall).trans
      ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans_eq (by dsimp [B]; ring))
  have hCauchy := cota_cauchy_radio_grado F (hF.differentiable (by simp)) N k hk (t : ℂ) B
    (by dsimp [B]; positivity) hB
  have he (x : ℝ) : F x = ((aManufacturada - (taylorManufacturada N).eval) x : ℝ) := by
    change aManufacturadaCompleja x - (taylorComplejo N).eval (x : ℂ) =
      ((aManufacturada x - (taylorManufacturada N).eval x : ℝ) : ℂ)
    rw [Complex.ofReal_sub, aManufacturada_extension]
    congr 1
    exact eval_map_apply Complex.ofRealHom x
  rw [iteratedDeriv_eje_real F _ hF
      ((aManufacturada_suave _).sub (eval_polynomial_contDiff _ _)) he, Complex.norm_real] at hCauchy
  exact hCauchy.trans_eq (by dsimp [B]; ring)

#check resto_taylorManufacturada_c3
#print axioms taylorManufacturada_grado
#print axioms coefTaylorManufacturada_complejo
#print axioms resto_taylorManufacturada_c3

end TesisPINN

