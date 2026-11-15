import TesisPINN.Teorema38

/-! Desigualdad global de interpolación Hölder–L², ecuación (3.34). -/

noncomputable section

namespace TesisPINN

open MeasureTheory Filter Asymptotics Set
open scoped Topology

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ] (U : Set X) (hU : MeasurableSet U)
variable (H α κ s R : ℝ) (hH : 0 ≤ H) (hα : 0 < α) (hκ : 0 < κ) (hR : 0 < R)
variable (hmass : ∀ x ∈ U, ∀ r : ℝ, 0 < r → r ≤ R →
  κ * r ^ s ≤ μ.real (Metric.ball x r ∩ U))

include hU hH hα hκ hR hmass

/-- Energía cero implica anulación puntual en el soporte por la masa local. -/
theorem lema39_eq_zero
    (v : X → ℝ) (hv : Integrable (fun x => v x ^ 2) μ)
    (hHol : ∀ x ∈ U, ∀ y ∈ U, |v x - v y| ≤ H * dist x y ^ α)
    (hzero : (∫ x, v x ^ 2 ∂μ) = 0) : EqOn v 0 U := by
  intro x hx
  let r (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 : ℝ))
  have hlim : Tendsto r atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp tendsto_natCast_atTop_atTop
  have hrad : ∀ᶠ n in atTop, r n ≤ R :=
    (hlim.eventually (Iio_mem_nhds hR)).mono fun _ hn => le_of_lt hn
  have hle : ∀ᶠ n in atTop, |v x| ≤ H * r n ^ α := by
    filter_upwards [hrad, eventually_ge_atTop (1 : ℕ)] with n hn hn'
    have hr : 0 < r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
    have hb := abs_le_holder_add_de_integral μ U hU v hv H α (r n)
      (κ * r n ^ s) 0 hH hα le_rfl x hx (by positivity) (hmass x hx _ hr hn) hHol
      (by rw [hzero]; simp)
    simpa only [add_zero] using hb
  have hlim' : Tendsto (fun n => H * r n ^ α) atTop (𝓝 0) := by
    simpa [Real.zero_rpow hα.ne'] using
      ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp hlim).const_mul H
  exact abs_eq_zero.mp (le_antisymm (ge_of_tendsto hlim' hle) (abs_nonneg _))

def constanteLema39 (H κ s R : ℝ) : ℝ :=
  H + (Real.sqrt κ)⁻¹ + (Real.sqrt (κ * R ^ s))⁻¹

/-- La constante de (3.34) depende solo de la cota Hölder y de la geometría
de masa. Se obtiene el supremo puntual, con energía cero incluida. -/
theorem lema39_global
    (hs : 0 < s) (v : X → ℝ) (hv : Integrable (fun x => v x ^ 2) μ)
    (hHol : ∀ x ∈ U, ∀ y ∈ U, |v x - v y| ≤ H * dist x y ^ α) :
    let Q := Real.sqrt (∫ x, v x ^ 2 ∂μ)
    supResiduo U v ≤ constanteLema39 H κ s R * (Q + Q ^ (2 * α / (2 * α + s))) := by
  intro Q
  let p := 2 * α / (2 * α + s)
  let q := 2 / (2 * α + s)
  let C := constanteLema39 H κ s R
  have hE : 0 ≤ ∫ x, v x ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hQsq : Q ^ 2 = ∫ x, v x ^ 2 ∂μ := Real.sq_sqrt hE
  have hC : 0 ≤ C := by unfold C constanteLema39; positivity
  have hp : 0 < p := by dsimp [p]; positivity
  change supResiduo U v ≤ C * (Q + Q ^ p)
  by_cases hzero : Q = 0
  · have hz : (∫ x, v x ^ 2 ∂μ) = 0 := by rw [← hQsq, hzero]; simp
    have hpoint := lema39_eq_zero μ U hU H α κ s R hH hα hκ hR hmass v hv hHol hz
    apply (supResiduo_le U v _ (by positivity) ?_).2
    intro x hx
    rw [hpoint hx]
    change |(0 : ℝ)| ≤ _
    rw [abs_zero]
    exact mul_nonneg hC (add_nonneg hQ (Real.rpow_nonneg hQ _))
  have hQpos := lt_of_le_of_ne hQ (Ne.symm hzero)
  let r := Q ^ q
  have hr : 0 < r := Real.rpow_pos_of_pos hQpos _
  have hpow : r ^ α = Q ^ p := by
    dsimp [r]
    rw [← Real.rpow_mul hQ]
    congr 1
    dsimp [p, q]
    ring
  have hb := supResiduo_le_radio_truncado μ U hU v hv H α κ s R r (Q ^ 2) hH hα hκ
    hR hr (sq_nonneg _) hmass hHol hQsq.ge
  by_cases hsmall : r ≤ R
  · rw [min_eq_left hsmall, hpow, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hQ,
      Real.sqrt_mul hκ.le, Real.sqrt_eq_rpow (r ^ s)] at hb
    have hqexp : 1 - (q * s * (1 / 2)) = p := by
      dsimp [p, q]
      field_simp
      <;> ring
    have hquot : Q / (Real.sqrt κ * (r ^ s) ^ (1 / 2 : ℝ)) =
        (Real.sqrt κ)⁻¹ * Q ^ p := by
      rw [show (r ^ s) ^ (1 / 2 : ℝ) = Q ^ (q * s * (1 / 2)) by
        dsimp [r]
        rw [← Real.rpow_mul hQ, ← Real.rpow_mul hQ]]
      calc
        _ = (Real.sqrt κ)⁻¹ * (Q / Q ^ (q * s * (1 / 2))) := by ring
        _ = _ := by
          congr 1
          conv_lhs => arg 1; rw [← Real.rpow_one Q]
          rw [← Real.rpow_sub hQpos, hqexp]
    rw [hquot, ← add_mul] at hb
    apply hb.trans
    have hi := mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (κ * R ^ s))) (Real.rpow_nonneg hQ p)
    have hCQ := mul_nonneg hC hQ
    dsimp [C, constanteLema39] at hCQ ⊢
    nlinarith
  · have hlarge : R ≤ r := le_of_not_ge hsmall
    rw [min_eq_right hlarge, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hQ, div_eq_mul_inv] at hb
    have hRpow : R ^ α ≤ Q ^ p := (Real.rpow_le_rpow hR.le hlarge hα.le).trans_eq hpow
    refine hb.trans ((add_le_add_left (mul_le_mul_of_nonneg_left hRpow hH) _).trans ?_)
    dsimp [C, constanteLema39]
    nlinarith [mul_nonneg hH hQ,
      mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg κ)) hQ,
      mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg κ)) (Real.rpow_nonneg hQ p),
      mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (κ * R ^ s))) (Real.rpow_nonneg hQ p)]

/-- Versión para funciones acotadas, como en la tesis. La concentración y
la continuidad Hölder proporcionan la integrabilidad cuadrática. -/
theorem lema39_global_acotado
    (hs : 0 < s) (hμ : μ Uᶜ = 0) (v : X → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hbounded : ∀ x ∈ U, |v x| ≤ M)
    (hHol : ∀ x ∈ U, ∀ y ∈ U, |v x - v y| ≤ H * dist x y ^ α) :
    let Q := Real.sqrt (∫ x, v x ^ 2 ∂μ)
    supResiduo U v ≤ constanteLema39 H κ s R * (Q + Q ^ (2 * α / (2 * α + s))) := by
  have hcont : ContinuousOn v U := continuo_de_cota_holder U v H α hα hHol
  have hmeas := aestronglyMeasurable_residuo_sq_de_continuidad μ U hU hμ v (fun _ => 0)
    hcont continuousOn_const
  have hInt : Integrable (fun x => v x ^ 2) μ := by
    apply (integrable_const (M ^ 2)).mono' (by simpa using hmeas)
    filter_upwards [mem_ae_iff.mpr hμ] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs (v x)]
    exact (sq_le_sq₀ (abs_nonneg _) hM).mpr (hbounded x hx)
  exact lema39_global μ U hU H α κ s R hH hα hκ hR hmass hs v hInt hHol

/-- Tasas de T3.8 con el exponente de masa como parámetro. -/
theorem lema39_tasa (hs : 0 < s) (β : ℝ) (hβ : 0 < β)
    (v : ℕ → X → ℝ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hv : ∀ᶠ n in atTop, Integrable (fun x => v n x ^ 2) μ ∧
      ∀ x ∈ U, ∀ y ∈ U, |v n x - v n y| ≤ H * dist x y ^ α)
    (hE : (fun n => ∫ x, v n x ^ 2 ∂μ) =O[atTop] fun n => (m n : ℝ) ^ (-β)) :
    (fun n => supResiduo U (v n)) =O[atTop] fun n => (m n : ℝ) ^ (-(α * β / (2 * α + s))) := by
  let Q (n : ℕ) := Real.sqrt (∫ x, v n x ^ 2 ∂μ)
  let p := 2 * α / (2 * α + s)
  let b (n : ℕ) := (m n : ℝ) ^ (-β / 2)
  have hp : 0 < p := by dsimp [p]; positivity
  have hp₁ : p ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hb (n : ℕ) : 0 ≤ b n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hQ : Q =O[atTop] b := by
    convert hE.sqrt (Eventually.of_forall (fun n => Real.rpow_nonneg (Nat.cast_nonneg (m n)) _)) using 1
    ext n
    simp only [b, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg (m n))]
    congr 1
    ring
  have hQp := hQ.rpow hp.le (Eventually.of_forall hb)
  have hbO : b =O[atTop] (fun n => b n ^ p) := by
    apply isBigO_de_cota_eventual _ _ 1
    filter_upwards [hm.eventually (eventually_ge_atTop (1 : ℕ))] with n hn
    have hmn : 1 ≤ (m n : ℝ) := by exact_mod_cast hn
    have hbn : b n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hmn (by linarith)
    refine ⟨hb n, Real.rpow_nonneg (hb n) p, ?_⟩
    rw [one_mul]
    calc
      b n = b n ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge
        (Real.rpow_pos_of_pos (by linarith : 0 < (m n : ℝ)) _) hbn hp₁
  have hsum := ((hQ.trans hbO).add hQp).const_mul_left (constanteLema39 H κ s R)
  have hdom : (fun n => supResiduo U (v n)) =O[atTop]
      (fun n => constanteLema39 H κ s R * (Q n + Q n ^ p)) := by
    apply isBigO_de_cota_eventual _ _ 1
    filter_upwards [hv] with n hn
    have hbound := lema39_global μ U hU H α κ s R hH hα hκ hR hmass hs (v n) hn.1 hn.2
    have hC : 0 ≤ constanteLema39 H κ s R := by unfold constanteLema39; positivity
    have hnn : 0 ≤ Q n + Q n ^ p := add_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    exact ⟨Real.sSup_nonneg' ⟨0, mem_insert _ _, le_rfl⟩,
      mul_nonneg hC hnn, by simpa using hbound⟩
  have hf : (fun n => b n ^ p) =
      (fun n => (m n : ℝ) ^ (-(α * β / (2 * α + s)))) := by
    funext n
    rw [show b n ^ p = (m n : ℝ) ^ ((-β / 2) * p) from
      (Real.rpow_mul (Nat.cast_nonneg _) _ _).symm]
    congr 1
    dsimp [p]
    ring
  rw [← hf]
  exact hdom.trans hsum

#check lema39_global
#check lema39_global_acotado
#check lema39_tasa
#print axioms lema39_eq_zero
#print axioms lema39_global
#print axioms lema39_global_acotado
#print axioms lema39_tasa

end TesisPINN
