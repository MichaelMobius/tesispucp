import TesisPINN.Lema319Dimensional
import TesisPINN.EstabilidadEliptica

/-!
# Transferencia por pérdida ponderada y por supremo
-/

noncomputable section

open MeasureTheory TopologicalSpace Topology Filter Asymptotics
open EllipticPdes EllipticPdes.H1Graph
open scoped ENNReal

namespace TesisPINN

/-- Densidad real medible y estrictamente positiva casi en todas partes. -/
structure DensidadInferiorEn {X : Type*} [MeasurableSpace X] (ν : Measure X) where
  rho : X → ℝ
  rho0 : ℝ
  rho0_pos : 0 < rho0
  measurable_rho : Measurable rho
  lower : ∀ᵐ x ∂ν, rho0 ≤ rho x

def DensidadInferiorEn.ley {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (D : DensidadInferiorEn ν) : Measure X :=
  ν.withDensity (fun x => ENNReal.ofReal (D.rho x))

private theorem norma_sq_integral_L2 {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (r : Lp ℝ 2 ν) : ‖r‖ ^ 2 = ∫ x, (r x) ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq r, MeasureTheory.L2.inner_def]
  congr 1
  funext x
  simp [Real.norm_eq_abs]

/-- Comparación cuadrática. El residuo puntual de la pérdida coincide
casi en todas partes con el representante usado por la energía. -/
theorem cota_densidad_dimensional {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (D : DensidadInferiorEn ν) (r : Lp ℝ 2 ν) (v : X → ℝ)
    (hv : (r : X → ℝ) =ᵐ[ν] v) (hi : Integrable (fun x => (v x) ^ 2) D.ley) :
    D.rho0 * ‖r‖ ^ 2 ≤ ∫ x, (v x) ^ 2 ∂D.ley := by
  have hd := D.measurable_rho.ennreal_ofReal
  have hfin : ∀ᵐ x ∂ν, ENNReal.ofReal (D.rho x) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have heq : (fun x => (ENNReal.ofReal (D.rho x)).toReal • (v x) ^ 2) =ᵐ[ν]
      (fun x => D.rho x * (r x) ^ 2) := by
    filter_upwards [D.lower, hv] with x hx hr
    simp [ENNReal.toReal_ofReal (D.rho0_pos.le.trans hx), hr, smul_eq_mul]
  have hw : Integrable (fun x => D.rho x * (r x) ^ 2) ν :=
    ((integrable_withDensity_iff_integrable_smul' hd hfin).mp hi).congr heq
  rw [DensidadInferiorEn.ley, integral_withDensity_eq_integral_toReal_smul hd hfin,
    integral_congr_ae heq, norma_sq_integral_L2, ← integral_const_mul]
  apply integral_mono_ae ((Lp.memLp r).integrable_sq.const_mul D.rho0) hw
  filter_upwards [D.lower] with x hx
  exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)

theorem cota_L2_de_perdida_dimensional {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (D : DensidadInferiorEn ν) (r : Lp ℝ 2 ν) (v : X → ℝ)
    (hv : (r : X → ℝ) =ᵐ[ν] v) (hi : Integrable (fun x => (v x) ^ 2) D.ley)
    (lr loss : ℝ) (hlr : 0 < lr)
    (hdom : lr * (∫ x, (v x) ^ 2 ∂D.ley) ≤ loss) :
    ‖r‖ ≤ Real.sqrt loss / Real.sqrt (D.rho0 * lr) := by
  have hp := mul_pos D.rho0_pos hlr
  have h := (mul_le_mul_of_nonneg_left (cota_densidad_dimensional D r v hv hi) hlr.le).trans hdom
  have hsq : (D.rho0 * lr) * ‖r‖ ^ 2 ≤ loss := by linarith
  have hnon : 0 ≤ loss := (mul_nonneg hp.le (sq_nonneg _)).trans hsq
  apply (le_div_iff₀ (Real.sqrt_pos.2 hp)).2
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).1
  rw [mul_pow, Real.sq_sqrt hp.le, Real.sq_sqrt hnon, mul_comm]
  exact hsq

/-- Comparación en norma entre `L²(ν)` y `L²(ν.withDensity ρ)`.
El miembro derecho es la raíz de la integral cuadrática finita. -/
theorem cota_L2_cambio_medida {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (D : DensidadInferiorEn ν) (r : Lp ℝ 2 ν) (v : X → ℝ)
    (hv : (r : X → ℝ) =ᵐ[ν] v) (hi : Integrable (fun x => (v x) ^ 2) D.ley) :
    ‖r‖ ≤ (Real.sqrt D.rho0)⁻¹ * Real.sqrt (∫ x, (v x) ^ 2 ∂D.ley) := by
  simpa [div_eq_inv_mul, mul_comm] using
    cota_L2_de_perdida_dimensional D r v hv hi 1 (∫ x, (v x) ^ 2 ∂D.ley)
      one_pos (by rw [one_mul])

theorem cota_L2_de_cota_ae {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsFiniteMeasure ν] (r : Lp ℝ 2 ν) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ᵐ x ∂ν, ‖r x‖ ≤ M) :
    ‖r‖ ≤ Real.sqrt (ν.real Set.univ) * M := by
  have htwo : ((2 : ℝ≥0∞).toReal)⁻¹ = (1 / 2 : ℝ) := by norm_num
  simpa only [htwo, ← Real.sqrt_eq_rpow, measureUnivNNReal, measureReal_def,
    ENNReal.coe_toNNReal_eq_toReal] using
    Lp.norm_le_of_ae_bound hM h

theorem cota_L2_de_supremo_esencial {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsFiniteMeasure ν] (r : Lp ℝ 2 ν) (hb : eLpNormEssSup r ν < ⊤) :
    ‖r‖ ≤ Real.sqrt (ν.real Set.univ) * (eLpNormEssSup r ν).toReal :=
  cota_L2_de_cota_ae r _ ENNReal.toReal_nonneg
    ((enorm_ae_le_eLpNormEssSup r ν).mono fun x hx =>
      by simpa using ENNReal.toReal_mono hb.ne hx)

theorem cota_L2_de_supremo_puntual {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (ν : Measure X) (U : Set X) (hU : MeasurableSet U) [IsFiniteMeasure (ν.restrict U)]
    (r : Lp ℝ 2 (ν.restrict U)) (v : X → ℝ)
    (hv : (r : X → ℝ) =ᵐ[ν.restrict U] v)
    (hb : ∃ M : ℝ, ∀ x ∈ U, |v x| ≤ M) :
    ‖r‖ ≤ Real.sqrt (ν.real U) * supResiduo U v := by
  have h := cota_L2_de_cota_ae r _ (supResiduo_nonneg_de_acotada hb)
    (by
      filter_upwards [hv, ae_restrict_mem hU] with x he hx
      simpa [he, Real.norm_eq_abs] using abs_le_supResiduo hx hb)
  simpa [measureReal_def, Measure.restrict_apply_univ] using h

/-- Multiplicar un mayorante asintótico por una constante fija. -/
theorem tasa_de_cota_no_negativa (e b a : ℕ → ℝ) (C : ℝ)
    (he : ∀ n, 0 ≤ e n) (hb : ∀ᶠ n in atTop, 0 ≤ b n)
    (hbound : ∀ᶠ n in atTop, e n ≤ C * b n) (hRate : b =O[atTop] a) :
    e =O[atTop] a := by
  apply IsBigO.trans ?_ hRate
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hbound, hb] with n h1 h2
  simpa only [Real.norm_eq_abs, abs_of_nonneg (he n), abs_of_nonneg h2] using h1

theorem tasa_raiz_perdida (loss : ℕ → ℝ) (m : ℕ → ℕ) (p : ℝ)
    (h : loss =O[atTop] fun n => (m n : ℝ) ^ (-p)) :
    (fun n => Real.sqrt (loss n)) =O[atTop] fun n => (m n : ℝ) ^ (-(p / 2)) := by
  have hr := IsBigO.rpow (r := (1 / 2 : ℝ)) (by norm_num)
    (Eventually.of_forall fun n => Real.rpow_nonneg (Nat.cast_nonneg (m n)) (-p)) h
  convert hr using 1
  · exact funext fun n => Real.sqrt_eq_rpow (loss n)
  · funext n
    rw [← Real.rpow_mul (Nat.cast_nonneg (m n))]
    congr 1
    ring

#check cota_L2_cambio_medida
#check cota_L2_de_supremo_esencial
#print axioms cota_densidad_dimensional
#print axioms cota_L2_cambio_medida
#print axioms cota_L2_de_perdida_dimensional
#print axioms cota_L2_de_supremo_puntual
#print axioms cota_L2_de_supremo_esencial
#print axioms tasa_raiz_perdida

end TesisPINN
