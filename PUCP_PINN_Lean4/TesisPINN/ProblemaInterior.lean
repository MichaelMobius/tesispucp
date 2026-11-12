import TesisPINN.Teorema38
import TesisPINN.ComparadoresAproximados

/-! Funcional PINN para una sola familia de muestras interiores. -/

noncomputable section

namespace TesisPINN

open MeasureTheory

variable {X : Type*} [PseudoMetricSpace X] {m : ℕ}

def constantesHolderInterior (U : Set X) (α : ℝ) (L : X → ℝ) : Set ℝ :=
  {C | 0 ≤ C ∧ ∀ x ∈ U, ∀ y ∈ U, |L x - L y| ≤ C * dist x y ^ α}

abbrev EsHolderInterior (U : Set X) (α : ℝ) (L : X → ℝ) : Prop :=
  (constantesHolderInterior U α L).Nonempty

/-- La seminorma exacta de la restricción al dominio. -/
def seminormaInterior (U : Set X) (α : ℝ) (L : X → ℝ) : ℝ :=
  sInf (constantesHolderInterior U α L)

theorem seminormaInterior_nonneg (U : Set X) (α : ℝ) (L : X → ℝ)
    (h : EsHolderInterior U α L) : 0 ≤ seminormaInterior U α L :=
  le_csInf h fun _ hC => hC.1

theorem seminormaInterior_cota (U : Set X) (α : ℝ) (L : X → ℝ)
    (h : EsHolderInterior U α L) (hα : 0 < α) :
    ∀ x ∈ U, ∀ y ∈ U, |L x - L y| ≤ seminormaInterior U α L * dist x y ^ α := by
  intro x hx y hy
  rcases eq_or_lt_of_le (dist_nonneg (x := x) (y := y)) with hd | hd
  · obtain ⟨C, hC⟩ := h
    have hc := hC.2 x hx y hy
    rw [← hd, Real.zero_rpow hα.ne', mul_zero] at hc ⊢
    exact hc
  · have hp : 0 < dist x y ^ α := Real.rpow_pos_of_pos hd _
    apply (div_le_iff₀ hp).1
    exact le_csInf h fun C hC => (div_le_iff₀ hp).2 (hC.2 x hx y hy)

def perdidaEmpiricaInterior (s : Fin m → X) (L f : X → ℝ) : ℝ :=
  (∑ i, (L (s i) - f (s i)) ^ 2) / (m : ℝ)

def funcionalInterior (U : Set X) (α : ℝ) (s : Fin m → X) (L f : X → ℝ)
    (a : ℝ) : ℝ :=
  perdidaEmpiricaInterior s L f + a * seminormaInterior U α L ^ 2

omit [PseudoMetricSpace X] in
theorem perdidaEmpiricaInterior_nonneg (s : Fin m → X) (L f : X → ℝ) :
    0 ≤ perdidaEmpiricaInterior s L f := by
  unfold perdidaEmpiricaInterior
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg m)

section Measure

variable [MeasurableSpace X] [OpensMeasurableSpace X]

def perdidaInterior (μ : Measure X) (L f : X → ℝ) : ℝ :=
  ∫ x, (L x - f x) ^ 2 ∂μ

omit [PseudoMetricSpace X] [OpensMeasurableSpace X] in
theorem perdidaInterior_nonneg (μ : Measure X) (L f : X → ℝ) :
    0 ≤ perdidaInterior μ L f :=
  integral_nonneg fun _ => sq_nonneg _

theorem residuoInterior_integrable (μ : Measure X) [IsProbabilityMeasure μ]
    (U : Set X) (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hμU : μ Uᶜ = 0) (L f : X → ℝ) (α : ℝ) (hα : 0 < α)
    (hL : EsHolderInterior U α L) (hf : EsHolderInterior U α f) :
    Integrable (fun x => (L x - f x) ^ 2) μ := by
  have hHL := seminormaInterior_cota U α L hL hα
  have hHf := seminormaInterior_cota U α f hf hα
  exact integrable_sq_of_holder_on_bounded μ U hUb hUne hμU _ _ _
    (add_nonneg (seminormaInterior_nonneg U α L hL) (seminormaInterior_nonneg U α f hf)) hα
    (aestronglyMeasurable_residuo_sq_de_continuidad μ U hU hμU L f
      (continuo_de_cota_holder U L _ _ hα hHL)
      (continuo_de_cota_holder U f _ _ hα hHf))
    (holder_resta U L f _ _ _ hHL hHf)

theorem perdidaInterior_le_funcional (μ : Measure X) [IsProbabilityMeasure μ]
    (U : Set X) (hU : MeasurableSet U) (hμU : μ Uᶜ = 0)
    (s : Fin m → X) (hm : 0 < m) (hs : ∀ i, s i ∈ U)
    (L f : X → ℝ) (α : ℝ) (hα : 0 < α)
    (hL : EsHolderInterior U α L) (hf : EsHolderInterior U α f)
    (ρ ρ₀ C d a : ℝ) (hρ : 0 < ρ) (hρ₀ : ρ ≤ ρ₀) (hC : 0 ≤ C)
    (hc : MuestrasCubren U s ρ) (hmass : MasaBolaSuperior μ U ρ₀ C d)
    (hint : Integrable (fun x => (L x - f x) ^ 2) μ)
    (ha : (3 * C * (m : ℝ) * ρ ^ d) * a = 3 * ρ ^ (2 * α)) :
    perdidaInterior μ L f ≤ (3 * C * (m : ℝ) * ρ ^ d) * funcionalInterior U α s L f a
      + 3 * ρ ^ (2 * α) * seminormaInterior U α f ^ 2 := by
  have hraw := integral_residuo_le_cobertura μ U hU (measure_univ) hμU L f s hm
    α ρ ρ₀ (seminormaInterior U α L) (seminormaInterior U α f) C d
    hα hρ hρ₀
    (seminormaInterior_nonneg U α L hL) (seminormaInterior_nonneg U α f hf) hC
    hs hc hmass (seminormaInterior_cota U α L hL hα)
    (seminormaInterior_cota U α f hf hα) hint
  rw [cuadrado_holder _ _ _ hρ.le, cuadrado_holder _ _ _ hρ.le] at hraw
  unfold perdidaInterior funcionalInterior perdidaEmpiricaInterior
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hsum : (3 * C * (m : ℝ) * ρ ^ d) *
      ((∑ i : Fin m, (L (s i) - f (s i)) ^ 2) / (m : ℝ)) =
      3 * C * ρ ^ d * ∑ i : Fin m, (L (s i) - f (s i)) ^ 2 := by
    field_simp
  rw [mul_add, hsum, ← mul_assoc, ha]
  linarith only [hraw]

end Measure

/-- Comparación aditiva con el ínfimo del funcional de una sola muestra. -/
theorem funcionalInterior_le_de_suboptimalidad {H : Type*}
    (U : Set X) (α : ℝ) (s : Fin m → X) (L : H → X → ℝ) (f : X → ℝ)
    (a : ℝ) (ha : 0 < a) (Hm : Set H) (h v : H) (hv : v ∈ Hm)
    (τ δ R K : ℝ)
    (hδ : funcionalInterior U α s (L h) f a ≤
      sInf ((fun w => funcionalInterior U α s (L w) f a) '' Hm) + δ)
    (hτ : perdidaEmpiricaInterior s (L v) f ≤ τ)
    (hR : seminormaInterior U α (L v) ^ 2 ≤ R) (htol : τ + δ ≤ K * a) :
    funcionalInterior U α s (L h) f a ≤ a * (R + K) ∧
      seminormaInterior U α (L h) ^ 2 ≤ R + K := by
  have hb : BddBelow ((fun w => funcionalInterior U α s (L w) f a) '' Hm) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact add_nonneg (perdidaEmpiricaInterior_nonneg s (L w) f)
      (mul_nonneg ha.le (sq_nonneg _))
  have hJ := le_comparador_de_infimo (fun w => funcionalInterior U α s (L w) f a)
    Hm h v δ hb hv hδ
  have hR' := mul_le_mul_of_nonneg_left hR ha.le
  have hj : funcionalInterior U α s (L h) f a ≤ a * (R + K) := by
    unfold funcionalInterior at hJ
    unfold funcionalInterior
    linarith only [hJ, hR', hτ, htol]
  exact ⟨hj, regularidad_controlada a _ _ _ ha (perdidaEmpiricaInterior_nonneg s (L h) f) hj⟩

#print axioms perdidaInterior_le_funcional
#print axioms funcionalInterior_le_de_suboptimalidad

end TesisPINN
