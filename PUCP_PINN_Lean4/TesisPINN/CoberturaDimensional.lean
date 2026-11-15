import TesisPINN.OcupacionLogaritmica
import TesisPINN.Lema36

/-! Cobertura con diámetro y exponentes de masa independientes. -/

noncomputable section

namespace TesisPINN

open Set MeasureTheory ProbabilityTheory

/-- Lema 3.3 con factor de diámetro `D`. Para `D = √d` y los exponentes
`d` y `d-1` se obtienen las constantes del texto. -/
theorem masa_bola_inferior_dimensional
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (U : Set X)
    (D c s ε₀ : ℝ) (hD : 0 < D) (hpart : ParticionesOcupacionLog μ U D c s ε₀)
    (x : X) (hx : x ∈ U) (r : ℝ) (hr : 0 < r) (hr₀ : r ≤ 2 * D * ε₀) :
    (c * (2 * D)⁻¹ ^ s) * r ^ s ≤ μ.real (Metric.ball x r ∩ U) := by
  let η := r / (2 * D)
  have hp : 0 < 2 * D := by positivity
  have hη : 0 < η := div_pos hr hp
  have hη₀ : η ≤ ε₀ := (div_le_iff₀ hp).2 (by linarith only [hr₀])
  obtain ⟨K, cells, _, _, hcov, hsub, hmass, hdiam⟩ := hpart η hη hη₀
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov hx)
  have hhalf : D * η = r / 2 := by dsimp [η]; field_simp
  have hc : cells k ⊆ Metric.ball x r ∩ U := by
    intro y hy
    have hd := hdiam k y hy x hk
    rw [hhalf] at hd
    exact ⟨by change dist y x < r; linarith, hsub k hy⟩
  calc
    _ = c * η ^ s := by
      dsimp [η]
      rw [div_eq_mul_inv, Real.mul_rpow hr.le (inv_nonneg.mpr hp.le)]
      ring
    _ ≤ _ := (hmass k).trans (measureReal_mono hc)

/-- Paquete geométrico de L3.6 para una familia finita de celdas con
solapamientos nulos y diámetro `D * η`. -/
theorem lema36_cobertura_dimensional
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [PseudoMetricSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure X) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → X) (hZ : ∀ i, Measurable (Z i)) (hindep : iIndepFun Z P)
    (hley : ∀ i, Measure.map (Z i) P = μ)
    (n K : ℕ) (cells : Fin K → Set X) (hc : ∀ k, MeasurableSet (cells k))
    (hdis : Pairwise (fun i j => μ (cells i ∩ cells j) = 0))
    (U : Set X) (hcov : U ⊆ ⋃ k, cells k) (D η p : ℝ)
    (hdiam : ∀ k, ∀ x ∈ cells k, ∀ y ∈ cells k, dist x y ≤ D * η)
    (hmass : ∀ k, p ≤ μ.real (cells k)) :
    ∃ A : Set Ω, MeasurableSet A ∧ (K : ℝ) * p ≤ 1 ∧
      1 - (K : ℝ) * (1 - p) ^ n ≤ P.real A ∧
      1 - (K : ℝ) * Real.exp (-(n : ℝ) * p) ≤ 1 - (K : ℝ) * (1 - p) ^ n ∧
      ∀ ω ∈ A, MuestrasCubren U (fun i : Fin n => Z i ω) (D * η) := by
  obtain ⟨hp, he⟩ := lema36_probabilidad_cobertura P μ Z n cells hc hZ hindep hley p hmass
  exact ⟨todasCeldasOcupadas Z n cells, todasCeldasOcupadas_measurable Z n cells hc hZ,
    cardinal_por_masa_minima_ae μ cells hc hdis p hmass, hp, he,
    ocupacion_implica_cobertura Z n U cells _ hcov hdiam⟩

/-- Parte determinista de (3.13) con dos exponentes de masa arbitrarios.
La aritmética muestral y los pesos de T3.4 son condiciones separadas. -/
theorem perdidaPoblacional_le_sumas_dimensional
    {H X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {mr mb : ℕ} (P : ProblemaPINN H X Y mr mb)
    (Hm : Set H) (U : Set X) (Γ : Set Y)
    (hU : MeasurableSet U) (hΓ : MeasurableSet Γ)
    (hμr : P.μr Uᶜ = 0) (hμb : P.μb Γᶜ = 0)
    (α εr εb εr₀ εb₀ Cr Cb Sf Sg sr sb : ℝ)
    (hα : 0 < α) (hεr : 0 < εr) (hεb : 0 < εb)
    (hεr₀ : εr ≤ εr₀) (hεb₀ : εb ≤ εb₀) (hCr : 0 ≤ Cr) (hCb : 0 ≤ Cb)
    (hsr : ∀ i, P.xr i ∈ U) (hsb : ∀ i, P.xb i ∈ Γ)
    (hcoverR : MuestrasCubren U P.xr εr) (hcoverB : MuestrasCubren Γ P.xb εb)
    (hmassR : MasaBolaSuperior P.μr U εr₀ Cr sr) (hmassB : MasaBolaSuperior P.μb Γ εb₀ Cb sb)
    (hHolder : CotasHolder P Hm U Γ α Sf Sg)
    (h : H) (hh : h ∈ Hm) (hint : P.PoblacionIntegrable h) :
    P.perdidaPoblacional h ≤
      P.lambdaR * (3 * Cr * εr ^ sr * ∑ i : Fin mr, (P.L h (P.xr i) - P.f (P.xr i)) ^ 2
        + 3 * (P.seminormaL h * εr ^ α) ^ 2 + 3 * (Sf * εr ^ α) ^ 2) +
      P.lambdaB * (3 * Cb * εb ^ sb * ∑ i : Fin mb, (P.B h (P.xb i) - P.g (P.xb i)) ^ 2
        + 3 * (P.seminormaB h * εb ^ α) ^ 2 + 3 * (Sg * εb ^ α) ^ 2) := by
  rcases hHolder with ⟨hSf, hSg, hCandidate, hf, hg⟩
  rcases hCandidate h hh with ⟨hSr, hSb, hL, hB⟩
  have hr := integral_residuo_le_cobertura P.μr U hU P.μr_prob
    hμr (P.L h) P.f P.xr P.mr_pos α εr εr₀ (P.seminormaL h)
    Sf Cr sr hα hεr hεr₀ hSr hSf hCr hsr hcoverR hmassR hL hf hint.1
  have hb := integral_residuo_le_cobertura P.μb Γ hΓ P.μb_prob
    hμb (P.B h) P.g P.xb P.mb_pos α εb εb₀ (P.seminormaB h)
    Sg Cb sb hα hεb hεb₀ hSb hSg hCb hsb hcoverB hmassB hB hg hint.2
  exact add_le_add (mul_le_mul_of_nonneg_left hr P.lambdaR_pos.le)
    (mul_le_mul_of_nonneg_left hb P.lambdaB_pos.le)

#check masa_bola_inferior_dimensional
#check lema36_cobertura_dimensional
#check perdidaPoblacional_le_sumas_dimensional
#print axioms masa_bola_inferior_dimensional
#print axioms lema36_cobertura_dimensional
#print axioms perdidaPoblacional_le_sumas_dimensional

end TesisPINN
