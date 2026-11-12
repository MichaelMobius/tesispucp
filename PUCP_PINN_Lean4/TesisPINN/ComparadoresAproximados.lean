import TesisPINN.CoberturaIntegral

/-! Parte determinista de la Proposición 3.10, con residuos escalares.
La comparación variacional vale sin restricciones geométricas. La cota poblacional
utiliza la desigualdad integral de cobertura con exponentes de masa 2 y 1. -/

noncomputable section

namespace TesisPINN

open MeasureTheory

/-- La suboptimalidad aditiva respecto del ínfimo se transfiere a cualquier
comparador admisible de un funcional acotado inferiormente. -/
theorem le_comparador_de_infimo {H : Type*} (J : H → ℝ) (Hm : Set H)
    (h v : H) (δ : ℝ) (hb : BddBelow (J '' Hm)) (hv : v ∈ Hm)
    (hh : J h ≤ sInf (J '' Hm) + δ) : J h ≤ J v + δ :=
  hh.trans (add_le_add_left (csInf_le hb (Set.mem_image_of_mem J hv)) δ)

namespace ProblemaPINN

variable {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {mr mb : ℕ}
variable (P : ProblemaPINN H X Y mr mb)

/-- Suboptimalidad aditiva en la clase admisible. -/
def EsMinimizadorAproximado (Hm : Set H) (h : H) (δ : ℝ) : Prop :=
  h ∈ Hm ∧ ∀ v ∈ Hm, P.funcionalRegularizado h ≤ P.funcionalRegularizado v + δ

/-- La comparación con todos los admisibles equivale a la cota por el ínfimo.
La no negatividad del funcional asegura que la imagen está acotada inferiormente. -/
theorem minimizadorAproximado_iff_le_infimo (Hm : Set H) (h : H) (δ : ℝ) :
    P.EsMinimizadorAproximado Hm h δ ↔
      h ∈ Hm ∧ P.funcionalRegularizado h ≤ sInf (P.funcionalRegularizado '' Hm) + δ := by
  have hbounded : BddBelow (P.funcionalRegularizado '' Hm) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, _, rfl⟩
    exact P.funcionalRegularizado_nonneg v
  constructor
  · rintro ⟨hh, hcomp⟩
    refine ⟨hh, (sub_le_iff_le_add).mp ?_⟩
    have hnonempty : (P.funcionalRegularizado '' Hm).Nonempty :=
      ⟨P.funcionalRegularizado h, ⟨h, hh, rfl⟩⟩
    apply le_csInf hnonempty
    rintro _ ⟨v, hv, rfl⟩
    exact (sub_le_iff_le_add).mpr (hcomp v hv)
  · rintro ⟨hh, hcomp⟩
    exact ⟨hh, fun v hv => le_comparador_de_infimo _ _ _ v δ hbounded hv hcomp⟩

/-- (3.39) y (3.40), antes de usar cobertura. -/
theorem cotas_minimizador_aproximado (Hm : Set H) (h v : H)
    (a ε δ Rstar : ℝ) (ha : 0 < a) (haR : P.regularizadorR = a)
    (haB : P.regularizadorB = a)
    (hmin : P.EsMinimizadorAproximado Hm h δ) (hv : v ∈ Hm)
    (hε : P.perdidaEmpirica v ≤ ε) (hR : P.regularidadTotal v ≤ Rstar) :
    P.regularidadTotal h ≤ Rstar + (ε + δ) / a ∧
      P.funcionalRegularizado h ≤ a * (Rstar + (ε + δ) / a) := by
  have hobj : P.funcionalRegularizado h ≤ a * (Rstar + (ε + δ) / a) := by
    calc
      P.funcionalRegularizado h ≤ P.funcionalRegularizado v + δ := hmin.2 v hv
      _ = P.perdidaEmpirica v + a * P.regularidadTotal v + δ := by
        rw [P.funcional_pesos_iguales v a haR haB]
      _ ≤ ε + a * Rstar + δ :=
        add_le_add_left (add_le_add hε (mul_le_mul_of_nonneg_left hR ha.le)) δ
      _ = a * (Rstar + (ε + δ) / a) := by
        rw [mul_add, mul_div_cancel₀ _ ha.ne']
        ring
  have hreg : a * P.regularidadTotal h ≤ P.funcionalRegularizado h := by
    rw [P.funcional_pesos_iguales h a haR haB]
    exact le_add_of_nonneg_left (P.perdidaEmpirica_nonneg h)
  exact ⟨le_of_mul_le_mul_left (hreg.trans hobj) ha, hobj⟩

end ProblemaPINN

/-- (3.41) con los términos de datos en los radios originales de (3.13).
El factor de cobertura es el de las dimensiones de masa interior 2 y frontera 1. -/
theorem perdidaPoblacional_aproximada_bajo_cobertura
    {H X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y] {mr mb : ℕ}
    (P : ProblemaPINN H X Y mr mb)
    (Hm : Set H) (U : Set X) (Γ : Set Y)
    (hU : MeasurableSet U) (hΓ : MeasurableSet Γ)
    (hμr : P.μr Uᶜ = 0) (hμb : P.μb Γᶜ = 0)
    (α εr εb εr₀ εb₀ Cr Cb Sf Sg ε δ Rstar : ℝ)
    (hα : 0 < α) (hεr : 0 < εr) (hεb : 0 < εb)
    (hεr₀ : εr ≤ εr₀) (hεb₀ : εb ≤ εb₀)
    (hCr : 0 < Cr) (hCb : 0 < Cb)
    (hsr : ∀ i, P.xr i ∈ U) (hsb : ∀ i, P.xb i ∈ Γ)
    (hcoverR : MuestrasCubren U P.xr εr) (hcoverB : MuestrasCubren Γ P.xb εb)
    (hmassR : MasaBolaSuperior P.μr U εr₀ Cr 2)
    (hmassB : MasaBolaSuperior P.μb Γ εb₀ Cb 1)
    (hHolder : CotasHolder P Hm U Γ α Sf Sg)
    (h v : H) (hmin : P.EsMinimizadorAproximado Hm h δ) (hv : v ∈ Hm)
    (hε : P.perdidaEmpirica v ≤ ε) (hR : P.regularidadTotal v ≤ Rstar)
    (hint : P.PoblacionIntegrable h) :
    let Cm := factorCoberturaCuadrado mr mb Cr Cb εr εb
    let a := pesoRegularizacionIgual P.lambdaR P.lambdaB εr εb α Cm
    P.regularizadorR = a → P.regularizadorB = a →
    P.perdidaPoblacional h ≤ Cm * (a * (Rstar + (ε + δ) / a)) +
      3 * P.lambdaR * εr ^ (2 * α) * Sf ^ 2 +
      3 * P.lambdaB * εb ^ (2 * α) * Sg ^ 2 := by
  intro Cm a haR haB
  have hCm : 0 < Cm := by
    have hr : 0 < Cr * (mr : ℝ) * εr ^ 2 :=
      mul_pos (mul_pos hCr (Nat.cast_pos.mpr P.mr_pos)) (sq_pos_of_pos hεr)
    exact mul_pos (by norm_num) (hr.trans_le (le_max_left _ _))
  have hwr : 0 < pesoCobertura P.lambdaR εr α Cm :=
    div_pos (mul_pos (mul_pos (by norm_num) P.lambdaR_pos) (Real.rpow_pos_of_pos hεr _)) hCm
  have ha : 0 < a :=
    hwr.trans_le (pesoInterior_le_igual P.lambdaR P.lambdaB εr εb α Cm)
  have hobj := (P.cotas_minimizador_aproximado Hm h v a ε δ Rstar
    ha haR haB hmin hv hε hR).2
  have hcover := objetivoCoberturaIntegral_de_hipotesis P Hm U Γ hU hΓ
    hμr hμb α εr εb εr₀ εb₀ Cr Cb Sf Sg hα hεr hεb hεr₀ hεb₀
    hCr hCb hsr hsb hcoverR hcoverB hmassR hmassB hHolder h hmin.1 hint
  have hR' := mul_le_mul_of_nonneg_right
    (pesoInterior_le_igual P.lambdaR P.lambdaB εr εb α Cm) (sq_nonneg (P.seminormaL h))
  have hB' := mul_le_mul_of_nonneg_right
    (pesoFrontera_le_igual P.lambdaR P.lambdaB εr εb α Cm) (sq_nonneg (P.seminormaB h))
  have hweighted :
      P.perdidaEmpirica h + pesoCobertura P.lambdaR εr α Cm * P.regularidadInterior h +
        pesoCobertura P.lambdaB εb α Cm * P.regularidadFrontera h ≤
      P.funcionalRegularizado h := by
    rw [P.funcional_pesos_iguales h a haR haB]
    unfold ProblemaPINN.regularidadTotal ProblemaPINN.regularidadInterior
      ProblemaPINN.regularidadFrontera
    dsimp only [a]
    rw [mul_add, ← add_assoc]
    exact add_le_add (add_le_add_right hR' _) hB'
  exact hcover.trans (add_le_add_left (add_le_add_left
    (mul_le_mul_of_nonneg_left (hweighted.trans hobj) hCm.le) _) _)

end TesisPINN

#check TesisPINN.ProblemaPINN.minimizadorAproximado_iff_le_infimo
#check TesisPINN.ProblemaPINN.cotas_minimizador_aproximado
#check TesisPINN.perdidaPoblacional_aproximada_bajo_cobertura
#print axioms TesisPINN.ProblemaPINN.minimizadorAproximado_iff_le_infimo
#print axioms TesisPINN.ProblemaPINN.cotas_minimizador_aproximado
#print axioms TesisPINN.perdidaPoblacional_aproximada_bajo_cobertura
