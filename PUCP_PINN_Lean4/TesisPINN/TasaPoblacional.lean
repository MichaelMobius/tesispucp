import TesisPINN.OcupacionAleatoria
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Tasa poblacional (3.26) en dimensión dos

La cobertura y la comparación variacional se usan con sus hipótesis
explícitas. Los índices `n`, `mr n` y `mb n` no se identifican.
-/

noncomputable section

namespace TesisPINN

open MeasureTheory ProbabilityTheory Filter Asymptotics

/-- Identidad exacta de (3.31), previa a sustituir los radios. -/
theorem factor_mul_peso_igual
    (mr mb : ℕ) (Cr Cb εr εb lambdaR lambdaB α : ℝ)
    (hCr : 0 < Cr) (hεr : 0 < εr) (hmr : 0 < mr) :
    factorCoberturaCuadrado mr mb Cr Cb εr εb *
      pesoRegularizacionIgual lambdaR lambdaB εr εb α
        (factorCoberturaCuadrado mr mb Cr Cb εr εb) =
      3 * max (lambdaR * εr ^ (2 * α)) (lambdaB * εb ^ (2 * α)) := by
  let Cm := factorCoberturaCuadrado mr mb Cr Cb εr εb
  have hCm : 0 < Cm := by
    have hr : 0 < Cr * (mr : ℝ) * εr ^ 2 := by positivity
    dsimp [Cm, factorCoberturaCuadrado]
    exact mul_pos (by norm_num) (lt_of_lt_of_le hr (le_max_left _ _))
  change Cm * max (pesoCobertura lambdaR εr α Cm)
    (pesoCobertura lambdaB εb α Cm) = _
  rw [mul_max_of_nonneg _ _ hCm.le]
  unfold pesoCobertura
  rw [mul_div_cancel₀ _ hCm.ne', mul_div_cancel₀ _ hCm.ne']
  simpa only [mul_assoc] using
    (mul_max_of_nonneg (lambdaR * εr ^ (2 * α))
      (lambdaB * εb ^ (2 * α)) (by norm_num : (0 : ℝ) ≤ 3)).symm

/-- La escala auxiliar de ocupación, escrita como potencias de `c` y `m`. -/
theorem escalaAuxiliarRaiz_eq_potencias
    (c s : ℝ) (m : ℕ) (hc : 0 < c) (hs : 0 < s) (hm : 0 < m) :
    escalaAuxiliarRaiz c s m =
      c ^ (-(1 / s)) * (m : ℝ) ^ (-(1 / (2 * s))) := by
  have hm' : 0 ≤ (m : ℝ) := by positivity
  have hroot : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  unfold escalaAuxiliarRaiz
  rw [one_div, Real.inv_rpow (mul_nonneg hc.le hroot)]
  rw [Real.mul_rpow hc.le hroot]
  rw [mul_inv_rev]
  rw [← Real.rpow_neg hroot, ← Real.rpow_neg hc.le]
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hm' (1 / (2 : ℝ)) (-(1 / s))]
  rw [mul_comm]
  congr 1
  field_simp

/-- Potencia `2α` del radio de cobertura en dimensión de masa `s`. -/
theorem radio_cobertura_potencia
    (c s α : ℝ) (m : ℕ) (hc : 0 < c) (hs : 0 < s) (hm : 0 < m) :
    (Real.sqrt 2 * escalaAuxiliarRaiz c s m) ^ (2 * α) =
      (Real.sqrt 2 * c ^ (-(1 / s))) ^ (2 * α) *
        (m : ℝ) ^ (-(α / s)) := by
  rw [escalaAuxiliarRaiz_eq_potencias c s m hc hs hm]
  rw [← mul_assoc]
  rw [Real.mul_rpow (by positivity : 0 ≤ Real.sqrt 2 * c ^ (-(1 / s)))
    (by positivity : 0 ≤ (m : ℝ) ^ (-(1 / (2 * s))))]
  rw [← Real.rpow_mul (by positivity : 0 ≤ (m : ℝ))
    (-(1 / (2 * s))) (2 * α)]
  congr 1
  field_simp

/-- La relación cuadrática de tamaños transforma la tasa de frontera en
una cota de la tasa interior, sin identificar `mr` con `mb`. -/
theorem tasa_frontera_le_tasa_interior
    (mr mb : ℕ) (K α : ℝ)
    (hmr : 0 < mr) (hmb : 0 < mb) (hK : 0 < K) (hα : 0 < α)
    (hrel : (mr : ℝ) ≤ K * (mb : ℝ) ^ 2) :
    (mb : ℝ) ^ (-α) ≤ K ^ (α / 2) * (mr : ℝ) ^ (-(α / 2)) := by
  have hmr' : 0 < (mr : ℝ) := Nat.cast_pos.mpr hmr
  have hmb' : 0 < (mb : ℝ) := Nat.cast_pos.mpr hmb
  have hpow := Real.rpow_le_rpow hmr'.le hrel (by positivity : 0 ≤ α / 2)
  rw [Real.mul_rpow hK.le (sq_nonneg _)] at hpow
  -- Normalize the two exponents in the inequality obtained by raising `hrel`.
  have hexp : (2 : ℝ) * (α / 2) = α := by ring
  rw [← Real.rpow_natCast (mb : ℝ) 2] at hpow
  norm_num only [Nat.cast_ofNat] at hpow
  rw [← Real.rpow_mul hmb'.le 2 (α / 2), hexp] at hpow
  have hmrPow : 0 < (mr : ℝ) ^ (α / 2) := Real.rpow_pos_of_pos hmr' _
  have hmbPow : 0 < (mb : ℝ) ^ α := Real.rpow_pos_of_pos hmb' _
  rw [Real.rpow_neg hmb'.le, Real.rpow_neg hmr'.le]
  have hcross : (1 : ℝ) * (mr : ℝ) ^ (α / 2) ≤
      K ^ (α / 2) * (mb : ℝ) ^ α := by simpa using hpow
  simpa only [div_eq_mul_inv, one_mul] using
    (div_le_div_iff₀ hmbPow hmrPow).2 hcross

theorem tasa_frontera_isBigO_tasa_interior
    (mr mb : ℕ → ℕ) (K α : ℝ)
    (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (hK : 0 < K) (hα : 0 < α)
    (hrel : ∀ᶠ n in atTop,
      (mr n : ℝ) ≤ K * (mb n : ℝ) ^ 2) :
    (fun n => (mb n : ℝ) ^ (-α)) =O[atTop]
      (fun n => (mr n : ℝ) ^ (-(α / 2))) := by
  apply isBigO_iff.mpr
  refine ⟨K ^ (α / 2), ?_⟩
  filter_upwards [hrel] with n hn
  have hbound := tasa_frontera_le_tasa_interior (mr n) (mb n)
    K α (hmr n) (hmb n) hK hα hn
  have hbn : 0 ≤ (mb n : ℝ) ^ (-α) := by positivity
  have hrn : 0 ≤ (mr n : ℝ) ^ (-(α / 2)) := by positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hbn, abs_of_nonneg hrn] using hbound

/-- El radio final, que usa la cota superior de masa de bolas, entra
eventualmente en cualquier intervalo `(0, ε₀]` de la Hipótesis 3.2. -/
theorem radio_cobertura_eventualmente_pequeno
    (c s ε₀ : ℝ) (m : ℕ → ℕ)
    (hc : 0 < c) (hs : 0 < s) (hε₀ : 0 < ε₀)
    (hmpos : ∀ n, 0 < m n)
    (hmGrowth : ∀ᶠ n in atTop, n ≤ m n) :
    ∀ᶠ n in atTop,
      Real.sqrt 2 * escalaAuxiliarRaiz c s (m n) ≤ ε₀ := by
  have hmTop : Tendsto m atTop atTop :=
    tendsto_atTop_mono' atTop hmGrowth tendsto_id
  have hmReal : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmTop
  have hpos : 0 < 1 / (2 * s) := by positivity
  have hpow : Tendsto (fun n => (m n : ℝ) ^ (-(1 / (2 * s))))
      atTop (nhds 0) := (tendsto_rpow_neg_atTop hpos).comp hmReal
  have hlim : Tendsto
      (fun n => Real.sqrt 2 * escalaAuxiliarRaiz c s (m n))
      atTop (nhds 0) := by
    convert hpow.const_mul (Real.sqrt 2 * c ^ (-(1 / s))) using 1 <;> try simp
    ext n
    rw [escalaAuxiliarRaiz_eq_potencias c s (m n) hc hs (hmpos n)]
    ring
  filter_upwards [hlim.eventually (Iio_mem_nhds hε₀)] with n hn
  exact hn.le

/-- Los prefijos del funcional empírico son literalmente las muestras
realizadas en el espacio común de probabilidad. -/
def problemaMuestral
    {H X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mr mb : ℕ → ℕ)
    (base : ∀ n, ProblemaPINN H X Y (mr n) (mb n))
    (Zr : ℕ → Ω → X) (Zb : ℕ → Ω → Y)
    (ω : Ω) (n : ℕ) : ProblemaPINN H X Y (mr n) (mb n) :=
  { base n with
    xr := fun i => Zr i ω
    xb := fun i => Zb i ω }

/-- La concentración de la ley implica pertenencia simultánea de todas las
muestras de la sucesión a su dominio; no se presupone para los prefijos. -/
theorem muestras_en_soporte_ae
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Measure X) (Z : ℕ → Ω → X)
    (U : Set X) (hμ : μ Uᶜ = 0)
    (hZ : ∀ i, Measurable (Z i))
    (hLaw : ∀ i, Measure.map (Z i) P = μ) :
    ∀ᵐ ω ∂P, ∀ i, Z i ω ∈ U := by
  apply ae_all_iff.mpr
  intro i
  have hU : U ∈ ae (Measure.map (Z i) P) := by
    rw [hLaw i]
    exact mem_ae_iff.mpr hμ
  exact mem_ae_of_mem_ae_map (hZ i).aemeasurable hU

private theorem cota_escalar_poblacional
    (loss x y t A B R F G : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 ≤ t)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR : 0 ≤ R) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hxA : x ≤ A * t) (hyB : y ≤ B * t)
    (hloss : loss ≤ 3 * max x y * R + 3 * x * F + 3 * y * G) :
    loss ≤ 3 * (A + B) * (R + F + G) * t := by
  have hmax : max x y ≤ x + y := max_le (by linarith) (by linarith)
  have hmaxmul := mul_le_mul_of_nonneg_right hmax hR
  have hxR := mul_le_mul_of_nonneg_right hxA hR
  have hyR := mul_le_mul_of_nonneg_right hyB hR
  have hxF := mul_le_mul_of_nonneg_right hxA hF
  have hyG := mul_le_mul_of_nonneg_right hyB hG
  have hAF : 0 ≤ A * t * G := by positivity
  have hBF : 0 ≤ B * t * F := by positivity
  nlinarith

/-- Un residuo Hölder sobre un soporte acotado tiene cuadrado integrable
para una medida finita, una vez establecida su mensurabilidad. -/
theorem integrable_sq_of_holder_on_bounded
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set X) (hU : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hμ : μ Uᶜ = 0)
    (f : X → ℝ) (C α : ℝ) (hC : 0 ≤ C) (hα : 0 < α)
    (hf : AEStronglyMeasurable (fun x => (f x) ^ 2) μ)
    (hHolder : ∀ x ∈ U, ∀ y ∈ U,
      |f x - f y| ≤ C * dist x y ^ α) :
    Integrable (fun x => (f x) ^ 2) μ := by
  obtain ⟨x₀, hx₀⟩ := hUne
  let B := |f x₀| + C * (Metric.diam U) ^ α
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply Integrable.of_bound hf (B ^ 2)
  filter_upwards [mem_ae_iff.mpr hμ] with x hx
  have hdist := Metric.dist_le_diam_of_mem hU hx hx₀
  have hpow := Real.rpow_le_rpow dist_nonneg hdist hα.le
  have hstep := hHolder x hx x₀ hx₀
  have hdiff : |f x - f x₀| ≤ C * (Metric.diam U) ^ α :=
    hstep.trans (mul_le_mul_of_nonneg_left hpow hC)
  have hval : |f x| ≤ B := by
    calc
      |f x| = |(f x - f x₀) + f x₀| := by ring
      _ ≤ |f x - f x₀| + |f x₀| := abs_add_le _ _
      _ ≤ B := by dsimp [B]; linarith
  calc
    ‖(f x) ^ 2‖ = |f x| ^ 2 := by simp [Real.norm_eq_abs]
    _ ≤ B ^ 2 := (sq_le_sq₀ (abs_nonneg _) hB).2 hval

/-- Las cotas Hölder de `CotasHolder` dan integrabilidad poblacional cuando
los dominios son acotados y los residuos cuadrados son medibles. -/
theorem poblacionIntegrable_de_holder_acotado
    {H X Y : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [PseudoMetricSpace Y] [MeasurableSpace Y]
    {mr mb : ℕ} (Pp : ProblemaPINN H X Y mr mb)
    (Hm : Set H) (U : Set X) (Gamma : Set Y)
    (hU : Bornology.IsBounded U) (hGamma : Bornology.IsBounded Gamma)
    (hUne : U.Nonempty) (hGne : Gamma.Nonempty)
    (hμr : Pp.μr Uᶜ = 0) (hμb : Pp.μb Gammaᶜ = 0)
    (α Sf Sg : ℝ) (hα : 0 < α)
    (hHolder : CotasHolder Pp Hm U Gamma α Sf Sg)
    (h : H) (hh : h ∈ Hm)
    (hMeasR : AEStronglyMeasurable
      (fun x => (Pp.L h x - Pp.f x) ^ 2) Pp.μr)
    (hMeasB : AEStronglyMeasurable
      (fun y => (Pp.B h y - Pp.g y) ^ 2) Pp.μb) :
    Pp.PoblacionIntegrable h := by
  rcases hHolder with ⟨hSf, hSg, hCandidates, hf, hg⟩
  obtain ⟨hCL, hCB, hL, hB⟩ := hCandidates h hh
  have hr (x : X) (hx : x ∈ U) (y : X) (hy : y ∈ U) :
      |(Pp.L h x - Pp.f x) - (Pp.L h y - Pp.f y)| ≤
        (Pp.seminormaL h + Sf) * dist x y ^ α := by
    have hrewrite : (Pp.L h x - Pp.f x) - (Pp.L h y - Pp.f y) =
        (Pp.L h x - Pp.L h y) - (Pp.f x - Pp.f y) := by ring
    rw [hrewrite]
    calc
      _ ≤ |Pp.L h x - Pp.L h y| + |Pp.f x - Pp.f y| := abs_sub _ _
      _ ≤ (Pp.seminormaL h + Sf) * dist x y ^ α := by
        have h1 := hL x hx y hy
        have h2 := hf x hx y hy
        nlinarith
  have hb (x : Y) (hx : x ∈ Gamma) (y : Y) (hy : y ∈ Gamma) :
      |(Pp.B h x - Pp.g x) - (Pp.B h y - Pp.g y)| ≤
        (Pp.seminormaB h + Sg) * dist x y ^ α := by
    have hrewrite : (Pp.B h x - Pp.g x) - (Pp.B h y - Pp.g y) =
        (Pp.B h x - Pp.B h y) - (Pp.g x - Pp.g y) := by ring
    rw [hrewrite]
    calc
      _ ≤ |Pp.B h x - Pp.B h y| + |Pp.g x - Pp.g y| := abs_sub _ _
      _ ≤ (Pp.seminormaB h + Sg) * dist x y ^ α := by
        have h1 := hB x hx y hy
        have h2 := hg x hx y hy
        nlinarith
  letI : IsProbabilityMeasure Pp.μr := ⟨Pp.μr_prob⟩
  letI : IsProbabilityMeasure Pp.μb := ⟨Pp.μb_prob⟩
  exact ⟨integrable_sq_of_holder_on_bounded Pp.μr U hU hUne hμr
      (fun x => Pp.L h x - Pp.f x) (Pp.seminormaL h + Sf) α
      (by linarith) hα hMeasR hr,
    integrable_sq_of_holder_on_bounded Pp.μb Gamma hGamma hGne hμb
      (fun y => Pp.B h y - Pp.g y) (Pp.seminormaB h + Sg) α
      (by linarith) hα hMeasB hb⟩

/-- La continuidad de operador y dato sobre el soporte da la
mensurabilidad casi en todas partes que necesita la integrabilidad. -/
theorem aestronglyMeasurable_residuo_sq_de_continuidad
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (hμ : μ Uᶜ = 0) (L f : X → ℝ)
    (hL : ContinuousOn L U) (hf : ContinuousOn f U) :
    AEStronglyMeasurable (fun x => (L x - f x) ^ 2) μ := by
  have hcont : ContinuousOn (fun x => (L x - f x) ^ 2) U :=
    (hL.sub hf).pow 2
  have hmeas := hcont.aestronglyMeasurable hU (μ := μ)
  rwa [Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hμ)] at hmeas

/-- Conversión cuantitativa de la cota de cobertura a la tasa de (3.26).
`K` es la constante de la relación `mr ≤ K mb²`. -/
theorem tasa_de_cota_cobertura
    (mr mb : ℕ) (Cr Cb cr cb lambdaR lambdaB α Sf Sg Rstar K loss : ℝ)
    (hmr : 0 < mr) (hmb : 0 < mb)
    (hCr : 0 < Cr) (hcr : 0 < cr) (hcb : 0 < cb)
    (hlambdaR : 0 < lambdaR) (hlambdaB : 0 < lambdaB)
    (hα : 0 < α) (hR : 0 ≤ Rstar) (hK : 0 < K)
    (hrel : (mr : ℝ) ≤ K * (mb : ℝ) ^ 2)
    (hloss : loss ≤
      factorCoberturaCuadrado mr mb Cr Cb
        (Real.sqrt 2 * escalaAuxiliarRaiz cr 2 mr)
        (Real.sqrt 2 * escalaAuxiliarRaiz cb 1 mb) *
      (pesoRegularizacionIgual lambdaR lambdaB
        (Real.sqrt 2 * escalaAuxiliarRaiz cr 2 mr)
        (Real.sqrt 2 * escalaAuxiliarRaiz cb 1 mb) α
        (factorCoberturaCuadrado mr mb Cr Cb
          (Real.sqrt 2 * escalaAuxiliarRaiz cr 2 mr)
          (Real.sqrt 2 * escalaAuxiliarRaiz cb 1 mb)) * Rstar) +
      3 * lambdaR * (Real.sqrt 2 * escalaAuxiliarRaiz cr 2 mr) ^ (2 * α) * Sf ^ 2 +
      3 * lambdaB * (Real.sqrt 2 * escalaAuxiliarRaiz cb 1 mb) ^ (2 * α) * Sg ^ 2) :
    loss ≤ 3 *
      (lambdaR * (Real.sqrt 2 * cr ^ (-(1 / (2 : ℝ)))) ^ (2 * α) +
       lambdaB * (Real.sqrt 2 * cb ^ (-(1 / (1 : ℝ)))) ^ (2 * α) *
         K ^ (α / 2)) *
      (Rstar + Sf ^ 2 + Sg ^ 2) * (mr : ℝ) ^ (-(α / 2)) := by
  let εr := Real.sqrt 2 * escalaAuxiliarRaiz cr 2 mr
  let εb := Real.sqrt 2 * escalaAuxiliarRaiz cb 1 mb
  let Ar := lambdaR * (Real.sqrt 2 * cr ^ (-(1 / (2 : ℝ)))) ^ (2 * α)
  let Ab := lambdaB * (Real.sqrt 2 * cb ^ (-(1 / (1 : ℝ)))) ^ (2 * α) *
    K ^ (α / 2)
  let t := (mr : ℝ) ^ (-(α / 2))
  have hεr : 0 < εr := by
    dsimp [εr, escalaAuxiliarRaiz]
    positivity
  have hεb : 0 < εb := by
    dsimp [εb, escalaAuxiliarRaiz]
    positivity
  have hfactor := factor_mul_peso_igual mr mb Cr Cb εr εb
    lambdaR lambdaB α hCr hεr hmr
  change loss ≤ factorCoberturaCuadrado mr mb Cr Cb εr εb *
      (pesoRegularizacionIgual lambdaR lambdaB εr εb α
        (factorCoberturaCuadrado mr mb Cr Cb εr εb) * Rstar) +
      3 * lambdaR * εr ^ (2 * α) * Sf ^ 2 +
      3 * lambdaB * εb ^ (2 * α) * Sg ^ 2 at hloss
  have hmain : factorCoberturaCuadrado mr mb Cr Cb εr εb *
      (pesoRegularizacionIgual lambdaR lambdaB εr εb α
        (factorCoberturaCuadrado mr mb Cr Cb εr εb) * Rstar) =
      3 * max (lambdaR * εr ^ (2 * α))
        (lambdaB * εb ^ (2 * α)) * Rstar := by
    rw [← mul_assoc, hfactor]
  rw [hmain] at hloss
  have hrpow := radio_cobertura_potencia cr 2 α mr hcr (by norm_num) hmr
  have hbpow := radio_cobertura_potencia cb 1 α mb hcb (by norm_num) hmb
  have hrate := tasa_frontera_le_tasa_interior mr mb K α hmr hmb hK hα hrel
  have hxr : lambdaR * εr ^ (2 * α) = Ar * t := by
    dsimp [εr, Ar, t]
    rw [hrpow]
    ring
  have hyb : lambdaB * εb ^ (2 * α) ≤ Ab * t := by
    dsimp [εb, Ab, t]
    rw [hbpow]
    have hlambdaAb : 0 ≤ lambdaB *
        (Real.sqrt 2 * cb ^ (-(1 / (1 : ℝ)))) ^ (2 * α) := by positivity
    have hh := mul_le_mul_of_nonneg_left hrate hlambdaAb
    convert hh using 1 <;> ring
  have hAr : 0 ≤ Ar := by dsimp [Ar]; positivity
  have hAb : 0 ≤ Ab := by dsimp [Ab]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hx : 0 ≤ lambdaR * εr ^ (2 * α) := by positivity
  have hy : 0 ≤ lambdaB * εb ^ (2 * α) := by positivity
  have hscalar := cota_escalar_poblacional loss
    (lambdaR * εr ^ (2 * α)) (lambdaB * εb ^ (2 * α))
    t Ar Ab Rstar (Sf ^ 2) (Sg ^ 2) hx hy ht hAr hAb hR
    (sq_nonneg _) (sq_nonneg _) hxr.le hyb
  have hloss' : loss ≤ 3 * max (lambdaR * εr ^ (2 * α))
      (lambdaB * εb ^ (2 * α)) * Rstar +
      3 * (lambdaR * εr ^ (2 * α)) * Sf ^ 2 +
      3 * (lambdaB * εb ^ (2 * α)) * Sg ^ 2 := by
    nlinarith [hloss]
  have hfinal := hscalar hloss'
  exact hfinal

/-- La forma con una constante eventual explícita implica la notación
`O` usual para pérdidas no negativas. -/
theorem isBigO_de_cota_eventual
    (loss t : ℕ → ℝ) (C : ℝ)
    (h : ∀ᶠ n in atTop, 0 ≤ loss n ∧ 0 ≤ t n ∧ loss n ≤ C * t n) :
    loss =O[atTop] t := by
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [h] with n hn
  simpa [Real.norm_eq_abs, abs_of_nonneg hn.1,
    abs_of_nonneg hn.2.1] using hn.2.2

/-- Forma casi segura de (3.26) para `d=2`. La existencia mensurable de
minimizadores y comparadores, y la cota uniforme aleatoria de la Hipótesis
3.7, figuran como premisas. Las particiones son las de la Hipótesis 3.2. -/
theorem tasa_poblacional_eventual_casi_segura
    {Ω X Y H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace H]
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (Zr : ℕ → Ω → X) (Zb : ℕ → Ω → Y)
    (mr mb Kr Kb : ℕ → ℕ)
    (cellsR : ∀ n, Fin (Kr n) → Set X)
    (cellsB : ∀ n, Fin (Kb n) → Set Y)
    (U : Set X) (Gamma : Set Y)
    (base : ∀ n, ProblemaPINN H X Y (mr n) (mb n))
    (Hm : ℕ → Set H) (hm g : ℕ → Ω → H)
    (_hMeasHm : ∀ n, Measurable (hm n))
    (_hMeasG : ∀ n, Measurable (g n))
    (cr cb Cr Cb ε₀ lambdaR lambdaB α Sf Sg K : ℝ)
    (hcr : 0 < cr) (hcb : 0 < cb)
    (hCr : 0 < Cr) (hCb : 0 < Cb)
    (hε₀ : 0 < ε₀) (hlambdaR : 0 < lambdaR)
    (hlambdaB : 0 < lambdaB) (hα : 0 < α) (hαone : α ≤ 1)
    (hK : 0 < K)
    (hU : MeasurableSet U) (hGamma : MeasurableSet Gamma)
    (hUbounded : Bornology.IsBounded U)
    (hGbounded : Bornology.IsBounded Gamma)
    (hμr : μr Uᶜ = 0) (hμb : μb Gammaᶜ = 0)
    (hmassR : MasaBolaSuperior μr U ε₀ Cr 2)
    (hmassB : MasaBolaSuperior μb Gamma ε₀ Cb 1)
    (hcR : ∀ n k, MeasurableSet (cellsR n k))
    (hcB : ∀ n k, MeasurableSet (cellsB n k))
    (hdisjR : ∀ n, Pairwise (fun i j => Disjoint (cellsR n i) (cellsR n j)))
    (hdisjB : ∀ n, Pairwise (fun i j => Disjoint (cellsB n i) (cellsB n j)))
    (hcoverR : ∀ n, U ⊆ ⋃ k, cellsR n k)
    (hcoverB : ∀ n, Gamma ⊆ ⋃ k, cellsB n k)
    (hdiamR : ∀ n k, ∀ x ∈ cellsR n k, ∀ y ∈ cellsR n k,
      dist x y ≤ Real.sqrt 2 * escalaAuxiliarRaiz cr 2 (mr n))
    (hdiamB : ∀ n k, ∀ x ∈ cellsB n k, ∀ y ∈ cellsB n k,
      dist x y ≤ Real.sqrt 2 * escalaAuxiliarRaiz cb 1 (mb n))
    (hmrpos : ∀ n, 0 < mr n) (hmbpos : ∀ n, 0 < mb n)
    (hmrGrowth : ∀ᶠ n in atTop, n ≤ mr n)
    (hmbGrowth : ∀ᶠ n in atTop, n ≤ mb n)
    (hminR : ∀ n k, cr * escalaAuxiliarRaiz cr 2 (mr n) ^ (2 : ℝ) ≤
      μr.real (cellsR n k))
    (hminB : ∀ n k, cb * escalaAuxiliarRaiz cb 1 (mb n) ^ (1 : ℝ) ≤
      μb.real (cellsB n k))
    (hZr : ∀ i, Measurable (Zr i))
    (hZb : ∀ i, Measurable (Zb i))
    (hIndepR : iIndepFun Zr P) (hIndepB : iIndepFun Zb P)
    (hLawR : ∀ i, Measure.map (Zr i) P = μr)
    (hLawB : ∀ i, Measure.map (Zb i) P = μb)
    (hbaseμr : ∀ n, (base n).μr = μr)
    (hbaseμb : ∀ n, (base n).μb = μb)
    (hbaseLambdaR : ∀ n, (base n).lambdaR = lambdaR)
    (hbaseLambdaB : ∀ n, (base n).lambdaB = lambdaB)
    (hHolder : ∀ ω n,
      CotasHolder (problemaMuestral mr mb base Zr Zb ω n)
        (Hm n) U Gamma α Sf Sg)
    (hContL : ∀ ω n, ContinuousOn
      (fun x => (problemaMuestral mr mb base Zr Zb ω n).L (hm n ω) x) U)
    (hContF : ∀ ω n, ContinuousOn
      (problemaMuestral mr mb base Zr Zb ω n).f U)
    (hContB : ∀ ω n, ContinuousOn
      (fun y => (problemaMuestral mr mb base Zr Zb ω n).B (hm n ω) y) Gamma)
    (hContG : ∀ ω n, ContinuousOn
      (problemaMuestral mr mb base Zr Zb ω n).g Gamma)
    (hweightsR : ∀ ω n,
      (problemaMuestral mr mb base Zr Zb ω n).regularizadorR =
        pesoRegularizacionIgual lambdaR lambdaB
          (Real.sqrt 2 * escalaAuxiliarRaiz cr 2 (mr n))
          (Real.sqrt 2 * escalaAuxiliarRaiz cb 1 (mb n)) α
          (factorCoberturaCuadrado (mr n) (mb n) Cr Cb
            (Real.sqrt 2 * escalaAuxiliarRaiz cr 2 (mr n))
            (Real.sqrt 2 * escalaAuxiliarRaiz cb 1 (mb n))))
    (hweightsB : ∀ ω n,
      (problemaMuestral mr mb base Zr Zb ω n).regularizadorB =
        pesoRegularizacionIgual lambdaR lambdaB
          (Real.sqrt 2 * escalaAuxiliarRaiz cr 2 (mr n))
          (Real.sqrt 2 * escalaAuxiliarRaiz cb 1 (mb n)) α
          (factorCoberturaCuadrado (mr n) (mb n) Cr Cb
            (Real.sqrt 2 * escalaAuxiliarRaiz cr 2 (mr n))
            (Real.sqrt 2 * escalaAuxiliarRaiz cb 1 (mb n))))
    (hrel : ∀ᶠ n in atTop,
      (mr n : ℝ) ≤ K * (mb n : ℝ) ^ 2)
    (hstats : ∀ᵐ ω ∂P, ∃ Rstar : ℝ, 0 ≤ Rstar ∧
      ∀ᶠ n in atTop,
        (problemaMuestral mr mb base Zr Zb ω n).EsMinimizadorGlobal
          (Hm n) (hm n ω) ∧
        (problemaMuestral mr mb base Zr Zb ω n).ComparadorExacto
          (Hm n) (g n ω) ∧
        (problemaMuestral mr mb base Zr Zb ω n).regularidadTotal
          (g n ω) ≤ Rstar) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧
      (∀ᶠ n in atTop,
        0 ≤ (problemaMuestral mr mb base Zr Zb ω n).perdidaPoblacional
          (hm n ω) ∧
        (problemaMuestral mr mb base Zr Zb ω n).perdidaPoblacional
          (hm n ω) ≤ C * (mr n : ℝ) ^ (-(α / 2))) ∧
      (fun n => (problemaMuestral mr mb base Zr Zb ω n).perdidaPoblacional
        (hm n ω)) =O[atTop] (fun n => (mr n : ℝ) ^ (-(α / 2))) := by
  have hcover := coberturas_cuadrado_eventuales_casi_seguras
    P μr Zr μb Zb Kr Kb mr mb cellsR cellsB U Gamma cr cb
    hcr hcb hcR hcB hdisjR hdisjB hcoverR hcoverB hdiamR hdiamB
    hmrpos hmbpos hmrGrowth hmbGrowth hminR hminB hZr hZb
    hIndepR hIndepB hLawR hLawB
  have hsr := muestras_en_soporte_ae P μr Zr U hμr hZr hLawR
  have hsb := muestras_en_soporte_ae P μb Zb Gamma hμb hZb hLawB
  have hsmallR := radio_cobertura_eventualmente_pequeno cr 2 ε₀ mr
    hcr (by norm_num) hε₀ hmrpos hmrGrowth
  have hsmallB := radio_cobertura_eventualmente_pequeno cb 1 ε₀ mb
    hcb (by norm_num) hε₀ hmbpos hmbGrowth
  have hUne : U.Nonempty := by
    by_contra hne
    have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hbad : (1 : ENNReal) = 0 := by simpa [he] using hμr
    norm_num at hbad
  have hGne : Gamma.Nonempty := by
    by_contra hne
    have he : Gamma = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hbad : (1 : ENNReal) = 0 := by simpa [he] using hμb
    norm_num at hbad
  filter_upwards [hcover, hsr, hsb, hstats] with ω hcoverω hsrω hsbω hstatω
  obtain ⟨Rstar, hRstar, hstatω⟩ := hstatω
  let C := 3 *
    (lambdaR * (Real.sqrt 2 * cr ^ (-(1 / (2 : ℝ)))) ^ (2 * α) +
     lambdaB * (Real.sqrt 2 * cb ^ (-(1 / (1 : ℝ)))) ^ (2 * α) *
       K ^ (α / 2)) *
    (Rstar + Sf ^ 2 + Sg ^ 2)
  have hrateEvent : ∀ᶠ n in atTop,
      0 ≤ (problemaMuestral mr mb base Zr Zb ω n).perdidaPoblacional
        (hm n ω) ∧
      (problemaMuestral mr mb base Zr Zb ω n).perdidaPoblacional
        (hm n ω) ≤ C * (mr n : ℝ) ^ (-(α / 2)) := by
    filter_upwards [hcoverω, hstatω, hsmallR, hsmallB, hrel] with
     n hcov hstat hsmallr hsmallb hrelN
    let Pn := problemaMuestral mr mb base Zr Zb ω n
    let εr := Real.sqrt 2 * escalaAuxiliarRaiz cr 2 (mr n)
    let εb := Real.sqrt 2 * escalaAuxiliarRaiz cb 1 (mb n)
    have hpR : 0 < εr := by
      have hm' : 0 < (mr n : ℝ) := Nat.cast_pos.mpr (hmrpos n)
      dsimp [εr, escalaAuxiliarRaiz]
      positivity
    have hpB : 0 < εb := by
      have hm' : 0 < (mb n : ℝ) := Nat.cast_pos.mpr (hmbpos n)
      dsimp [εb, escalaAuxiliarRaiz]
      positivity
    have hpnμr : Pn.μr = μr := by simpa [Pn, problemaMuestral] using hbaseμr n
    have hpnμb : Pn.μb = μb := by simpa [Pn, problemaMuestral] using hbaseμb n
    have hpnLambdaR : Pn.lambdaR = lambdaR := by
      simpa [Pn, problemaMuestral] using hbaseLambdaR n
    have hpnLambdaB : Pn.lambdaB = lambdaB := by
      simpa [Pn, problemaMuestral] using hbaseLambdaB n
    have hcoverN : MuestrasCubren U Pn.xr εr ∧
        MuestrasCubren Gamma Pn.xb εb := by
      simpa [Pn, problemaMuestral, εr, εb] using hcov
    have hInt := poblacionIntegrable_de_holder_acotado Pn (Hm n) U Gamma
        hUbounded hGbounded hUne hGne
        (by rw [hpnμr]; exact hμr)
        (by rw [hpnμb]; exact hμb)
        α Sf Sg hα (hHolder ω n) (hm n ω) hstat.1.1
        (by
          rw [hpnμr]
          exact aestronglyMeasurable_residuo_sq_de_continuidad μr U hU hμr
            (Pn.L (hm n ω)) Pn.f (hContL ω n) (hContF ω n))
        (by
          rw [hpnμb]
          exact aestronglyMeasurable_residuo_sq_de_continuidad μb Gamma
            hGamma hμb (Pn.B (hm n ω)) Pn.g (hContB ω n)
            (hContG ω n))
    have hnonneg : 0 ≤ Pn.perdidaPoblacional (hm n ω) :=
      Pn.perdidaPoblacional_nonneg (hm n ω) hInt
    have hineq := perdidaPoblacional_minimizador_bajo_cobertura
      Pn (Hm n) U Gamma hU hGamma
      (by rw [hpnμr]; exact hμr)
      (by rw [hpnμb]; exact hμb)
      α εr εb ε₀ ε₀ Cr Cb Sf Sg Rstar hα hpR hpB
      hsmallr hsmallb hCr hCb
      (by intro i; exact hsrω i)
      (by intro i; exact hsbω i)
      hcoverN.1 hcoverN.2
      (by rw [hpnμr]; exact hmassR)
      (by rw [hpnμb]; exact hmassB)
      (hHolder ω n) (hm n ω) (g n ω) hstat.1 hstat.2.1
      hstat.2.2 hInt
      (by rw [hpnLambdaR, hpnLambdaB]; exact hweightsR ω n)
      (by rw [hpnLambdaR, hpnLambdaB]; exact hweightsB ω n)
    have hineq' : Pn.perdidaPoblacional (hm n ω) ≤
        factorCoberturaCuadrado (mr n) (mb n) Cr Cb εr εb *
        (pesoRegularizacionIgual lambdaR lambdaB εr εb α
          (factorCoberturaCuadrado (mr n) (mb n) Cr Cb εr εb) * Rstar) +
        3 * lambdaR * εr ^ (2 * α) * Sf ^ 2 +
        3 * lambdaB * εb ^ (2 * α) * Sg ^ 2 := by
      simpa only [hpnLambdaR, hpnLambdaB] using hineq
    exact ⟨hnonneg, tasa_de_cota_cobertura (mr n) (mb n) Cr Cb cr cb
      lambdaR lambdaB α Sf Sg Rstar K (Pn.perdidaPoblacional (hm n ω))
      (hmrpos n) (hmbpos n) hCr hcr hcb hlambdaR hlambdaB hα
      hRstar hK hrelN hineq'⟩
  refine ⟨C, ?_, hrateEvent, ?_⟩
  · dsimp [C]
    positivity
  · apply isBigO_de_cota_eventual _ _ C
    filter_upwards [hrateEvent] with n hn
    exact ⟨hn.1, by positivity, hn.2⟩

/-- La cota eventual con constante real aleatoria es un evento medible
cuando cada pérdida es medible. La constante puede reducirse a un entero
por la no negatividad de la escala. -/
theorem measurableSet_eventual_cota_poblacional
    {Ω : Type*} [MeasurableSpace Ω]
    (loss : ℕ → Ω → ℝ) (t : ℕ → ℝ)
    (hloss : ∀ n, Measurable (loss n)) (ht : ∀ n, 0 ≤ t n) :
    MeasurableSet {ω | ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      loss n ω ≤ C * t n} := by
  have heq : {ω | ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
        loss n ω ≤ C * t n} =
      {ω | ∃ k : ℕ, ∀ᶠ n in atTop,
        loss n ω ≤ (k : ℝ) * t n} := by
    ext ω
    constructor
    · rintro ⟨C, _, hC⟩
      obtain ⟨k, hk⟩ := exists_nat_ge C
      refine ⟨k, ?_⟩
      filter_upwards [hC] with n hn
      exact hn.trans (mul_le_mul_of_nonneg_right hk (ht n))
    · rintro ⟨k, hk⟩
      exact ⟨k, Nat.cast_nonneg _, hk⟩
  rw [heq]
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  have hevent : {ω | ∀ᶠ n in atTop,
        loss n ω ≤ (k : ℝ) * t n} =
      ⋃ N : ℕ, ⋂ n : ℕ,
        {ω | N ≤ n → loss n ω ≤ (k : ℝ) * t n} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, eventually_atTop]
  rw [hevent]
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro n
  by_cases hN : N ≤ n
  · simpa [hN] using (measurableSet_le (hloss n) measurable_const)
  · simpa [hN] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω))

/-- La conclusión eventual casi segura se lee como probabilidad uno cuando
la pérdida aleatoria de cada índice es medible. -/
theorem prob_uno_eventual_cota_poblacional
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (loss : ℕ → Ω → ℝ) (t : ℕ → ℝ)
    (hloss : ∀ n, Measurable (loss n)) (ht : ∀ n, 0 ≤ t n)
    (hae : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      loss n ω ≤ C * t n) :
    P {ω | ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      loss n ω ≤ C * t n} = 1 := by
  exact (prob_compl_eq_zero_iff
    (measurableSet_eventual_cota_poblacional loss t hloss ht)).mp
      (mem_ae_iff.mp hae)

#print axioms TesisPINN.factor_mul_peso_igual
#print axioms TesisPINN.escalaAuxiliarRaiz_eq_potencias
#print axioms TesisPINN.radio_cobertura_potencia
#print axioms TesisPINN.tasa_frontera_le_tasa_interior
#print axioms TesisPINN.tasa_frontera_isBigO_tasa_interior
#print axioms TesisPINN.radio_cobertura_eventualmente_pequeno
#print axioms TesisPINN.muestras_en_soporte_ae
#print axioms TesisPINN.cota_escalar_poblacional
#print axioms TesisPINN.poblacionIntegrable_de_holder_acotado
#print axioms TesisPINN.aestronglyMeasurable_residuo_sq_de_continuidad
#print axioms TesisPINN.tasa_de_cota_cobertura
#print axioms TesisPINN.isBigO_de_cota_eventual
#print axioms TesisPINN.tasa_poblacional_eventual_casi_segura
#print axioms TesisPINN.measurableSet_eventual_cota_poblacional
#print axioms TesisPINN.prob_uno_eventual_cota_poblacional

end TesisPINN
