import TesisPINN.VoronoiMedible

/-! Integración determinista de las celdas de cobertura. -/

noncomputable section

namespace TesisPINN

open MeasureTheory

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {m : ℕ}

/-- Versión de (3.14) para la muestra que define la celda. -/
theorem residuo_puntual_en_celda
    (U : Set X) (L f : X → ℝ) (s : Fin m → X)
    (α ε CL Cf : ℝ) (hα : 0 < α) (hε : 0 ≤ ε)
    (hCL : 0 ≤ CL) (hCf : 0 ≤ Cf)
    (hs : ∀ i, s i ∈ U)
    (hL : ∀ x ∈ U, ∀ y ∈ U,
      |L x - L y| ≤ CL * dist x y ^ α)
    (hf : ∀ x ∈ U, ∀ y ∈ U,
      |f x - f y| ≤ Cf * dist x y ^ α)
    (i : Fin m) (x : X) (hx : x ∈ celdaVoronoi U s i)
    (hdist : dist x (s i) ≤ ε) :
    (L x - f x) ^ 2 ≤
      3 * ((L (s i) - f (s i)) ^ 2 +
        (CL * ε ^ α) ^ 2 + (Cf * ε ^ α) ^ 2) := by
  have hpow : dist x (s i) ^ α ≤ ε ^ α :=
    Real.rpow_le_rpow dist_nonneg hdist hα.le
  have hA : |L x - L (s i)| ≤ CL * ε ^ α :=
    (hL x hx.1 (s i) (hs i)).trans
      (mul_le_mul_of_nonneg_left hpow hCL)
  have hC : |f (s i) - f x| ≤ Cf * ε ^ α := by
    rw [abs_sub_comm]
    exact (hf x hx.1 (s i) (hs i)).trans
      (mul_le_mul_of_nonneg_left hpow hCf)
  have hAn : 0 ≤ CL * ε ^ α :=
    mul_nonneg hCL (Real.rpow_nonneg hε _)
  have hCn : 0 ≤ Cf * ε ^ α :=
    mul_nonneg hCf (Real.rpow_nonneg hε _)
  have hAsq : (L x - L (s i)) ^ 2 ≤ (CL * ε ^ α) ^ 2 := by
    calc
      (L x - L (s i)) ^ 2 = |L x - L (s i)| ^ 2 := by simp
      _ ≤ (CL * ε ^ α) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hAn).2 hA
  have hCsq : (f (s i) - f x) ^ 2 ≤ (Cf * ε ^ α) ^ 2 := by
    calc
      (f (s i) - f x) ^ 2 = |f (s i) - f x| ^ 2 := by simp
      _ ≤ (Cf * ε ^ α) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hCn).2 hC
  have hThree := cuadrado_suma_tres_le
    (L x - L (s i)) (L (s i) - f (s i)) (f (s i) - f x)
  nlinarith

/-- Integración sobre una partición de Voronoi, con la concentración de la
medida en `U` expresada explícitamente. -/
theorem integral_le_suma_celdas
    (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (hμ : μ Set.univ = 1) (hμU : μ Uᶜ = 0)
    (s : Fin m → X) (hm : 0 < m)
    (f : X → ℝ) (hf : Integrable f μ) (b : Fin m → ℝ)
    (hb : ∀ i, ∀ x ∈ celdaVoronoi U s i, f x ≤ b i) :
    ∫ x, f x ∂μ ≤
      ∑ i : Fin m, μ.real (celdaVoronoi U s i) * b i := by
  have hμfinite : μ Set.univ ≠ ⊤ := by rw [hμ]; simp
  have hcellfinite (i : Fin m) : μ (celdaVoronoi U s i) ≠ ⊤ :=
    ne_top_of_le_ne_top hμfinite (measure_mono (Set.subset_univ _))
  have hsplit : ∫ x, f x ∂μ =
      ∑ i : Fin m, ∫ x in celdaVoronoi U s i, f x ∂μ := by
    rw [integral_eq_setIntegral ((mem_ae_iff).2 hμU) f]
    conv_lhs => rw [celdaVoronoi_cover U s hm]
    exact integral_iUnion_fintype (fun i => celdaVoronoi_measurable U hU s i)
      (celdaVoronoi_pairwise U s) (fun i => hf.integrableOn)
  rw [hsplit]
  apply Finset.sum_le_sum
  intro i hi
  calc
    ∫ x in celdaVoronoi U s i, f x ∂μ ≤
        ∫ _ in celdaVoronoi U s i, b i ∂μ :=
      setIntegral_mono_on hf.integrableOn (integrableOn_const (hcellfinite i))
        (celdaVoronoi_measurable U hU s i) (hb i)
    _ = μ.real (celdaVoronoi U s i) * b i := by
      rw [setIntegral_const, smul_eq_mul]

theorem suma_masas_celdas
    (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (hμ : μ Set.univ = 1) (hμU : μ Uᶜ = 0)
    (s : Fin m → X) (hm : 0 < m) :
    ∑ i : Fin m, μ.real (celdaVoronoi U s i) = 1 := by
  have hsplit := integral_iUnion_fintype
    (μ := μ) (f := fun _ : X => (1 : ℝ))
    (fun i => celdaVoronoi_measurable U hU s i)
    (celdaVoronoi_pairwise U s)
    (fun i => integrableOn_const (by
      have hfinite : μ Set.univ ≠ ⊤ := by rw [hμ]; simp
      exact ne_top_of_le_ne_top hfinite (measure_mono (Set.subset_univ _))))
  have hUone : μ.real U = 1 := by
    rw [measureReal_def, measure_of_measure_compl_eq_zero hμU, hμ]
    norm_num
  rw [← celdaVoronoi_cover U s hm] at hsplit
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hsplit
  rw [hUone] at hsplit
  exact hsplit.symm

theorem medidaReal_celdaVoronoi_le
    (μ : Measure X) (U : Set X) (s : Fin m → X)
    (ε ε₀ C d : ℝ) (hμ : μ Set.univ = 1)
    (hε : 0 < ε) (hε₀ : ε ≤ ε₀) (hC : 0 ≤ C)
    (hs : ∀ i, s i ∈ U) (hcover : MuestrasCubren U s ε)
    (hmass : MasaBolaSuperior μ U ε₀ C d) (i : Fin m) :
    μ.real (celdaVoronoi U s i) ≤ C * ε ^ d := by
  have hfinite : μ (celdaVoronoi U s i) ≠ ⊤ := by
    have hμfinite : μ Set.univ ≠ ⊤ := by rw [hμ]; simp
    exact ne_top_of_le_ne_top hμfinite (measure_mono (Set.subset_univ _))
  have hnonneg : 0 ≤ C * ε ^ d :=
    mul_nonneg hC (Real.rpow_nonneg hε.le _)
  have hle := (ENNReal.toReal_le_toReal hfinite (by simp)).2
    (medida_celdaVoronoi_le μ U s ε ε₀ C d hε hε₀ hs hcover hmass i)
  simpa only [measureReal_def, ENNReal.toReal_ofReal hnonneg] using hle

/-- (3.13) para un solo término residual, con exponente de masa `d`.
La hipótesis de integrabilidad hace explícita la finitud de la integral real. -/
theorem integral_residuo_le_cobertura
    (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (hμ : μ Set.univ = 1) (hμU : μ Uᶜ = 0)
    (L f : X → ℝ) (s : Fin m → X) (hm : 0 < m)
    (α ε ε₀ CL Cf C d : ℝ)
    (hα : 0 < α) (hε : 0 < ε) (hε₀ : ε ≤ ε₀)
    (hCL : 0 ≤ CL) (hCf : 0 ≤ Cf) (hC : 0 ≤ C)
    (hs : ∀ i, s i ∈ U) (hcover : MuestrasCubren U s ε)
    (hmass : MasaBolaSuperior μ U ε₀ C d)
    (hL : ∀ x ∈ U, ∀ y ∈ U,
      |L x - L y| ≤ CL * dist x y ^ α)
    (hf : ∀ x ∈ U, ∀ y ∈ U,
      |f x - f y| ≤ Cf * dist x y ^ α)
    (hint : Integrable (fun x => (L x - f x) ^ 2) μ) :
    ∫ x, (L x - f x) ^ 2 ∂μ ≤
      3 * C * ε ^ d * ∑ i : Fin m, (L (s i) - f (s i)) ^ 2
        + 3 * (CL * ε ^ α) ^ 2 + 3 * (Cf * ε ^ α) ^ 2 := by
  let v : Fin m → ℝ := fun i => (L (s i) - f (s i)) ^ 2
  let a : ℝ := (CL * ε ^ α) ^ 2
  let b : ℝ := (Cf * ε ^ α) ^ 2
  let M : ℝ := C * ε ^ d
  have hcell (i : Fin m) : μ.real (celdaVoronoi U s i) ≤ M :=
    medidaReal_celdaVoronoi_le μ U s ε ε₀ C d hμ hε hε₀ hC hs hcover hmass i
  have hsum : ∑ i : Fin m, μ.real (celdaVoronoi U s i) = 1 :=
    suma_masas_celdas μ U hU hμ hμU s hm
  -- The required distance bound follows from coverage and lexicographic minimality.
  have hpoint' (i : Fin m) (x : X) (hx : x ∈ celdaVoronoi U s i) :
      (L x - f x) ^ 2 ≤ 3 * (v i + a + b) :=
    residuo_puntual_en_celda U L f s α ε CL Cf hα hε.le hCL hCf
      hs hL hf i x hx (by
        obtain ⟨j, hj⟩ := hcover x hx.1
        exact ((Prod.Lex.toLex_le_toLex').mp (hx.2 j)).1.trans hj)
  have hfirst := integral_le_suma_celdas μ U hU hμ hμU s hm
    (fun x => (L x - f x) ^ 2) hint (fun i => 3 * (v i + a + b)) hpoint'
  have hsecond :
      ∑ i : Fin m, μ.real (celdaVoronoi U s i) * (3 * (v i + a + b)) ≤
        ∑ i : Fin m, (3 * M * v i + μ.real (celdaVoronoi U s i) *
          (3 * (a + b))) := by
    apply Finset.sum_le_sum
    intro i hi
    have hv : 0 ≤ v i := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_right (hcell i) hv
    nlinarith
  calc
    ∫ x, (L x - f x) ^ 2 ∂μ ≤
        ∑ i : Fin m, μ.real (celdaVoronoi U s i) * (3 * (v i + a + b)) := hfirst
    _ ≤ ∑ i : Fin m, (3 * M * v i + μ.real (celdaVoronoi U s i) *
          (3 * (a + b))) := hsecond
    _ = 3 * M * ∑ i : Fin m, v i + 3 * a + 3 * b := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hsum]
      ring
    _ = 3 * C * ε ^ d * ∑ i : Fin m, (L (s i) - f (s i)) ^ 2
        + 3 * (CL * ε ^ α) ^ 2 + 3 * (Cf * ε ^ α) ^ 2 := by
      dsimp [M, a, b, v]
      ring

/-- Suma de las desigualdades integrales interior y de frontera de (3.13),
antes de absorber los promedios empíricos en `C_m`. -/
theorem perdidaPoblacional_le_sumas_cobertura
    {H Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {mr mb : ℕ}
    (P : ProblemaPINN H X Y mr mb)
    (Hm : Set H) (U : Set X) (Gamma : Set Y)
    (hU : MeasurableSet U) (hGamma : MeasurableSet Gamma)
    (hμr : P.μr Uᶜ = 0) (hμb : P.μb Gammaᶜ = 0)
    (α εr εb εr₀ εb₀ Cr Cb Sf Sg : ℝ)
    (hα : 0 < α) (hεr : 0 < εr) (hεb : 0 < εb)
    (hεr₀ : εr ≤ εr₀) (hεb₀ : εb ≤ εb₀)
    (hCr : 0 ≤ Cr) (hCb : 0 ≤ Cb)
    (hsr : ∀ i, P.xr i ∈ U) (hsb : ∀ i, P.xb i ∈ Gamma)
    (hcoverR : MuestrasCubren U P.xr εr)
    (hcoverB : MuestrasCubren Gamma P.xb εb)
    (hmassR : MasaBolaSuperior P.μr U εr₀ Cr 2)
    (hmassB : MasaBolaSuperior P.μb Gamma εb₀ Cb 1)
    (hHolder : CotasHolder P Hm U Gamma α Sf Sg)
    (h : H) (hh : h ∈ Hm) (hint : P.PoblacionIntegrable h) :
    P.perdidaPoblacional h ≤
      P.lambdaR * (3 * Cr * εr ^ (2 : ℝ) *
        ∑ i : Fin mr, (P.L h (P.xr i) - P.f (P.xr i)) ^ 2
        + 3 * (P.seminormaL h * εr ^ α) ^ 2
        + 3 * (Sf * εr ^ α) ^ 2) +
      P.lambdaB * (3 * Cb * εb ^ (1 : ℝ) *
        ∑ i : Fin mb, (P.B h (P.xb i) - P.g (P.xb i)) ^ 2
        + 3 * (P.seminormaB h * εb ^ α) ^ 2
        + 3 * (Sg * εb ^ α) ^ 2) := by
  rcases hHolder with ⟨hSf, hSg, hCandidate, hf, hg⟩
  rcases hCandidate h hh with ⟨hSr, hSb, hL, hB⟩
  have hr := integral_residuo_le_cobertura P.μr U hU P.μr_prob
    hμr (P.L h) P.f P.xr P.mr_pos α εr εr₀ (P.seminormaL h)
    Sf Cr 2 hα hεr hεr₀ hSr hSf hCr hsr hcoverR hmassR hL hf hint.1
  have hb := integral_residuo_le_cobertura P.μb Gamma hGamma P.μb_prob
    hμb (P.B h) P.g P.xb P.mb_pos α εb εb₀ (P.seminormaB h)
    Sg Cb 1 hα hεb hεb₀ hSb hSg hCb hsb hcoverB hmassB hB hg hint.2
  have hr' := mul_le_mul_of_nonneg_left hr P.lambdaR_pos.le
  have hb' := mul_le_mul_of_nonneg_left hb P.lambdaB_pos.le
  exact add_le_add hr' hb'

private theorem cuadrado_holder (S ε α : ℝ) (hε : 0 ≤ ε) :
    (S * ε ^ α) ^ 2 = ε ^ (2 * α) * S ^ 2 := by
  calc
    (S * ε ^ α) ^ 2 = S ^ 2 * (ε ^ α) ^ 2 := by ring
    _ = S ^ 2 * ε ^ (α * 2) := by rw [← Real.rpow_mul_natCast hε]; norm_num
    _ = ε ^ (2 * α) * S ^ 2 := by rw [show α * (2 : ℝ) = 2 * α by ring]; ring

private theorem coeficiente_muestra_le
    (m : ℕ) (hm : 0 < m) (lam C ε d Cm S : ℝ)
    (hlam : 0 ≤ lam) (hS : 0 ≤ S)
    (hCm : 3 * C * (m : ℝ) * ε ^ d ≤ Cm) :
    lam * (3 * C * ε ^ d * S) ≤ Cm * (lam / m * S) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hcoef : 3 * C * ε ^ d ≤ Cm / (m : ℝ) := by
    apply (le_div_iff₀ hm').2
    nlinarith [hCm]
  have hmul := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hlam hS)
  calc
    lam * (3 * C * ε ^ d * S) = (3 * C * ε ^ d) * (lam * S) := by ring
    _ ≤ (Cm / m) * (lam * S) := hmul
    _ = Cm * (lam / m * S) := by ring

private theorem objetivo_de_cota_sumas
    {H Y : Type*} [MeasurableSpace Y] {mr mb : ℕ}
    (P : ProblemaPINN H X Y mr mb) (h : H)
    (α εr εb Cr Cb Sf Sg : ℝ)
    (hεr : 0 < εr) (hεb : 0 < εb)
    (hCr : 0 < Cr) (hCb : 0 < Cb)
    (hraw : P.perdidaPoblacional h ≤
      P.lambdaR * (3 * Cr * εr ^ (2 : ℝ) *
        ∑ i : Fin mr, (P.L h (P.xr i) - P.f (P.xr i)) ^ 2
        + 3 * (P.seminormaL h * εr ^ α) ^ 2
        + 3 * (Sf * εr ^ α) ^ 2) +
      P.lambdaB * (3 * Cb * εb ^ (1 : ℝ) *
        ∑ i : Fin mb, (P.B h (P.xb i) - P.g (P.xb i)) ^ 2
        + 3 * (P.seminormaB h * εb ^ α) ^ 2
        + 3 * (Sg * εb ^ α) ^ 2)) :
    ObjetivoCoberturaIntegral P εr εb α Cr Cb Sf Sg h := by
  let Cm := factorCoberturaCuadrado mr mb Cr Cb εr εb
  have hCm : 0 < Cm := by
    have hr : 0 < Cr * (mr : ℝ) * εr ^ 2 := by
      exact mul_pos (mul_pos hCr (Nat.cast_pos.mpr P.mr_pos)) (sq_pos_of_pos hεr)
    dsimp [Cm, factorCoberturaCuadrado]
    exact mul_pos (by norm_num) (lt_of_lt_of_le hr (le_max_left _ _))
  have hCmR : 3 * Cr * (mr : ℝ) * εr ^ (2 : ℝ) ≤ Cm := by
    rw [Real.rpow_two]
    dsimp [Cm, factorCoberturaCuadrado]
    nlinarith [le_max_left (Cr * (mr : ℝ) * εr ^ 2)
      (Cb * (mb : ℝ) * εb)]
  have hCmB : 3 * Cb * (mb : ℝ) * εb ^ (1 : ℝ) ≤ Cm := by
    rw [Real.rpow_one]
    dsimp [Cm, factorCoberturaCuadrado]
    nlinarith [le_max_right (Cr * (mr : ℝ) * εr ^ 2)
      (Cb * (mb : ℝ) * εb)]
  have hwr : Cm * pesoCobertura P.lambdaR εr α Cm =
      3 * P.lambdaR * εr ^ (2 * α) := by
    unfold pesoCobertura
    field_simp
  have hwb : Cm * pesoCobertura P.lambdaB εb α Cm =
      3 * P.lambdaB * εb ^ (2 * α) := by
    unfold pesoCobertura
    field_simp
  have hSr : 0 ≤ ∑ i : Fin mr,
      (P.L h (P.xr i) - P.f (P.xr i)) ^ 2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hSb : 0 ≤ ∑ i : Fin mb,
      (P.B h (P.xb i) - P.g (P.xb i)) ^ 2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hsampleR := coeficiente_muestra_le mr P.mr_pos P.lambdaR Cr εr 2 Cm
    (∑ i : Fin mr, (P.L h (P.xr i) - P.f (P.xr i)) ^ 2)
    P.lambdaR_pos.le hSr hCmR
  have hsampleB := coeficiente_muestra_le mb P.mb_pos P.lambdaB Cb εb 1 Cm
    (∑ i : Fin mb, (P.B h (P.xb i) - P.g (P.xb i)) ^ 2)
    P.lambdaB_pos.le hSb hCmB
  have hsemR : P.lambdaR * (3 * (P.seminormaL h * εr ^ α) ^ 2) =
      Cm * (pesoCobertura P.lambdaR εr α Cm * P.regularidadInterior h) := by
    rw [cuadrado_holder _ _ _ hεr.le]
    unfold ProblemaPINN.regularidadInterior
    calc
      P.lambdaR * (3 * (εr ^ (2 * α) * P.seminormaL h ^ 2)) =
          (3 * P.lambdaR * εr ^ (2 * α)) * P.seminormaL h ^ 2 := by ring
      _ = (Cm * pesoCobertura P.lambdaR εr α Cm) * P.seminormaL h ^ 2 := by rw [hwr]
      _ = Cm * (pesoCobertura P.lambdaR εr α Cm * P.seminormaL h ^ 2) := by ring
  have hsemB : P.lambdaB * (3 * (P.seminormaB h * εb ^ α) ^ 2) =
      Cm * (pesoCobertura P.lambdaB εb α Cm * P.regularidadFrontera h) := by
    rw [cuadrado_holder _ _ _ hεb.le]
    unfold ProblemaPINN.regularidadFrontera
    calc
      P.lambdaB * (3 * (εb ^ (2 * α) * P.seminormaB h ^ 2)) =
          (3 * P.lambdaB * εb ^ (2 * α)) * P.seminormaB h ^ 2 := by ring
      _ = (Cm * pesoCobertura P.lambdaB εb α Cm) * P.seminormaB h ^ 2 := by rw [hwb]
      _ = Cm * (pesoCobertura P.lambdaB εb α Cm * P.seminormaB h ^ 2) := by ring
  have hdataR : P.lambdaR * (3 * (Sf * εr ^ α) ^ 2) =
      3 * P.lambdaR * εr ^ (2 * α) * Sf ^ 2 := by
    rw [cuadrado_holder _ _ _ hεr.le]
    ring
  have hdataB : P.lambdaB * (3 * (Sg * εb ^ α) ^ 2) =
      3 * P.lambdaB * εb ^ (2 * α) * Sg ^ 2 := by
    rw [cuadrado_holder _ _ _ hεb.le]
    ring
  change P.perdidaPoblacional h ≤
    Cm * (P.perdidaEmpirica h +
      pesoCobertura P.lambdaR εr α Cm * P.regularidadInterior h +
      pesoCobertura P.lambdaB εb α Cm * P.regularidadFrontera h) +
    3 * P.lambdaR * εr ^ (2 * α) * Sf ^ 2 +
    3 * P.lambdaB * εb ^ (2 * α) * Sg ^ 2
  unfold ProblemaPINN.perdidaEmpirica ProblemaPINN.perdidaEmpiricaInterior
    ProblemaPINN.perdidaEmpiricaFrontera
  exact hraw.trans (by
    change P.lambdaR * (3 * Cr * εr ^ (2 : ℝ) *
        ∑ i : Fin mr, (P.L h (P.xr i) - P.f (P.xr i)) ^ 2
        + 3 * (P.seminormaL h * εr ^ α) ^ 2
        + 3 * (Sf * εr ^ α) ^ 2) +
      P.lambdaB * (3 * Cb * εb ^ (1 : ℝ) *
        ∑ i : Fin mb, (P.B h (P.xb i) - P.g (P.xb i)) ^ 2
        + 3 * (P.seminormaB h * εb ^ α) ^ 2
        + 3 * (Sg * εb ^ α) ^ 2) ≤ _
    nlinarith [hsampleR, hsampleB, hsemR, hsemB, hdataR, hdataB])

/-- La desigualdad integral (3.13) de la tesis, en dimensión interior `2` y
dimensión de frontera `1`. Cobertura, soporte e integrabilidad son hipótesis
deterministas explícitas; no se afirma que el muestreo las satisfaga casi seguramente. -/
theorem objetivoCoberturaIntegral_de_hipotesis
    {H Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {mr mb : ℕ}
    (P : ProblemaPINN H X Y mr mb)
    (Hm : Set H) (U : Set X) (Gamma : Set Y)
    (hU : MeasurableSet U) (hGamma : MeasurableSet Gamma)
    (hμr : P.μr Uᶜ = 0) (hμb : P.μb Gammaᶜ = 0)
    (α εr εb εr₀ εb₀ Cr Cb Sf Sg : ℝ)
    (hα : 0 < α) (hεr : 0 < εr) (hεb : 0 < εb)
    (hεr₀ : εr ≤ εr₀) (hεb₀ : εb ≤ εb₀)
    (hCr : 0 < Cr) (hCb : 0 < Cb)
    (hsr : ∀ i, P.xr i ∈ U) (hsb : ∀ i, P.xb i ∈ Gamma)
    (hcoverR : MuestrasCubren U P.xr εr)
    (hcoverB : MuestrasCubren Gamma P.xb εb)
    (hmassR : MasaBolaSuperior P.μr U εr₀ Cr 2)
    (hmassB : MasaBolaSuperior P.μb Gamma εb₀ Cb 1)
    (hHolder : CotasHolder P Hm U Gamma α Sf Sg)
    (h : H) (hh : h ∈ Hm) (hint : P.PoblacionIntegrable h) :
    ObjetivoCoberturaIntegral P εr εb α Cr Cb Sf Sg h := by
  apply objetivo_de_cota_sumas P h α εr εb Cr Cb Sf Sg hεr hεb hCr hCb
  exact perdidaPoblacional_le_sumas_cobertura P Hm U Gamma hU hGamma
    hμr hμb α εr εb εr₀ εb₀ Cr Cb Sf Sg hα hεr hεb hεr₀ hεb₀
    hCr.le hCb.le hsr hsb hcoverR hcoverB hmassR hmassB hHolder h hh hint

/-- Cota poblacional determinista para un minimizador con comparador exacto.
La cobertura es una hipótesis geométrica; este teorema no afirma (3.26). -/
theorem perdidaPoblacional_minimizador_bajo_cobertura
    {H Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {mr mb : ℕ}
    (P : ProblemaPINN H X Y mr mb)
    (Hm : Set H) (U : Set X) (Gamma : Set Y)
    (hU : MeasurableSet U) (hGamma : MeasurableSet Gamma)
    (hμr : P.μr Uᶜ = 0) (hμb : P.μb Gammaᶜ = 0)
    (α εr εb εr₀ εb₀ Cr Cb Sf Sg Rstar : ℝ)
    (hα : 0 < α) (hεr : 0 < εr) (hεb : 0 < εb)
    (hεr₀ : εr ≤ εr₀) (hεb₀ : εb ≤ εb₀)
    (hCr : 0 < Cr) (hCb : 0 < Cb)
    (hsr : ∀ i, P.xr i ∈ U) (hsb : ∀ i, P.xb i ∈ Gamma)
    (hcoverR : MuestrasCubren U P.xr εr)
    (hcoverB : MuestrasCubren Gamma P.xb εb)
    (hmassR : MasaBolaSuperior P.μr U εr₀ Cr 2)
    (hmassB : MasaBolaSuperior P.μb Gamma εb₀ Cb 1)
    (hHolder : CotasHolder P Hm U Gamma α Sf Sg)
    (hm g : H) (hmin : P.EsMinimizadorGlobal Hm hm)
    (hg : P.ComparadorExacto Hm g)
    (hRstar : P.regularidadTotal g ≤ Rstar)
    (hint : P.PoblacionIntegrable hm)
    (haR : P.regularizadorR =
      pesoRegularizacionIgual P.lambdaR P.lambdaB εr εb α
        (factorCoberturaCuadrado mr mb Cr Cb εr εb))
    (haB : P.regularizadorB =
      pesoRegularizacionIgual P.lambdaR P.lambdaB εr εb α
        (factorCoberturaCuadrado mr mb Cr Cb εr εb)) :
    P.perdidaPoblacional hm ≤
      factorCoberturaCuadrado mr mb Cr Cb εr εb *
        (pesoRegularizacionIgual P.lambdaR P.lambdaB εr εb α
          (factorCoberturaCuadrado mr mb Cr Cb εr εb) * Rstar) +
      3 * P.lambdaR * εr ^ (2 * α) * Sf ^ 2 +
      3 * P.lambdaB * εb ^ (2 * α) * Sg ^ 2 := by
  let Cm := factorCoberturaCuadrado mr mb Cr Cb εr εb
  let a := pesoRegularizacionIgual P.lambdaR P.lambdaB εr εb α Cm
  have hCm : 0 < Cm := by
    have hr : 0 < Cr * (mr : ℝ) * εr ^ 2 :=
      mul_pos (mul_pos hCr (Nat.cast_pos.mpr P.mr_pos)) (sq_pos_of_pos hεr)
    dsimp [Cm, factorCoberturaCuadrado]
    exact mul_pos (by norm_num) (lt_of_lt_of_le hr (le_max_left _ _))
  have hwrPos : 0 < pesoCobertura P.lambdaR εr α Cm := by
    unfold pesoCobertura
    exact div_pos (mul_pos (mul_pos (by norm_num) P.lambdaR_pos)
      (Real.rpow_pos_of_pos hεr _)) hCm
  have ha : 0 < a :=
    lt_of_lt_of_le hwrPos (pesoInterior_le_igual P.lambdaR P.lambdaB εr εb α Cm)
  have hreg := P.regularidad_minimizador_le_comparador Hm hm g hmin hg
    a ha haR haB
  have hemp := P.perdidaEmpirica_le_regularidad_uniforme Hm hm g hmin hg
    a Rstar ha haR haB hRstar
  have hcomp := P.comparacion_con_interpolador Hm hm g hmin hg a haR haB
  have hweighted :
      P.perdidaEmpirica hm +
        pesoCobertura P.lambdaR εr α Cm * P.regularidadInterior hm +
        pesoCobertura P.lambdaB εb α Cm * P.regularidadFrontera hm ≤
      P.perdidaEmpirica hm + a * P.regularidadTotal hm := by
    have hr := mul_le_mul_of_nonneg_right
      (pesoInterior_le_igual P.lambdaR P.lambdaB εr εb α Cm)
      (sq_nonneg (P.seminormaL hm))
    have hb := mul_le_mul_of_nonneg_right
      (pesoFrontera_le_igual P.lambdaR P.lambdaB εr εb α Cm)
      (sq_nonneg (P.seminormaB hm))
    unfold ProblemaPINN.regularidadTotal ProblemaPINN.regularidadInterior
      ProblemaPINN.regularidadFrontera
    nlinarith
  have htotal :
      P.perdidaEmpirica hm +
        pesoCobertura P.lambdaR εr α Cm * P.regularidadInterior hm +
        pesoCobertura P.lambdaB εb α Cm * P.regularidadFrontera hm ≤
      a * Rstar :=
    (hweighted.trans hcomp).trans (mul_le_mul_of_nonneg_left hRstar ha.le)
  have hObj := objetivoCoberturaIntegral_de_hipotesis P Hm U Gamma hU hGamma
    hμr hμb α εr εb εr₀ εb₀ Cr Cb Sf Sg hα hεr hεb hεr₀ hεb₀
    hCr hCb hsr hsb hcoverR hcoverB hmassR hmassB hHolder hm hmin.1 hint
  change P.perdidaPoblacional hm ≤
    Cm * (P.perdidaEmpirica hm +
      pesoCobertura P.lambdaR εr α Cm * P.regularidadInterior hm +
      pesoCobertura P.lambdaB εb α Cm * P.regularidadFrontera hm) +
    3 * P.lambdaR * εr ^ (2 * α) * Sf ^ 2 +
    3 * P.lambdaB * εb ^ (2 * α) * Sg ^ 2 at hObj
  change P.perdidaPoblacional hm ≤ Cm * (a * Rstar) +
    3 * P.lambdaR * εr ^ (2 * α) * Sf ^ 2 +
    3 * P.lambdaB * εb ^ (2 * α) * Sg ^ 2
  have hmul := mul_le_mul_of_nonneg_left htotal hCm.le
  nlinarith

#print axioms TesisPINN.integral_le_suma_celdas
#print axioms TesisPINN.residuo_puntual_en_celda
#print axioms TesisPINN.suma_masas_celdas
#print axioms TesisPINN.medidaReal_celdaVoronoi_le
#print axioms TesisPINN.integral_residuo_le_cobertura
#print axioms TesisPINN.perdidaPoblacional_le_sumas_cobertura
#print axioms TesisPINN.objetivoCoberturaIntegral_de_hipotesis
#print axioms TesisPINN.perdidaPoblacional_minimizador_bajo_cobertura

end TesisPINN
