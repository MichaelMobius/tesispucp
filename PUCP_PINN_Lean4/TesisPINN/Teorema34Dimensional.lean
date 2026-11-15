import TesisPINN.CoberturaDimensional
import TesisPINN.Teorema34

/-! Teorema 3.4 con exponentes de masa y factor geométrico parametrizados. -/

noncomputable section

namespace TesisPINN

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- Datos geométricos y de ley utilizados por la cobertura dimensional. -/
structure DatosMasaDimensional {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (U : Set X) (D s ε₀ : ℝ) where
  c : ℝ
  C : ℝ
  c_pos : 0 < c
  C_pos : 0 < C
  medible : MeasurableSet U
  acotado : Bornology.IsBounded U
  concentrada : μ Uᶜ = 0
  superior : MasaBolaSuperior μ U ε₀ C s
  particiones : ParticionesOcupacionLog μ U D c s ε₀

def DatosMasa38.toDimensional {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {μ : Measure X} {U : Set X} {s ε₀ : ℝ} (a : DatosMasa38 μ U s ε₀) :
    DatosMasaDimensional μ U (Real.sqrt 2) s ε₀ where
  c := a.c
  C := a.C
  c_pos := a.c_pos
  C_pos := a.C_pos
  medible := a.medible
  acotado := a.acotado
  concentrada := a.concentrada
  superior := a.superior
  particiones := a.particiones.particionesOcupacionLog

def DatosMasaDimensional.reindexar {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {μ : Measure X} {U : Set X} {D s t ε₀ : ℝ} (h : s = t)
    (a : DatosMasaDimensional μ U D s ε₀) : DatosMasaDimensional μ U D t ε₀ := h ▸ a

@[simp] theorem DatosMasaDimensional.reindexar_c {X : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {U : Set X} {D s t ε₀ : ℝ}
    (h : s = t) (a : DatosMasaDimensional μ U D s ε₀) : (a.reindexar h).c = a.c := by
  cases h
  rfl

@[simp] theorem DatosMasaDimensional.reindexar_C {X : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {U : Set X} {D s t ε₀ : ℝ}
    (h : s = t) (a : DatosMasaDimensional μ U D s ε₀) : (a.reindexar h).C = a.C := by
  cases h
  rfl

def radioRaizDimensional (D c s : ℝ) (m : ℕ) : ℝ := D * escalaAuxiliarRaiz c s m

theorem radioRaizDimensional_eq (D c s : ℝ) (m : ℕ)
    (hc : 0 < c) (hs : 0 < s) (hm : 0 < m) :
    radioRaizDimensional D c s m =
      D * c ^ (-(1 / s)) * (m : ℝ) ^ (-(1 / (2 * s))) := by
  rw [radioRaizDimensional, escalaAuxiliarRaiz_eq_potencias _ _ _ hc hs hm, mul_assoc]

theorem radioRaizDimensional_pos (D c s : ℝ) (m : ℕ) (hD : 0 < D) (hc : 0 < c) (hm : 0 < m) :
    0 < radioRaizDimensional D c s m := by
  have h : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  unfold radioRaizDimensional escalaAuxiliarRaiz
  positivity

theorem radioRaizDimensional_potencia (D c s a : ℝ) (m : ℕ)
    (hD : 0 ≤ D) (hc : 0 < c) (hs : 0 < s) (hm : 0 < m) :
    radioRaizDimensional D c s m ^ a =
      (D * c ^ (-(1 / s))) ^ a * (m : ℝ) ^ (-(a / (2 * s))) := by
  rw [radioRaizDimensional, escalaAuxiliarRaiz_eq_potencias _ _ _ hc hs hm, ← mul_assoc,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (Nat.cast_nonneg m)]
  congr 1
  ring

def factorCoberturaDimensional (mr mb : ℕ) (Cr Cb rr rb sr sb : ℝ) : ℝ :=
  3 * max (Cr * (mr : ℝ) * rr ^ sr) (Cb * (mb : ℝ) * rb ^ sb)

theorem factorCoberturaDimensional_pos (mr mb : ℕ) (Cr Cb rr rb sr sb : ℝ)
    (hmr : 0 < mr) (hCr : 0 < Cr) (hr : 0 < rr) :
    0 < factorCoberturaDimensional mr mb Cr Cb rr rb sr sb := by
  have hm : (0 : ℝ) < mr := Nat.cast_pos.mpr hmr
  exact mul_pos (by norm_num) ((show 0 < Cr * (mr : ℝ) * rr ^ sr by positivity).trans_le (le_max_left _ _))

theorem factorCoberturaDimensional_raiz (mr mb : ℕ) (D Cr Cb cr cb sr sb : ℝ)
    (hD : 0 ≤ D) (hcr : 0 < cr) (hcb : 0 < cb) (hsr : 0 < sr) (hsb : 0 < sb)
    (hmr : 0 < mr) (hmb : 0 < mb) :
    factorCoberturaDimensional mr mb Cr Cb (radioRaizDimensional D cr sr mr)
      (radioRaizDimensional D cb sb mb) sr sb =
    3 * max (Cr / cr * D ^ sr * Real.sqrt mr) (Cb / cb * D ^ sb * Real.sqrt mb) := by
  have h (m : ℕ) (c C s : ℝ) (hc : 0 < c) (hs : 0 < s) (hm : 0 < m) :
      C * (m : ℝ) * radioRaizDimensional D c s m ^ s = C / c * D ^ s * Real.sqrt m := by
    have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hroot : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm'
    have hmass := escalaAuxiliarRaiz_masa c s m hc hs hm
    rw [radioRaizDimensional, Real.mul_rpow hD (by
      unfold escalaAuxiliarRaiz
      positivity)]
    rw [show escalaAuxiliarRaiz c s m ^ s = (1 / Real.sqrt (m : ℝ)) / c from
      (eq_div_iff hc.ne').2 (by simpa [mul_comm] using hmass)]
    field_simp
    rw [Real.sq_sqrt hm'.le]
    ring
  unfold factorCoberturaDimensional
  rw [h mr cr Cr sr hcr hsr hmr, h mb cb Cb sb hcb hsb hmb]

theorem factorCoberturaDimensional_dim2 (mr mb : ℕ) (Cr Cb rr rb : ℝ) :
    factorCoberturaDimensional mr mb Cr Cb rr rb 2 1 =
      factorCoberturaCuadrado mr mb Cr Cb rr rb := by
  simp [factorCoberturaDimensional, factorCoberturaCuadrado, Real.rpow_two]

theorem factorCoberturaRaizDimensional_dim2 (mr mb : ℕ) (Cr Cb cr cb : ℝ)
    (hcr : 0 < cr) (hcb : 0 < cb) (hmr : 0 < mr) (hmb : 0 < mb) :
    factorCoberturaDimensional mr mb Cr Cb (radioRaizDimensional (Real.sqrt 2) cr 2 mr)
      (radioRaizDimensional (Real.sqrt 2) cb 1 mb) 2 1 = factor34 mr mb Cr Cb cr cb :=
  (factorCoberturaDimensional_dim2 _ _ _ _ _ _).trans
    (factorCoberturaCuadrado_radio34 _ _ _ _ _ _ hcr hcb hmr hmb)

/-- C' de (3.9), en una factorización equivalente de la potencia del radio. -/
def constante34Dimensional (D cr cb sr sb lr lb α Sf Sg : ℝ) : ℝ :=
  3 * max (lr * (D * cr ^ (-(1 / sr))) ^ (2 * α) * Sf ^ 2)
    (lb * (D * cb ^ (-(1 / sb))) ^ (2 * α) * Sg ^ 2)

theorem constante34Dimensional_eq (D cr cb sr sb lr lb α Sf Sg : ℝ)
    (hD : 0 ≤ D) (hcr : 0 < cr) (hcb : 0 < cb) :
    constante34Dimensional D cr cb sr sb lr lb α Sf Sg =
      3 * D ^ (2 * α) * max (lr * cr ^ (-(2 * α / sr)) * Sf ^ 2)
        (lb * cb ^ (-(2 * α / sb)) * Sg ^ 2) := by
  have hd := Real.rpow_nonneg hD (2 * α)
  have h (c s l S : ℝ) (hc : 0 < c) :
      l * (D * c ^ (-(1 / s))) ^ (2 * α) * S ^ 2 =
        D ^ (2 * α) * (l * c ^ (-(2 * α / s)) * S ^ 2) := by
    rw [Real.mul_rpow hD (by positivity), ← Real.rpow_mul hc.le,
      show -(1 / s) * (2 * α) = -(2 * α / s) by ring]
    ring
  unfold constante34Dimensional
  rw [h cr sr lr Sf hcr, h cb sb lb Sg hcb, ← mul_max_of_nonneg _ _ hd]
  ring

theorem datos34Dimensional_le (D cr cb sr sb lr lb α Sf Sg : ℝ)
    (mr mb : ℕ) (hD : 0 ≤ D) (hcr : 0 < cr) (hcb : 0 < cb)
    (hsr : 0 < sr) (hsb : 0 < sb) (hmr : 0 < mr) (hmb : 0 < mb) :
    3 * lr * radioRaizDimensional D cr sr mr ^ (2 * α) * Sf ^ 2 +
      3 * lb * radioRaizDimensional D cb sb mb ^ (2 * α) * Sg ^ 2 ≤
      constante34Dimensional D cr cb sr sb lr lb α Sf Sg *
        ((mr : ℝ) ^ (-(α / sr)) + (mb : ℝ) ^ (-(α / sb))) := by
  rw [radioRaizDimensional_potencia _ _ _ _ _ hD hcr hsr hmr,
    radioRaizDimensional_potencia _ _ _ _ _ hD hcb hsb hmb]
  rw [show 2 * α / (2 * sr) = α / sr by ring,
    show 2 * α / (2 * sb) = α / sb by ring]
  unfold constante34Dimensional
  have hr := mul_le_mul_of_nonneg_right
    (le_max_left (lr * (D * cr ^ (-(1 / sr))) ^ (2 * α) * Sf ^ 2)
      (lb * (D * cb ^ (-(1 / sb))) ^ (2 * α) * Sg ^ 2))
    (Real.rpow_nonneg (Nat.cast_nonneg mr) (-(α / sr)))
  have hb := mul_le_mul_of_nonneg_right
    (le_max_right (lr * (D * cr ^ (-(1 / sr))) ^ (2 * α) * Sf ^ 2)
      (lb * (D * cb ^ (-(1 / sb))) ^ (2 * α) * Sg ^ 2))
    (Real.rpow_nonneg (Nat.cast_nonneg mb) (-(α / sb)))
  linarith only [hr, hb]

/-- Funcional con (3.7) en modo separado y con (3.23) en modo igual. -/
def Operadores38.problemaDimensional {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (op : Operadores38 H X Y) (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] {mr mb : ℕ} (hmr : 0 < mr) (hmb : 0 < mb)
    (lr lb α rr rb F : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hr : 0 < rr) (hb : 0 < rb)
    (hF : 0 < F) (iguales : Bool) (xr : Fin mr → X) (xb : Fin mb → Y) :
    ProblemaPINN H X Y mr mb :=
  let ar := pesoCobertura lr rr α F
  let ab := pesoCobertura lb rb α F
  have hra : 0 ≤ ar := pesoCobertura_nonneg _ _ _ _ hlr.le hr.le hF.le
  have hba : 0 ≤ ab := pesoCobertura_nonneg _ _ _ _ hlb.le hb.le hF.le
  { L := op.L, B := op.B, f := op.f, g := op.g, xr := xr, xb := xb, μr := μr, μb := μb
    μr_prob := measure_univ, μb_prob := measure_univ
    seminormaL := op.seminormaL, seminormaB := op.seminormaB
    lambdaR := lr, lambdaB := lb
    regularizadorR := if iguales then max ar ab else ar
    regularizadorB := if iguales then max ar ab else ab
    mr_pos := hmr, mb_pos := hmb, lambdaR_pos := hlr, lambdaB_pos := hlb
    regularizadorR_nonneg := by cases iguales <;> simp [hra, hba]
    regularizadorB_nonneg := by cases iguales <;> simp [hra, hba] }

def CoberturaDimensional {H X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] {mr mb : ℕ}
    (P : ProblemaPINN H X Y mr mb) (U : Set X) (Γ : Set Y) (rr rb : ℝ) : Prop :=
  (∀ i, P.xr i ∈ U) ∧ (∀ i, P.xb i ∈ Γ) ∧
    MuestrasCubren U P.xr rr ∧ MuestrasCubren Γ P.xb rb

/-- Absorción de (3.13) para dos exponentes y radios independientes. -/
theorem cota34_dimensional_bajo_cobertura
    {H X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (μr : Measure X) [IsProbabilityMeasure μr] (μb : Measure Y) [IsProbabilityMeasure μb]
    (U : Set X) (Γ : Set Y) (D sr sb ε₀ : ℝ)
    (dr : DatosMasaDimensional μr U D sr ε₀) (db : DatosMasaDimensional μb Γ D sb ε₀)
    (op : Operadores38 H X Y) (Hm : Set H)
    {mr mb : ℕ} (hmr : 0 < mr) (hmb : 0 < mb)
    (lr lb α Sf Sg rr rb : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (hr : 0 < rr) (hb : 0 < rb) (hr₀ : rr ≤ ε₀) (hb₀ : rb ≤ ε₀)
    (iguales : Bool) (xr : Fin mr → X) (xb : Fin mb → Y) :
    let F := factorCoberturaDimensional mr mb dr.C db.C rr rb sr sb
    let P := op.problemaDimensional μr μb hmr hmb lr lb α rr rb F hlr hlb hr hb
      (factorCoberturaDimensional_pos _ _ _ _ _ _ _ _ hmr dr.C_pos hr) iguales xr xb
    op.CotasHolder34 Hm U Γ α Sf Sg → CoberturaDimensional P U Γ rr rb →
    ∀ h ∈ Hm, P.perdidaPoblacional h ≤ F * P.funcionalRegularizado h +
      3 * lr * rr ^ (2 * α) * Sf ^ 2 + 3 * lb * rb ^ (2 * α) * Sg ^ 2 := by
  intro F P hh hcov h hmem
  obtain ⟨hsr, hsb, hcr, hcb⟩ := hcov
  have hholder : CotasHolder P Hm U Γ α Sf Sg := hh
  have hcand := hh.2.2.1 h hmem
  have hInt : P.PoblacionIntegrable h :=
    poblacionIntegrable_de_holder_acotado P Hm U Γ dr.acotado db.acotado
      (soporte_no_vacio μr U dr.concentrada) (soporte_no_vacio μb Γ db.concentrada)
      dr.concentrada db.concentrada α Sf Sg hα hholder h hmem
      (aestronglyMeasurable_residuo_sq_de_continuidad μr U dr.medible dr.concentrada _ _
        (continuo_de_cota_holder U _ _ α hα hcand.2.2.1)
        (continuo_de_cota_holder U _ Sf α hα hh.2.2.2.1))
      (aestronglyMeasurable_residuo_sq_de_continuidad μb Γ db.medible db.concentrada _ _
        (continuo_de_cota_holder Γ _ _ α hα hcand.2.2.2)
        (continuo_de_cota_holder Γ _ Sg α hα hh.2.2.2.2))
  have hsum := perdidaPoblacional_le_sumas_dimensional P Hm U Γ dr.medible db.medible
    dr.concentrada db.concentrada α rr rb ε₀ ε₀ dr.C db.C Sf Sg sr sb hα hr hb hr₀ hb₀
    dr.C_pos.le db.C_pos.le hsr hsb hcr hcb dr.superior db.superior hholder h hmem hInt
  simp only [cuadrado_holder _ _ _ hr.le, cuadrado_holder _ _ _ hb.le] at hsum
  have hF : 0 < F := factorCoberturaDimensional_pos _ _ _ _ _ _ _ _ hmr dr.C_pos hr
  have hfR : 3 * dr.C * (mr : ℝ) * rr ^ sr ≤ F := by
    unfold F factorCoberturaDimensional
    have := mul_le_mul_of_nonneg_left (le_max_left (dr.C * (mr : ℝ) * rr ^ sr)
      (db.C * (mb : ℝ) * rb ^ sb)) (by norm_num : (0 : ℝ) ≤ 3)
    linarith only [this]
  have hfB : 3 * db.C * (mb : ℝ) * rb ^ sb ≤ F := by
    unfold F factorCoberturaDimensional
    have := mul_le_mul_of_nonneg_left (le_max_right (dr.C * (mr : ℝ) * rr ^ sr)
      (db.C * (mb : ℝ) * rb ^ sb)) (by norm_num : (0 : ℝ) ≤ 3)
    linarith only [this]
  have ar : pesoCobertura lr rr α F ≤ P.regularizadorR := by
    cases iguales
    · exact le_rfl
    · exact le_max_left _ _
  have ab : pesoCobertura lb rb α F ≤ P.regularizadorB := by
    cases iguales
    · exact le_rfl
    · exact le_max_right _ _
  have hregR := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ar hF.le)
    (sq_nonneg (P.seminormaL h))
  have hregB := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ab hF.le)
    (sq_nonneg (P.seminormaB h))
  rw [pesoCobertura, mul_div_cancel₀ _ hF.ne'] at hregR hregB
  have hmR : (mr : ℝ) ≠ 0 := (Nat.cast_pos.mpr hmr).ne'
  have hmB : (mb : ℝ) ≠ 0 := (Nat.cast_pos.mpr hmb).ne'
  have heR := mul_le_mul_of_nonneg_right hfR (P.perdidaEmpiricaInterior_nonneg h)
  have heB := mul_le_mul_of_nonneg_right hfB (P.perdidaEmpiricaFrontera_nonneg h)
  have hexR : (3 * dr.C * (mr : ℝ) * rr ^ sr) * P.perdidaEmpiricaInterior h =
      lr * (3 * dr.C * rr ^ sr * ∑ i, (P.L h (P.xr i) - P.f (P.xr i)) ^ 2) := by
    have he : P.lambdaR = lr := rfl
    rw [ProblemaPINN.perdidaEmpiricaInterior, he]
    field_simp
  have hexB : (3 * db.C * (mb : ℝ) * rb ^ sb) * P.perdidaEmpiricaFrontera h =
      lb * (3 * db.C * rb ^ sb * ∑ i, (P.B h (P.xb i) - P.g (P.xb i)) ^ 2) := by
    have he : P.lambdaB = lb := rfl
    rw [ProblemaPINN.perdidaEmpiricaFrontera, he]
    field_simp
  rw [hexR] at heR
  rw [hexB] at heB
  change P.perdidaPoblacional h ≤ lr * _ + lb * _ at hsum
  unfold ProblemaPINN.funcionalRegularizado ProblemaPINN.perdidaEmpirica
    ProblemaPINN.regularidadInterior ProblemaPINN.regularidadFrontera
  linarith only [hsum, heR, heB, hregR, hregB]

/-- Los radios (3.5) determinan el mismo funcional en las pruebas de evento
finito y en la sucesión de prefijos. -/
def Operadores38.problemaRaizDimensional
    {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (op : Operadores38 H X Y) (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] {mr mb : ℕ} (hmr : 0 < mr) (hmb : 0 < mb)
    (D sr sb Cr Cb cr cb lr lb α : ℝ)
    (hD : 0 < D) (hCr : 0 < Cr) (hcr : 0 < cr) (hcb : 0 < cb)
    (hlr : 0 < lr) (hlb : 0 < lb) (igual : Bool)
    (xr : Fin mr → X) (xb : Fin mb → Y) : ProblemaPINN H X Y mr mb :=
  let r := radioRaizDimensional D cr sr mr
  let b := radioRaizDimensional D cb sb mb
  have hr : 0 < r := radioRaizDimensional_pos _ _ _ _ hD hcr hmr
  have hb : 0 < b := radioRaizDimensional_pos _ _ _ _ hD hcb hmb
  op.problemaDimensional μr μb hmr hmb lr lb α r b
    (factorCoberturaDimensional mr mb Cr Cb r b sr sb) hlr hlb hr hb
    (factorCoberturaDimensional_pos _ _ _ _ _ _ _ _ hmr hCr hr) igual xr xb

def falloRaiz34 (m : ℕ) : ℝ :=
  Real.sqrt (m : ℝ) * (1 - 1 / Real.sqrt (m : ℝ)) ^ m

theorem escala_le_de_radio_dimensional (D η ε₀ : ℝ) (hD : 1 ≤ D)
    (hη : 0 < η) (hr : D * η ≤ ε₀) : η ≤ ε₀ :=
  (le_mul_of_one_le_left hη.le hD).trans hr

theorem evento_raiz_dimensional
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [PseudoMetricSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure X) [IsProbabilityMeasure μ]
    (Z : Muestreo38 P μ) (U : Set X) (D s ε₀ : ℝ)
    (dm : DatosMasaDimensional μ U D s ε₀) (hD : 1 ≤ D) (hs : 0 < s)
    (m : ℕ) (hm : 0 < m) (hsmall : radioRaizDimensional D dm.c s m ≤ ε₀) :
    ∃ A : Set Ω, MeasurableSet A ∧ P.real Aᶜ ≤ falloRaiz34 m ∧
      ∀ ω ∈ A, MuestrasCubren U (fun i : Fin m => Z.Z i ω) (radioRaizDimensional D dm.c s m) := by
  let η := escalaAuxiliarRaiz dm.c s m
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hc := dm.c_pos
  have hη : 0 < η := by unfold η escalaAuxiliarRaiz; positivity
  obtain ⟨k, cells, hmeas, hdis, hcov, _, hmass, hdiam⟩ :=
    dm.particiones η hη (escala_le_de_radio_dimensional D η ε₀ hD hη hsmall)
  have hmin (i : Fin k) : 1 / Real.sqrt (m : ℝ) ≤ μ.real (cells i) :=
    (escalaAuxiliarRaiz_masa dm.c s m dm.c_pos hs hm).symm.trans_le (hmass i)
  obtain ⟨A, hA, hk, hprob, _, hcover⟩ := lema36_cobertura_dimensional P μ Z.Z Z.medible
    Z.indep Z.ley m k cells hmeas (solapamiento_nulo_de_disjuntas μ cells hdis)
    U hcov D η (1 / Real.sqrt m) hdiam hmin
  have hroot := Real.sqrt_pos.2 hm'
  have hk' : (k : ℝ) ≤ Real.sqrt m := by
    apply (div_le_one hroot).1
    simpa [div_eq_mul_inv] using hk
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : 1 ≤ Real.sqrt (m : ℝ) := by simpa using Real.sqrt_le_sqrt hm1
  have hp : 1 / Real.sqrt (m : ℝ) ≤ 1 := (div_le_one hroot).2 h1
  have hle := mul_le_mul_of_nonneg_right hk' (pow_nonneg (sub_nonneg.2 hp) m)
  refine ⟨A, hA, ?_, hcover⟩
  rw [probReal_compl_eq_one_sub hA]
  unfold falloRaiz34
  linarith

/-- El evento común solo depende de los prefijos, en ambas leyes. -/
theorem evento_cobertura34_dimensional
    {Ω X Y : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] (U : Set X) (Γ : Set Y) (D sr sb ε₀ : ℝ)
    (dr : DatosMasaDimensional μr U D sr ε₀) (db : DatosMasaDimensional μb Γ D sb ε₀)
    (Zr : Muestreo38 P μr) (Zb : Muestreo38 P μb)
    (hD : 1 ≤ D) (hsr : 0 < sr) (hsb : 0 < sb)
    (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (hr : radioRaizDimensional D dr.c sr mr ≤ ε₀) (hb : radioRaizDimensional D db.c sb mb ≤ ε₀) :
    ∃ A : Set Ω, MeasurableSet A ∧ 1 - falloRaiz34 mr - falloRaiz34 mb ≤ P.real A ∧
      ∀ ω ∈ A, (∀ i : Fin mr, Zr.Z i ω ∈ U) ∧ (∀ i : Fin mb, Zb.Z i ω ∈ Γ) ∧
        MuestrasCubren U (fun i : Fin mr => Zr.Z i ω) (radioRaizDimensional D dr.c sr mr) ∧
        MuestrasCubren Γ (fun i : Fin mb => Zb.Z i ω) (radioRaizDimensional D db.c sb mb) := by
  obtain ⟨Ar, hAr, hpR, hcR⟩ := evento_raiz_dimensional P μr Zr U D sr ε₀ dr hD hsr mr hmr hr
  obtain ⟨Ab, hAb, hpB, hcB⟩ := evento_raiz_dimensional P μb Zb Γ D sb ε₀ db hD hsb mb hmb hb
  let Sr := muestrasEnSoporte Zr.Z mr U
  let Sb := muestrasEnSoporte Zb.Z mb Γ
  have hSr : MeasurableSet Sr := muestrasEnSoporte_measurable Zr.Z mr U dr.medible Zr.medible
  have hSb : MeasurableSet Sb := muestrasEnSoporte_measurable Zb.Z mb Γ db.medible Zb.medible
  have hsR : P.real Srᶜ = 0 := medidaReal_fallo_soporte P μr Zr.Z mr U dr.concentrada Zr.medible Zr.ley
  have hsB : P.real Sbᶜ = 0 := medidaReal_fallo_soporte P μb Zb.Z mb Γ db.concentrada Zb.medible Zb.ley
  have h := probReal_inter_cuatro_ge P Ar Ab Sr Sb hAr hAb hSr hSb
  refine ⟨(Ar ∩ Ab) ∩ (Sr ∩ Sb), (hAr.inter hAb).inter (hSr.inter hSb), by linarith, ?_⟩
  rintro ω ⟨⟨hr', hb'⟩, hr'', hb''⟩
  exact ⟨hr'', hb'', hcR ω hr', hcB ω hb'⟩

theorem teorema34_dimensional
    {Ω H X Y : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] (U : Set X) (Γ : Set Y) (d : ℕ) (hd : 2 ≤ d) (ε₀ : ℝ)
    (dr : DatosMasaDimensional μr U (Real.sqrt d) d ε₀)
    (db : DatosMasaDimensional μb Γ (Real.sqrt d) ((d : ℝ) - 1) ε₀)
    (Zr : Muestreo38 P μr) (Zb : Muestreo38 P μb) (op : Operadores38 H X Y) (Hm : Set H)
    (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (lr lb α Sf Sg : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (hradR : radioRaizDimensional (Real.sqrt d) dr.c d mr ≤ ε₀)
    (hradB : radioRaizDimensional (Real.sqrt d) db.c ((d : ℝ) - 1) mb ≤ ε₀)
    (hHolder : op.CotasHolder34 Hm U Γ α Sf Sg) :
    let D := Real.sqrt d
    let s := (d : ℝ) - 1
    have hD : 0 < D := Real.sqrt_pos.2 (Nat.cast_pos.mpr (by omega))
    let rr := radioRaizDimensional D dr.c d mr
    let rb := radioRaizDimensional D db.c s mb
    let F := factorCoberturaDimensional mr mb dr.C db.C rr rb d s
    let Pω := fun ω => op.problemaRaizDimensional μr μb hmr hmb D d s dr.C db.C dr.c db.c lr lb α
      hD dr.C_pos dr.c_pos db.c_pos hlr hlb false (fun i => Zr.Z i ω) (fun i => Zb.Z i ω)
    ∃ A : Set Ω, MeasurableSet A ∧ 1 - falloRaiz34 mr - falloRaiz34 mb ≤ P.real A ∧
      ∀ ω ∈ A, ∀ h ∈ Hm, (Pω ω).perdidaPoblacional h ≤
        F * (Pω ω).funcionalRegularizado h +
        constante34Dimensional D dr.c db.c d s lr lb α Sf Sg *
          ((mr : ℝ) ^ (-(α / (d : ℝ))) + (mb : ℝ) ^ (-(α / s))) := by
  intro D s hD rr rb F Pω
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hD' : 1 ≤ D := by
    have h : (1 : ℝ) ≤ d := by linarith
    simpa [D] using Real.sqrt_le_sqrt h
  have hs : 0 < s := by dsimp [s]; linarith
  have hdpos : (0 : ℝ) < d := by linarith
  obtain ⟨A, hA, hp, hc⟩ := evento_cobertura34_dimensional P μr μb U Γ D d s ε₀ dr db Zr Zb
    hD' hdpos hs mr mb hmr hmb hradR hradB
  refine ⟨A, hA, hp, fun ω hω h hh => ?_⟩
  have h := cota34_dimensional_bajo_cobertura μr μb U Γ D d s ε₀ dr db op Hm hmr hmb
    lr lb α Sf Sg rr rb hlr hlb hα (radioRaizDimensional_pos _ _ _ _ hD dr.c_pos hmr)
    (radioRaizDimensional_pos _ _ _ _ hD db.c_pos hmb) hradR hradB false
    (fun i => Zr.Z i ω) (fun i => Zb.Z i ω) hHolder (hc ω hω) h hh
  have hdata := datos34Dimensional_le D dr.c db.c d s lr lb α Sf Sg mr mb
    hD.le dr.c_pos db.c_pos hdpos hs hmr hmb
  change (Pω ω).perdidaPoblacional _ ≤ F * (Pω ω).funcionalRegularizado _ +
    3 * lr * rr ^ (2 * α) * Sf ^ 2 + 3 * lb * rb ^ (2 * α) * Sg ^ 2 at h
  change 3 * lr * rr ^ (2 * α) * Sf ^ 2 + 3 * lb * rb ^ (2 * α) * Sg ^ 2 ≤ _ at hdata
  exact h.trans (by linarith only [hdata])

/-- Identificación del problema de pesos mínimos con la interfaz 2D anterior. -/
theorem problemaRaizDimensional_dim2
    {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (op : Operadores38 H X Y) (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] (mr mb : ℕ)
    (hmr : 0 < mr) (hmb : 0 < mb)
    (Cr Cb cr cb lr lb α : ℝ) (hCr : 0 < Cr) (hcr : 0 < cr) (hcb : 0 < cb)
    (hlr : 0 < lr) (hlb : 0 < lb) (xr : Fin mr → X) (xb : Fin mb → Y) :
    op.problemaRaizDimensional μr μb hmr hmb (Real.sqrt 2) 2 1 Cr Cb cr cb lr lb α
      (by positivity) hCr hcr hcb hlr hlb false xr xb =
    op.problema34 μr μb mr mb hmr hmb Cr Cb cr cb lr lb α hCr hcr hcb hlr hlb xr xb := by
  simp only [Operadores38.problemaRaizDimensional, Operadores38.problemaDimensional,
    Operadores38.problema34, factorCoberturaRaizDimensional_dim2 _ _ _ _ _ _ hcr hcb hmr hmb]
  rfl

theorem teorema34_dim2_de_dimensional
    {Ω H X Y : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (U : Set X) (Γ : Set Y) (ε₀ : ℝ)
    (dr : DatosMasa38 μr U 2 ε₀) (db : DatosMasa38 μb Γ 1 ε₀)
    (sr : Muestreo38 P μr) (sb : Muestreo38 P μb)
    (D : Operadores38 H X Y) (Hadm : Set H)
    (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (lr lb α Sf Sg : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (hradR : radio34 dr.c 2 mr ≤ ε₀) (hradB : radio34 db.c 1 mb ≤ ε₀)
    (hHolder : D.CotasHolder34 Hadm U Γ α Sf Sg) :
    ∃ Ωm : Set Ω, MeasurableSet Ωm ∧
      1 - Real.sqrt (mr : ℝ) * (1 - 1 / Real.sqrt (mr : ℝ)) ^ mr
        - Real.sqrt (mb : ℝ) * (1 - 1 / Real.sqrt (mb : ℝ)) ^ mb ≤ P.real Ωm ∧
      ∀ ω ∈ Ωm, ∀ h ∈ Hadm,
        (D.problema34 μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
            dr.C_pos dr.c_pos db.c_pos hlr hlb
            (fun i => sr.Z i ω) (fun j => sb.Z j ω)).perdidaPoblacional h ≤
          factor34 mr mb dr.C db.C dr.c db.c *
            (D.problema34 μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
              dr.C_pos dr.c_pos db.c_pos hlr hlb
              (fun i => sr.Z i ω) (fun j => sb.Z j ω)).funcionalRegularizado h +
          constante34 lr lb dr.c db.c α Sf Sg *
            ((mr : ℝ) ^ (-(α / 2)) + (mb : ℝ) ^ (-α)) := by
  let db' : DatosMasaDimensional μb Γ (Real.sqrt (↑(2 : ℕ) : ℝ)) ((↑(2 : ℕ) : ℝ) - 1) ε₀ :=
    db.toDimensional.reindexar (by norm_num)
  have hdbC : db'.C = db.C := by simp [db', DatosMasa38.toDimensional]
  have hdbc : db'.c = db.c := by simp [db', DatosMasa38.toDimensional]
  have hb : radioRaizDimensional (Real.sqrt (↑(2 : ℕ) : ℝ)) db'.c ((↑(2 : ℕ) : ℝ) - 1) mb ≤ ε₀ := by
    simpa [hdbc, radioRaizDimensional, radio34, show (2 : ℝ) - 1 = 1 by norm_num] using hradB
  have hr := teorema34_dimensional P μr μb U Γ 2 le_rfl ε₀ dr.toDimensional db' sr sb D Hadm
    mr mb hmr hmb lr lb α Sf Sg hlr hlb hα hradR hb hHolder
  obtain ⟨A, hA, hprob, hc⟩ := hr
  refine ⟨A, hA, hprob, fun ω hω h hh => ?_⟩
  have H := hc ω hω h hh
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, div_one] at H
  have hc' := constante34Dimensional_eq (Real.sqrt 2) dr.c db.c 2 1 lr lb α Sf Sg
    (Real.sqrt_nonneg _) dr.c_pos db.c_pos
  rw [show 2 * α / (2 : ℝ) = α by ring, div_one] at hc'
  simpa only [DatosMasa38.toDimensional, hdbc, hdbC, problemaRaizDimensional_dim2,
    factorCoberturaRaizDimensional_dim2 _ _ _ _ _ _ dr.c_pos db.c_pos hmr hmb,
    hc', constante34] using H

#check teorema34_dimensional
#check teorema34_dim2_de_dimensional
#print axioms teorema34_dim2_de_dimensional
#print axioms factorCoberturaDimensional_raiz
#print axioms radioRaizDimensional_eq
#print axioms constante34Dimensional_eq
#print axioms cota34_dimensional_bajo_cobertura
#print axioms evento_cobertura34_dimensional
#print axioms teorema34_dimensional
#print axioms problemaRaizDimensional_dim2

end TesisPINN
