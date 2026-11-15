import TesisPINN.Lema36
import TesisPINN.Teorema38

/-!
# Teorema 3.4 (Shin–Darbon–Karniadakis, Theorem 3.1) y Lema 3.5 (Lemma B.1)

Cota de generalización uniforme por cobertura, en dimensión dos: masa interior
de exponente `2`, masa de frontera de exponente `1` y factor geométrico `√2`.

* `lema35_dim2` es el Lema 3.5: la desigualdad determinista (3.13) bajo un
  evento de cobertura, para todos los candidatos de la clase a la vez.
* `teorema34_dim2` es el Teorema 3.4: existe un evento medible `Ω_m`,
  determinado por las muestras, con la probabilidad (3.10), sobre el cual la
  desigualdad (3.11) vale simultáneamente para todo candidato admisible.

Las cantidades se escriben con las fórmulas de la tesis para `d = 2`:
`radio34` es (3.5), `factor34` es (3.6), los pesos de `problema34` son (3.7) y
`constante34` es (3.9). Los lemas `factorCoberturaCuadrado_radio34`,
`radio34_potencia_interior` y `radio34_potencia_frontera` las identifican con
las expresiones que usa la maquinaria (`factorCoberturaCuadrado`,
`escalaAuxiliarRaiz`).

No se supone independencia entre el muestreo interior y el de frontera: las dos
sucesiones viven en el mismo espacio de probabilidad y solo se usa la cota de
unión. El caso unidimensional del enunciado de la tesis no se trata aquí.
-/

noncomputable section

namespace TesisPINN

open MeasureTheory ProbabilityTheory

/-! ## Constantes del enunciado en la notación de la tesis -/

/-- Radio de cobertura (3.5) con `√d = √2`:
`ε = √2 · c^{-1/s} · m^{-1/(2s)}`, con `s = 2` en el interior y `s = 1` en la
frontera. Se define mediante la escala auxiliar `η = ε/√2` de la maquinaria;
`radio34_eq` da la fórmula de la tesis. -/
def radio34 (c s : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt 2 * escalaAuxiliarRaiz c s m

theorem radio34_eq (c s : ℝ) (m : ℕ) (hc : 0 < c) (hs : 0 < s) (hm : 0 < m) :
    radio34 c s m =
      Real.sqrt 2 * c ^ (-(1 / s)) * (m : ℝ) ^ (-(1 / (2 * s))) := by
  unfold radio34
  rw [escalaAuxiliarRaiz_eq_potencias c s m hc hs hm, mul_assoc]

theorem radio34_pos (c s : ℝ) (m : ℕ) (hc : 0 < c) (hm : 0 < m) :
    0 < radio34 c s m := by
  unfold radio34
  exact radio38_pos c s m hc hm

/-- La escala auxiliar `η = ε/√2` es positiva y no excede `ε₀` cuando el radio
final `ε` pertenece a `(0, ε₀]`. -/
theorem escala_le_de_radio (η ε₀ : ℝ) (hp : 0 < Real.sqrt 2 * η)
    (h : Real.sqrt 2 * η ≤ ε₀) : 0 < η ∧ η ≤ ε₀ := by
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hs1 : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hpos : 0 < η := pos_of_mul_pos_right hp hs.le
  exact ⟨hpos, (le_mul_of_one_le_left hpos.le hs1).trans h⟩

/-- Potencia `2α` del radio interior: `ε_r^{2α} = (√2)^{2α} c^{-α} m^{-α/2}`. -/
theorem radio34_potencia_interior (c α : ℝ) (m : ℕ) (hc : 0 < c) (hm : 0 < m) :
    radio34 c 2 m ^ (2 * α) =
      (Real.sqrt 2) ^ (2 * α) * c ^ (-α) * (m : ℝ) ^ (-(α / 2)) := by
  have hexp : -(1 / (2 : ℝ)) * (2 * α) = -α := by ring
  unfold radio34
  rw [radio_cobertura_potencia c 2 α m hc (by norm_num) hm,
    Real.mul_rpow (Real.sqrt_nonneg 2) (Real.rpow_nonneg hc.le _),
    ← Real.rpow_mul hc.le, hexp]

/-- Potencia `2α` del radio de frontera:
`ε_b^{2α} = (√2)^{2α} c^{-2α} m^{-α}`. -/
theorem radio34_potencia_frontera (c α : ℝ) (m : ℕ) (hc : 0 < c) (hm : 0 < m) :
    radio34 c 1 m ^ (2 * α) =
      (Real.sqrt 2) ^ (2 * α) * c ^ (-(2 * α)) * (m : ℝ) ^ (-α) := by
  have hexp : -(1 / (1 : ℝ)) * (2 * α) = -(2 * α) := by ring
  have hexp' : -(α / (1 : ℝ)) = -α := by ring
  unfold radio34
  rw [radio_cobertura_potencia c 1 α m hc (by norm_num) hm,
    Real.mul_rpow (Real.sqrt_nonneg 2) (Real.rpow_nonneg hc.le _),
    ← Real.rpow_mul hc.le, hexp, hexp']

/-- Factor de cobertura (3.6) para `d = 2`:
`C_m = 3 max{(C_r/c_r)(√2)² m_r^{1/2}, (C_b/c_b) √2 m_b^{1/2}}`. -/
def factor34 (mr mb : ℕ) (Cr Cb cr cb : ℝ) : ℝ :=
  3 * max (Cr / cr * (Real.sqrt 2) ^ 2 * Real.sqrt (mr : ℝ))
    (Cb / cb * Real.sqrt 2 * Real.sqrt (mb : ℝ))

theorem factor34_pos (mr mb : ℕ) (Cr Cb cr cb : ℝ)
    (hCr : 0 < Cr) (hcr : 0 < cr) (hmr : 0 < mr) :
    0 < factor34 mr mb Cr Cb cr cb := by
  have hmr' : (0 : ℝ) < mr := Nat.cast_pos.mpr hmr
  have hsr : 0 < Real.sqrt (mr : ℝ) := Real.sqrt_pos.2 hmr'
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h1 : 0 < Cr / cr * (Real.sqrt 2) ^ 2 * Real.sqrt (mr : ℝ) :=
    mul_pos (mul_pos (div_pos hCr hcr) (pow_pos hs2 2)) hsr
  unfold factor34
  exact mul_pos (by norm_num) (h1.trans_le (le_max_left _ _))

private theorem factor_escalar (C c m S q e : ℝ) (hS : 0 < S)
    (hm : m = S * S) (he : e = 1 / S / c) :
    C * m * (q * e) = C / c * q * S := by
  rw [hm, he]
  have h1 : C * (S * S) * (q * (1 / S / c)) = C / c * q * S * (S * S⁻¹) := by
    ring
  rw [h1, mul_inv_cancel₀ hS.ne', mul_one]

/-- El factor `C_m = 3 max{C_r m_r ε_r², C_b m_b ε_b}` del Lema 3.5, evaluado en
los radios (3.5), es el factor (3.6) del Teorema 3.4. -/
theorem factorCoberturaCuadrado_radio34 (mr mb : ℕ) (Cr Cb cr cb : ℝ)
    (hcr : 0 < cr) (hcb : 0 < cb) (hmr : 0 < mr) (hmb : 0 < mb) :
    factorCoberturaCuadrado mr mb Cr Cb (radio34 cr 2 mr) (radio34 cb 1 mb) =
      factor34 mr mb Cr Cb cr cb := by
  have hmr' : (0 : ℝ) < mr := Nat.cast_pos.mpr hmr
  have hmb' : (0 : ℝ) < mb := Nat.cast_pos.mpr hmb
  have hsr : 0 < Real.sqrt (mr : ℝ) := Real.sqrt_pos.2 hmr'
  have hsb : 0 < Real.sqrt (mb : ℝ) := Real.sqrt_pos.2 hmb'
  have hr := escalaAuxiliarRaiz_masa cr 2 mr hcr (by norm_num) hmr
  have hb := escalaAuxiliarRaiz_masa cb 1 mb hcb (by norm_num) hmb
  rw [Real.rpow_two] at hr
  rw [Real.rpow_one] at hb
  have hηr : escalaAuxiliarRaiz cr 2 mr ^ 2 = 1 / Real.sqrt (mr : ℝ) / cr :=
    eq_div_of_mul_eq hcr.ne' (by rw [mul_comm]; exact hr)
  have hηb : escalaAuxiliarRaiz cb 1 mb = 1 / Real.sqrt (mb : ℝ) / cb :=
    eq_div_of_mul_eq hcb.ne' (by rw [mul_comm]; exact hb)
  have hmr2 : (mr : ℝ) = Real.sqrt (mr : ℝ) * Real.sqrt (mr : ℝ) :=
    (Real.mul_self_sqrt hmr'.le).symm
  have hmb2 : (mb : ℝ) = Real.sqrt (mb : ℝ) * Real.sqrt (mb : ℝ) :=
    (Real.mul_self_sqrt hmb'.le).symm
  have e1 : Cr * (mr : ℝ) * (Real.sqrt 2 * escalaAuxiliarRaiz cr 2 mr) ^ 2 =
      Cr / cr * (Real.sqrt 2) ^ 2 * Real.sqrt (mr : ℝ) := by
    rw [mul_pow]
    exact factor_escalar Cr cr (mr : ℝ) (Real.sqrt (mr : ℝ)) ((Real.sqrt 2) ^ 2)
      (escalaAuxiliarRaiz cr 2 mr ^ 2) hsr hmr2 hηr
  have e2 : Cb * (mb : ℝ) * (Real.sqrt 2 * escalaAuxiliarRaiz cb 1 mb) =
      Cb / cb * Real.sqrt 2 * Real.sqrt (mb : ℝ) :=
    factor_escalar Cb cb (mb : ℝ) (Real.sqrt (mb : ℝ)) (Real.sqrt 2)
      (escalaAuxiliarRaiz cb 1 mb) hsb hmb2 hηb
  unfold factorCoberturaCuadrado factor34 radio34
  rw [e1, e2]

/-- Constante (3.9) para `d = 2`:
`C' = 3 (√2)^{2α} max{λ_r c_r^{-α} [f]², λ_b c_b^{-2α} [g]²}`. -/
def constante34 (lr lb cr cb α Sf Sg : ℝ) : ℝ :=
  3 * (Real.sqrt 2) ^ (2 * α) *
    max (lr * cr ^ (-α) * Sf ^ 2) (lb * cb ^ (-(2 * α)) * Sg ^ 2)

private theorem datos34_escalar (q A B r1 r2 : ℝ)
    (hq : 0 ≤ q) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) :
    3 * q * A * r1 + 3 * q * B * r2 ≤ 3 * q * max A B * (r1 + r2) := by
  have hq3 : 0 ≤ 3 * q := mul_nonneg (by norm_num) hq
  have e1 : 3 * q * A * r1 ≤ 3 * q * max A B * r1 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_left A B) hq3) hr1
  have e2 : 3 * q * B * r2 ≤ 3 * q * max A B * r2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_right A B) hq3) hr2
  linarith

/-- Los términos de datos de (3.13), evaluados en los radios (3.5), quedan
acotados por `C' (m_r^{-α/2} + m_b^{-α})`, como en (3.11). -/
theorem datos34_le (lr lb cr cb α Sf Sg : ℝ) (mr mb : ℕ)
    (hcr : 0 < cr) (hcb : 0 < cb) (hmr : 0 < mr) (hmb : 0 < mb) :
    3 * lr * radio34 cr 2 mr ^ (2 * α) * Sf ^ 2 +
        3 * lb * radio34 cb 1 mb ^ (2 * α) * Sg ^ 2 ≤
      constante34 lr lb cr cb α Sf Sg *
        ((mr : ℝ) ^ (-(α / 2)) + (mb : ℝ) ^ (-α)) := by
  have h := datos34_escalar ((Real.sqrt 2) ^ (2 * α))
    (lr * cr ^ (-α) * Sf ^ 2) (lb * cb ^ (-(2 * α)) * Sg ^ 2)
    ((mr : ℝ) ^ (-(α / 2))) ((mb : ℝ) ^ (-α))
    (Real.rpow_nonneg (Real.sqrt_nonneg 2) _)
    (Real.rpow_nonneg (Nat.cast_nonneg mr) _)
    (Real.rpow_nonneg (Nat.cast_nonneg mb) _)
  rw [radio34_potencia_interior cr α mr hcr hmr,
    radio34_potencia_frontera cb α mb hcb hmb]
  unfold constante34
  linarith [h]

/-! ## Problema regularizado con los pesos (3.7) -/

theorem pesoCobertura_nonneg (l ε α Cm : ℝ)
    (hl : 0 ≤ l) (hε : 0 ≤ ε) (hCm : 0 ≤ Cm) :
    0 ≤ pesoCobertura l ε α Cm := by
  unfold pesoCobertura
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hl) (Real.rpow_nonneg hε _)) hCm

/-- Problema PINN del Teorema 3.4 para una realización `(xr, xb)` de las
muestras. Los pesos de regularización son los de (3.7),
`λ̂_r = 3 λ_r ε_r^{2α} / C_m` y `λ̂_b = 3 λ_b ε_b^{2α} / C_m`,
distintos en el interior y en la frontera; su `funcionalRegularizado` es la
pérdida `Loss_m(h; λ, λ̂_m)` de (3.8). -/
def Operadores38.problema34 {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Operadores38 H X Y)
    (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (Cr Cb cr cb lr lb α : ℝ) (hCr : 0 < Cr) (hcr : 0 < cr) (hcb : 0 < cb)
    (hlr : 0 < lr) (hlb : 0 < lb)
    (xr : Fin mr → X) (xb : Fin mb → Y) : ProblemaPINN H X Y mr mb where
  L := D.L
  f := D.f
  B := D.B
  g := D.g
  xr := xr
  xb := xb
  μr := μr
  μb := μb
  μr_prob := measure_univ
  μb_prob := measure_univ
  seminormaL := D.seminormaL
  seminormaB := D.seminormaB
  lambdaR := lr
  lambdaB := lb
  regularizadorR :=
    pesoCobertura lr (radio34 cr 2 mr) α (factor34 mr mb Cr Cb cr cb)
  regularizadorB :=
    pesoCobertura lb (radio34 cb 1 mb) α (factor34 mr mb Cr Cb cr cb)
  mr_pos := hmr
  mb_pos := hmb
  lambdaR_pos := hlr
  lambdaB_pos := hlb
  regularizadorR_nonneg := pesoCobertura_nonneg _ _ _ _ hlr.le
    (radio34_pos cr 2 mr hcr hmr).le (factor34_pos mr mb Cr Cb cr cb hCr hcr hmr).le
  regularizadorB_nonneg := pesoCobertura_nonneg _ _ _ _ hlb.le
    (radio34_pos cb 1 mb hcb hmb).le (factor34_pos mr mb Cr Cb cr cb hCr hcr hmr).le

/-- Hipótesis de regularidad del Teorema 3.4 para la clase de candidatos
admisibles `Hadm`: los datos `f`, `g` y los operadores `L[h]`, `B[h]` son
Hölder de exponente `α`. `Sf` y `Sg` acotan las seminormas de los datos.
Los valores `seminormaL` y `seminormaB` pueden ser las seminormas exactas o
mayorantes válidos usados en el regularizador. Coincide definicionalmente con
`CotasHolder` para cualquier `problema34`. -/
def Operadores38.CotasHolder34 {H X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (D : Operadores38 H X Y) (Hadm : Set H) (U : Set X) (Γ : Set Y)
    (α Sf Sg : ℝ) : Prop :=
  0 ≤ Sf ∧ 0 ≤ Sg ∧
  (∀ h ∈ Hadm, 0 ≤ D.seminormaL h ∧ 0 ≤ D.seminormaB h ∧
    (∀ x ∈ U, ∀ y ∈ U,
      |D.L h x - D.L h y| ≤ D.seminormaL h * dist x y ^ α) ∧
    (∀ x ∈ Γ, ∀ y ∈ Γ,
      |D.B h x - D.B h y| ≤ D.seminormaB h * dist x y ^ α)) ∧
  (∀ x ∈ U, ∀ y ∈ U, |D.f x - D.f y| ≤ Sf * dist x y ^ α) ∧
  (∀ x ∈ Γ, ∀ y ∈ Γ, |D.g x - D.g y| ≤ Sg * dist x y ^ α)

/-! ## Lema 3.5: control determinista bajo un evento de cobertura -/

/-- **Lema 3.5 (Shin, Lemma B.1), dimensión dos.** Si las muestras pertenecen
a `U` y a `Γ` y son `ε_r`-densas en `U` y `ε_b`-densas en `Γ`, con
`0 < ε_r, ε_b ≤ ε₀`, y se cumplen las cotas de masa de bolas cerradas (3.4),
entonces todo candidato `h` de la clase verifica (3.13) con
`C_m = 3 max{C_r m_r ε_r², C_b m_b ε_b}`. La cobertura es una hipótesis
determinista; ninguna probabilidad interviene. -/
theorem lema35_dim2
    {H X Y : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [PseudoMetricSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {mr mb : ℕ}
    (P : ProblemaPINN H X Y mr mb)
    (Hm : Set H) (U : Set X) (Γ : Set Y)
    (hU : MeasurableSet U) (hΓ : MeasurableSet Γ)
    (hμr : P.μr Uᶜ = 0) (hμb : P.μb Γᶜ = 0)
    (α εr εb ε₀ Cr Cb Sf Sg : ℝ)
    (hα : 0 < α) (hεr : 0 < εr) (hεb : 0 < εb)
    (hεr₀ : εr ≤ ε₀) (hεb₀ : εb ≤ ε₀)
    (hCr : 0 < Cr) (hCb : 0 < Cb)
    (hsr : ∀ i, P.xr i ∈ U) (hsb : ∀ i, P.xb i ∈ Γ)
    (hcoverR : MuestrasCubren U P.xr εr)
    (hcoverB : MuestrasCubren Γ P.xb εb)
    (hmassR : MasaBolaSuperior P.μr U ε₀ Cr 2)
    (hmassB : MasaBolaSuperior P.μb Γ ε₀ Cb 1)
    (hHolder : CotasHolder P Hm U Γ α Sf Sg) :
    ∀ h ∈ Hm, P.PoblacionIntegrable h →
      P.perdidaPoblacional h ≤
        factorCoberturaCuadrado mr mb Cr Cb εr εb *
          (P.perdidaEmpirica h +
            3 * P.lambdaR * εr ^ (2 * α) /
              factorCoberturaCuadrado mr mb Cr Cb εr εb * (P.seminormaL h) ^ 2 +
            3 * P.lambdaB * εb ^ (2 * α) /
              factorCoberturaCuadrado mr mb Cr Cb εr εb * (P.seminormaB h) ^ 2) +
        3 * P.lambdaR * εr ^ (2 * α) * Sf ^ 2 +
        3 * P.lambdaB * εb ^ (2 * α) * Sg ^ 2 := by
  intro h hh hint
  exact objetivoCoberturaIntegral_de_hipotesis P Hm U Γ hU hΓ hμr hμb
    α εr εb ε₀ ε₀ Cr Cb Sf Sg hα hεr hεb hεr₀ hεb₀ hCr hCb hsr hsb
    hcoverR hcoverB hmassR hmassB hHolder h hh hint

/-! ## Evento de cobertura del Teorema 3.4 -/

section Evento

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (μ : Measure X) [IsProbabilityMeasure μ]
  (Z : ℕ → Ω → X)

/-- Las primeras `m` muestras pertenecen a `U`. -/
def muestrasEnSoporte (m : ℕ) (U : Set X) : Set Ω :=
  {ω | ∀ i : Fin m, Z i ω ∈ U}

theorem muestrasEnSoporte_measurable (m : ℕ) (U : Set X)
    (hU : MeasurableSet U) (hZ : ∀ i, Measurable (Z i)) :
    MeasurableSet (muestrasEnSoporte Z m U) := by
  rw [show muestrasEnSoporte Z m U = ⋂ i : Fin m, (Z i) ⁻¹' U by
    ext ω; simp [muestrasEnSoporte]]
  exact MeasurableSet.iInter fun i => hU.preimage (hZ i)

omit [IsProbabilityMeasure P] [IsProbabilityMeasure μ] in
/-- La concentración de la ley en `U` hace nulo el evento en que alguna de las
primeras `m` muestras cae fuera de `U`. -/
theorem medidaReal_fallo_soporte (m : ℕ) (U : Set X) (hμ : μ Uᶜ = 0)
    (hZ : ∀ i, Measurable (Z i))
    (hLaw : ∀ i, Measure.map (Z i) P = μ) :
    P.real (muestrasEnSoporte Z m U)ᶜ = 0 := by
  have hae : ∀ᵐ ω ∂P, ∀ i, Z i ω ∈ U :=
    muestras_en_soporte_ae P μ Z U hμ hZ hLaw
  have h0 : P {ω | ¬ ∀ i, Z i ω ∈ U} = 0 := ae_iff.mp hae
  have hsub : (muestrasEnSoporte Z m U)ᶜ ⊆ {ω | ¬ ∀ i, Z i ω ∈ U} := by
    intro ω hω hall
    exact hω (fun i => hall i)
  have hnull : P (muestrasEnSoporte Z m U)ᶜ = 0 := measure_mono_null hsub h0
  rw [measureReal_def, hnull, ENNReal.toReal_zero]

/-- Cota de unión para la intersección de cuatro eventos medibles. -/
theorem probReal_inter_cuatro_ge (A B C D : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    1 - P.real Aᶜ - P.real Bᶜ - P.real Cᶜ - P.real Dᶜ ≤
      P.real ((A ∩ B) ∩ (C ∩ D)) := by
  have hm : MeasurableSet ((A ∩ B) ∩ (C ∩ D)) :=
    (hA.inter hB).inter (hC.inter hD)
  have hcompl : ((A ∩ B) ∩ (C ∩ D))ᶜ = (Aᶜ ∪ Bᶜ) ∪ (Cᶜ ∪ Dᶜ) := by
    simp only [Set.compl_inter]
  have h1 : P.real ((A ∩ B) ∩ (C ∩ D))ᶜ ≤
      P.real Aᶜ + P.real Bᶜ + (P.real Cᶜ + P.real Dᶜ) := by
    rw [hcompl]
    exact (measureReal_union_le _ _).trans
      (add_le_add (measureReal_union_le _ _) (measureReal_union_le _ _))
  have h2 : P.real ((A ∩ B) ∩ (C ∩ D))ᶜ = 1 - P.real ((A ∩ B) ∩ (C ∩ D)) :=
    probReal_compl_eq_one_sub hm
  linarith

end Evento

/-- Descripción determinista de una realización en el evento de cobertura
`Ω_m`: las muestras pertenecen a su soporte y son densas con los radios (3.5). -/
def CoberturaMuestral34 {Ω X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (Zr : ℕ → Ω → X) (Zb : ℕ → Ω → Y) (U : Set X) (Γ : Set Y)
    (cr cb : ℝ) (mr mb : ℕ) (ω : Ω) : Prop :=
  (∀ i : Fin mr, Zr i ω ∈ U) ∧ (∀ j : Fin mb, Zb j ω ∈ Γ) ∧
  MuestrasCubren U (fun i : Fin mr => Zr i ω) (radio34 cr 2 mr) ∧
  MuestrasCubren Γ (fun j : Fin mb => Zb j ω) (radio34 cb 1 mb)

/-- **Parte probabilística del Teorema 3.4.** Bajo la Hipótesis 3.2 y con los
radios finales (3.5) en `(0, ε₀]`, existe un evento medible `Ω_m`, determinado
solo por las muestras, con la probabilidad (3.10), en el cual las muestras son
`ε_r`-densas en `U` y `ε_b`-densas en `Γ`. No se usa independencia entre las
muestras interiores y las de frontera. -/
theorem evento_cobertura34_dim2
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (U : Set X) (Γ : Set Y) (ε₀ : ℝ)
    (dr : DatosMasa38 μr U 2 ε₀) (db : DatosMasa38 μb Γ 1 ε₀)
    (sr : Muestreo38 P μr) (sb : Muestreo38 P μb)
    (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (hradR : radio34 dr.c 2 mr ≤ ε₀) (hradB : radio34 db.c 1 mb ≤ ε₀) :
    ∃ Ωm : Set Ω, MeasurableSet Ωm ∧
      1 - Real.sqrt (mr : ℝ) * (1 - 1 / Real.sqrt (mr : ℝ)) ^ mr
        - Real.sqrt (mb : ℝ) * (1 - 1 / Real.sqrt (mb : ℝ)) ^ mb ≤ P.real Ωm ∧
      ∀ ω ∈ Ωm, CoberturaMuestral34 sr.Z sb.Z U Γ dr.c db.c mr mb ω := by
  have hεr : 0 < radio34 dr.c 2 mr := radio34_pos dr.c 2 mr dr.c_pos hmr
  have hεb : 0 < radio34 db.c 1 mb := radio34_pos db.c 1 mb db.c_pos hmb
  obtain ⟨hηr0, hηr⟩ :=
    escala_le_de_radio (escalaAuxiliarRaiz dr.c 2 mr) ε₀ hεr hradR
  obtain ⟨hηb0, hηb⟩ :=
    escala_le_de_radio (escalaAuxiliarRaiz db.c 1 mb) ε₀ hεb hradB
  obtain ⟨Kr, cellsR, hcR, hdisjR, hcovR, _hsubR, hminR, hdiamR⟩ :=
    dr.particiones (escalaAuxiliarRaiz dr.c 2 mr) hηr0 hηr
  obtain ⟨Kb, cellsB, hcB, hdisjB, hcovB, _hsubB, hminB, hdiamB⟩ :=
    db.particiones (escalaAuxiliarRaiz db.c 1 mb) hηb0 hηb
  have hminR' : ∀ k, 1 / Real.sqrt (mr : ℝ) ≤ μr.real (cellsR k) := by
    intro k
    rw [← escalaAuxiliarRaiz_masa dr.c 2 mr dr.c_pos (by norm_num) hmr]
    exact hminR k
  have hminB' : ∀ k, 1 / Real.sqrt (mb : ℝ) ≤ μb.real (cellsB k) := by
    intro k
    rw [← escalaAuxiliarRaiz_masa db.c 1 mb db.c_pos (by norm_num) hmb]
    exact hminB k
  have hmOR := todasCeldasOcupadas_measurable sr.Z mr cellsR hcR sr.medible
  have hmOB := todasCeldasOcupadas_measurable sb.Z mb cellsB hcB sb.medible
  have hmSR := muestrasEnSoporte_measurable sr.Z mr U dr.medible sr.medible
  have hmSB := muestrasEnSoporte_measurable sb.Z mb Γ db.medible sb.medible
  have hfR := lema36_fallo_shin P μr sr.Z mr hmr cellsR hcR
    (solapamiento_nulo_de_disjuntas μr cellsR hdisjR) sr.medible sr.indep sr.ley hminR'
  have hfB := lema36_fallo_shin P μb sb.Z mb hmb cellsB hcB
    (solapamiento_nulo_de_disjuntas μb cellsB hdisjB) sb.medible sb.indep sb.ley hminB'
  have hsR := medidaReal_fallo_soporte P μr sr.Z mr U dr.concentrada
    sr.medible sr.ley
  have hsB := medidaReal_fallo_soporte P μb sb.Z mb Γ db.concentrada
    sb.medible sb.ley
  have h4 := probReal_inter_cuatro_ge P
    (todasCeldasOcupadas sr.Z mr cellsR) (todasCeldasOcupadas sb.Z mb cellsB)
    (muestrasEnSoporte sr.Z mr U) (muestrasEnSoporte sb.Z mb Γ)
    hmOR hmOB hmSR hmSB
  refine ⟨(todasCeldasOcupadas sr.Z mr cellsR ∩ todasCeldasOcupadas sb.Z mb cellsB) ∩
      (muestrasEnSoporte sr.Z mr U ∩ muestrasEnSoporte sb.Z mb Γ),
    (hmOR.inter hmOB).inter (hmSR.inter hmSB), by linarith, ?_⟩
  rintro ω ⟨⟨hoR, hoB⟩, hsuR, hsuB⟩
  exact ⟨hsuR, hsuB,
    ocupacion_implica_cobertura sr.Z mr U cellsR (radio34 dr.c 2 mr)
      hcovR hdiamR ω hoR,
    ocupacion_implica_cobertura sb.Z mb Γ cellsB (radio34 db.c 1 mb)
      hcovB hdiamB ω hoB⟩

/-! ## Teorema 3.4 -/

/-- **Parte determinista del Teorema 3.4.** En una realización del evento de
cobertura, la desigualdad (3.11) vale para todo candidato admisible. -/
theorem cota34_de_cobertura_dim2
    {Ω H X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (U : Set X) (Γ : Set Y) (ε₀ : ℝ)
    (dr : DatosMasa38 μr U 2 ε₀) (db : DatosMasa38 μb Γ 1 ε₀)
    (Zr : ℕ → Ω → X) (Zb : ℕ → Ω → Y)
    (D : Operadores38 H X Y) (Hadm : Set H)
    (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (lr lb α Sf Sg : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (hradR : radio34 dr.c 2 mr ≤ ε₀) (hradB : radio34 db.c 1 mb ≤ ε₀)
    (hHolder : D.CotasHolder34 Hadm U Γ α Sf Sg)
    (ω : Ω) (hω : CoberturaMuestral34 Zr Zb U Γ dr.c db.c mr mb ω)
    (h : H) (hh : h ∈ Hadm) :
    (D.problema34 μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
        dr.C_pos dr.c_pos db.c_pos hlr hlb
        (fun i => Zr i ω) (fun j => Zb j ω)).perdidaPoblacional h ≤
      factor34 mr mb dr.C db.C dr.c db.c *
        (D.problema34 μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
          dr.C_pos dr.c_pos db.c_pos hlr hlb
          (fun i => Zr i ω) (fun j => Zb j ω)).funcionalRegularizado h +
      constante34 lr lb dr.c db.c α Sf Sg *
        ((mr : ℝ) ^ (-(α / 2)) + (mb : ℝ) ^ (-α)) := by
  obtain ⟨hsuR, hsuB, hcoverR, hcoverB⟩ := hω
  have hεr : 0 < radio34 dr.c 2 mr := radio34_pos dr.c 2 mr dr.c_pos hmr
  have hεb : 0 < radio34 db.c 1 mb := radio34_pos db.c 1 mb db.c_pos hmb
  have hContL : ContinuousOn (D.L h) U :=
    continuo_de_cota_holder U _ _ α hα (hHolder.2.2.1 h hh).2.2.1
  have hContB : ContinuousOn (D.B h) Γ :=
    continuo_de_cota_holder Γ _ _ α hα (hHolder.2.2.1 h hh).2.2.2
  have hContF : ContinuousOn D.f U :=
    continuo_de_cota_holder U _ Sf α hα hHolder.2.2.2.1
  have hContG : ContinuousOn D.g Γ :=
    continuo_de_cota_holder Γ _ Sg α hα hHolder.2.2.2.2
  let Pω := D.problema34 μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
    dr.C_pos dr.c_pos db.c_pos hlr hlb (fun i => Zr i ω) (fun j => Zb j ω)
  change Pω.perdidaPoblacional h ≤
    factor34 mr mb dr.C db.C dr.c db.c * Pω.funcionalRegularizado h +
    constante34 lr lb dr.c db.c α Sf Sg *
      ((mr : ℝ) ^ (-(α / 2)) + (mb : ℝ) ^ (-α))
  have hHolderP : CotasHolder Pω Hadm U Γ α Sf Sg := hHolder
  have hint : Pω.PoblacionIntegrable h :=
    poblacionIntegrable_de_holder_acotado Pω Hadm U Γ
      dr.acotado db.acotado (soporte_no_vacio μr U dr.concentrada)
      (soporte_no_vacio μb Γ db.concentrada) dr.concentrada db.concentrada
      α Sf Sg hα hHolderP h hh
      (aestronglyMeasurable_residuo_sq_de_continuidad μr U dr.medible
        dr.concentrada _ _ hContL hContF)
      (aestronglyMeasurable_residuo_sq_de_continuidad μb Γ db.medible
        db.concentrada _ _ hContB hContG)
  have hobj := objetivoCoberturaIntegral_de_hipotesis Pω
    Hadm U Γ dr.medible db.medible dr.concentrada db.concentrada
    α (radio34 dr.c 2 mr) (radio34 db.c 1 mb) ε₀ ε₀ dr.C db.C Sf Sg
    hα hεr hεb hradR hradB dr.C_pos db.C_pos hsuR hsuB hcoverR hcoverB
    dr.superior db.superior hHolderP h hh hint
  have hobj1 : Pω.perdidaPoblacional h ≤
      factorCoberturaCuadrado mr mb dr.C db.C
          (radio34 dr.c 2 mr) (radio34 db.c 1 mb) *
        (Pω.perdidaEmpirica h +
          pesoCobertura lr (radio34 dr.c 2 mr) α
            (factorCoberturaCuadrado mr mb dr.C db.C
              (radio34 dr.c 2 mr) (radio34 db.c 1 mb)) *
            Pω.regularidadInterior h +
          pesoCobertura lb (radio34 db.c 1 mb) α
            (factorCoberturaCuadrado mr mb dr.C db.C
              (radio34 dr.c 2 mr) (radio34 db.c 1 mb)) *
            Pω.regularidadFrontera h) +
      3 * lr * radio34 dr.c 2 mr ^ (2 * α) * Sf ^ 2 +
      3 * lb * radio34 db.c 1 mb ^ (2 * α) * Sg ^ 2 := hobj
  rw [factorCoberturaCuadrado_radio34 mr mb dr.C db.C dr.c db.c
    dr.c_pos db.c_pos hmr hmb] at hobj1
  have hobj2 : Pω.perdidaPoblacional h ≤
      factor34 mr mb dr.C db.C dr.c db.c * Pω.funcionalRegularizado h +
      3 * lr * radio34 dr.c 2 mr ^ (2 * α) * Sf ^ 2 +
      3 * lb * radio34 db.c 1 mb ^ (2 * α) * Sg ^ 2 := hobj1
  have hdatos := datos34_le lr lb dr.c db.c α Sf Sg mr mb
    dr.c_pos db.c_pos hmr hmb
  linarith [hobj2, hdatos]

/-- **Teorema 3.4 (Shin–Darbon–Karniadakis, Theorem 3.1), dimensión dos.**
Bajo la Hipótesis 3.2 (`DatosMasa38`, `Muestreo38`), con `λ_r, λ_b > 0`,
`α > 0` y tamaños `m_r, m_b` para los que los radios (3.5) pertenecen a
`(0, ε₀]`, existe un evento medible `Ω_m`, determinado solo por las muestras,
tal que

* `P(Ω_m) ≥ 1 - √m_r (1 - 1/√m_r)^{m_r} - √m_b (1 - 1/√m_b)^{m_b}`, que es
  (3.10), y
* en `Ω_m`, **para todo candidato admisible `h` simultáneamente**,
  `LossPINN(h; λ) ≤ C_m · Loss_m(h; λ, λ̂_m) + C' (m_r^{-α/2} + m_b^{-α})`,
  que es (3.11) con `d = 2`.

El cuantificador sobre `h` es interior al evento: `h` puede elegirse después
de observar la muestra. La integrabilidad de los residuos no es una hipótesis:
se deduce de las cotas Hölder y de la acotación de `U` y `Γ`. -/
theorem teorema34_dim2
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
  obtain ⟨Ωm, hmeas, hprob, hcob⟩ := evento_cobertura34_dim2 P μr μb U Γ ε₀
    dr db sr sb mr mb hmr hmb hradR hradB
  exact ⟨Ωm, hmeas, hprob, fun ω hω h hh =>
    cota34_de_cobertura_dim2 μr μb U Γ ε₀ dr db sr.Z sb.Z D Hadm mr mb hmr hmb
      lr lb α Sf Sg hlr hlb hα hradR hradB hHolder ω (hcob ω hω) h hh⟩

/-- **Teorema 3.4 con el enunciado desplegado.** Es `teorema34_dim2` sin las
estructuras intermedias: la pérdida poblacional, la pérdida empírica
regularizada (3.8) y los pesos (3.7) aparecen con sus integrales, sumas y
cocientes explícitos. La prueba es `teorema34_dim2` literalmente: las dos
formas coinciden por definición. -/
theorem teorema34_dim2_explicito
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
        lr * ∫ x, (D.L h x - D.f x) ^ 2 ∂μr +
            lb * ∫ y, (D.B h y - D.g y) ^ 2 ∂μb ≤
          factor34 mr mb dr.C db.C dr.c db.c *
            (lr / (mr : ℝ) *
                ∑ i : Fin mr, (D.L h (sr.Z i ω) - D.f (sr.Z i ω)) ^ 2 +
              lb / (mb : ℝ) *
                ∑ j : Fin mb, (D.B h (sb.Z j ω) - D.g (sb.Z j ω)) ^ 2 +
              3 * lr * radio34 dr.c 2 mr ^ (2 * α) /
                  factor34 mr mb dr.C db.C dr.c db.c * (D.seminormaL h) ^ 2 +
              3 * lb * radio34 db.c 1 mb ^ (2 * α) /
                  factor34 mr mb dr.C db.C dr.c db.c * (D.seminormaB h) ^ 2) +
          constante34 lr lb dr.c db.c α Sf Sg *
            ((mr : ℝ) ^ (-(α / 2)) + (mb : ℝ) ^ (-α)) :=
  teorema34_dim2 P μr μb U Γ ε₀ dr db sr sb D Hadm mr mb hmr hmb
    lr lb α Sf Sg hlr hlb hα hradR hradB hHolder

/-- La probabilidad (3.10) es no trivial: cada término de fallo es a lo sumo
`√m exp (-√m)`, de modo que la cota inferior tiende a uno. -/
theorem probabilidad34_ge_exponencial (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb) :
    1 - Real.sqrt (mr : ℝ) * Real.exp (-Real.sqrt (mr : ℝ))
        - Real.sqrt (mb : ℝ) * Real.exp (-Real.sqrt (mb : ℝ)) ≤
      1 - Real.sqrt (mr : ℝ) * (1 - 1 / Real.sqrt (mr : ℝ)) ^ mr
        - Real.sqrt (mb : ℝ) * (1 - 1 / Real.sqrt (mb : ℝ)) ^ mb := by
  have hr := cota_shin_le_exponencial mr hmr
  have hb := cota_shin_le_exponencial mb hmb
  linarith

private theorem mul_exp_neg_le (x : ℝ) : x * Real.exp (-x) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (x - 1)
  have hx : x ≤ Real.exp (x - 1) := by linarith
  calc
    x * Real.exp (-x) ≤ Real.exp (x - 1) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ = Real.exp (-1) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- La observación que sigue a (3.10): cada término de fallo es a lo sumo
`e^{-1}`, así que la cota inferior de probabilidad es estrictamente positiva
para todos los tamaños `m_r, m_b ≥ 1`. -/
theorem probabilidad34_pos (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb) :
    0 < 1 - Real.sqrt (mr : ℝ) * (1 - 1 / Real.sqrt (mr : ℝ)) ^ mr
        - Real.sqrt (mb : ℝ) * (1 - 1 / Real.sqrt (mb : ℝ)) ^ mb := by
  have hr := (cota_shin_le_exponencial mr hmr).trans (mul_exp_neg_le _)
  have hb := (cota_shin_le_exponencial mb hmb).trans (mul_exp_neg_le _)
  have he : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    linarith
  have hinv : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    simp
  have hpos : 0 < Real.exp (-1) := Real.exp_pos _
  have h2 : 2 * Real.exp (-1) < 1 := by
    nlinarith [mul_pos hpos (sub_pos.mpr he)]
  linarith

#print axioms TesisPINN.probabilidad34_pos
#print axioms TesisPINN.factorCoberturaCuadrado_radio34
#print axioms TesisPINN.datos34_le
#print axioms TesisPINN.lema35_dim2
#print axioms TesisPINN.evento_cobertura34_dim2
#print axioms TesisPINN.cota34_de_cobertura_dim2
#print axioms TesisPINN.teorema34_dim2
#print axioms TesisPINN.teorema34_dim2_explicito
#print axioms TesisPINN.probabilidad34_ge_exponencial

end TesisPINN
