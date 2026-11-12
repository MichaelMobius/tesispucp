import TesisPINN.ComparadoresAproximados
import TesisPINN.Teorema38

/-! Proposición 3.10 para residuos escalares y dimensiones de masa 2 y 1. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Filter Asymptotics

/-- Se eligen las particiones a la escala de los radios originales en una
cola determinista de tamaños. La conclusión vuelve a los índices originales. -/
theorem DatosMasa38.cobertura_prefijos_ae
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [PseudoMetricSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure X) [IsProbabilityMeasure μ] (U : Set X) (s ε₀ : ℝ)
    (d : DatosMasa38 μ U s ε₀) (muestras : Muestreo38 P μ)
    (hs : 0 < s) (hε₀ : 0 < ε₀) (m : ℕ → ℕ)
    (hm : ∀ n, 0 < m n) (hcrece : ∀ᶠ n in atTop, n ≤ m n) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      Real.sqrt 2 * escalaAuxiliarRaiz d.c s (m n) ≤ ε₀ ∧
      MuestrasCubren U (fun i : Fin (m n) => muestras.Z i ω)
        (Real.sqrt 2 * escalaAuxiliarRaiz d.c s (m n)) := by
  have hsmall := radio_cobertura_eventualmente_pequeno d.c s ε₀ m
    d.c_pos hs hε₀ hm hcrece
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  let mt := fun n => m (n + N)
  have hη (n : ℕ) :
      0 < escalaAuxiliarRaiz d.c s (mt n) ∧ escalaAuxiliarRaiz d.c s (mt n) ≤ ε₀ := by
    have hsqrt : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hpos := pos_of_mul_pos_right (radio38_pos d.c s (mt n) d.c_pos (hm (n + N)))
      (Real.sqrt_nonneg 2)
    exact ⟨hpos, (le_mul_of_one_le_left hpos.le hsqrt).trans (hN (n + N) (by omega))⟩
  choose k cells hc using fun n => d.particiones _ (hη n).1 (hη n).2
  have hcreceTail : ∀ᶠ n in atTop, n ≤ mt n :=
    ((tendsto_add_atTop_nat N).eventually hcrece).mono (fun n hn => by dsimp [mt]; omega)
  have hcover := cobertura_eventual_de_particiones_raiz P μ muestras.Z k mt cells U
    d.c s d.c_pos hs (fun n => (hc n).1) (fun n => (hc n).2.1)
    (fun n => (hc n).2.2.1) (fun n => (hc n).2.2.2.2.2)
    (fun n => hm (n + N)) hcreceTail (fun n => (hc n).2.2.2.2.1)
    muestras.medible muestras.indep muestras.ley
  exact hcover.mono fun _ h => hsmall.and (eventual_en_cola N h)

/-- Una cota de la regularidad cuadrática da cotas para cada seminorma
y para los incrementos de cada residuo. -/
theorem holder_residuos_de_regularidad
    {H X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] {mr mb : ℕ}
    (P : ProblemaPINN H X Y mr mb) (Hm : Set H) (U : Set X) (Γ : Set Y)
    (α Sf Sg R : ℝ) (hH : CotasHolder P Hm U Γ α Sf Sg)
    (h : H) (hh : h ∈ Hm) (hreg : P.regularidadTotal h ≤ R) :
    (P.seminormaL h ≤ Real.sqrt R ∧ P.seminormaB h ≤ Real.sqrt R) ∧
    (∀ x ∈ U, ∀ y ∈ U, |(P.L h x - P.f x) - (P.L h y - P.f y)| ≤
      (Real.sqrt R + Sf) * dist x y ^ α) ∧
    (∀ x ∈ Γ, ∀ y ∈ Γ, |(P.B h x - P.g x) - (P.B h y - P.g y)| ≤
      (Real.sqrt R + Sg) * dist x y ^ α) := by
  have hR := (P.regularidadTotal_nonneg h).trans hreg
  obtain ⟨_, _, hclass, hf, hg⟩ := hH
  obtain ⟨hL0, hB0, hL, hB⟩ := hclass h hh
  change (P.seminormaL h) ^ 2 + (P.seminormaB h) ^ 2 ≤ R at hreg
  have hsr : P.seminormaL h ≤ Real.sqrt R :=
    (sq_le_sq₀ hL0 (Real.sqrt_nonneg R)).1 (by rw [Real.sq_sqrt hR]; nlinarith)
  have hsb : P.seminormaB h ≤ Real.sqrt R :=
    (sq_le_sq₀ hB0 (Real.sqrt_nonneg R)).1 (by rw [Real.sq_sqrt hR]; nlinarith)
  refine ⟨⟨hsr, hsb⟩, ?_, ?_⟩
  · apply holder_resta U (P.L h) P.f (Real.sqrt R) Sf α _ hf
    intro x hx y hy
    exact (hL x hx y hy).trans (mul_le_mul_of_nonneg_right hsr (by positivity))
  · apply holder_resta Γ (P.B h) P.g (Real.sqrt R) Sg α _ hg
    intro x hx y hy
    exact (hB x hx y hy).trans (mul_le_mul_of_nonneg_right hsb (by positivity))

/-- Proposición 3.10 en la instancia escalar de dimensión dos. -/
theorem proposicion310_dim2
    {Ω H X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (U : Set X) (Γ : Set Y) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (dr : DatosMasa38 μr U 2 ε₀) (db : DatosMasa38 μb Γ 1 ε₀)
    (sr : Muestreo38 P μr) (sb : Muestreo38 P μb)
    (D : Operadores38 H X Y)
    (mr mb : ℕ → ℕ) (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (hgr : ∀ᶠ n in atTop, n ≤ mr n) (hgb : ∀ᶠ n in atTop, n ≤ mb n)
    (lr lb α Sf Sg Ksize : ℝ) (hlr : 0 < lr) (hlb : 0 < lb)
    (hα : 0 < α) (_hαone : α ≤ 1) (hKsize : 0 < Ksize)
    (hrel : ∀ᶠ n in atTop, (mr n : ℝ) ≤ Ksize * (mb n : ℝ) ^ 2)
    (Hm : ℕ → Set H) (hm v : ∀ n, Ω → Hm n)
    (_hMeasHm : ∀ n, Measurable (fun ω => (hm n ω : H)))
    (_hMeasV : ∀ n, Measurable (fun ω => (v n ω : H)))
    (ε δ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hδ : ∀ n, 0 ≤ δ n)
    (Rstar : Ω → ℝ) (K : ℝ) :
    let base := fun n => D.base μr μb (mr n) (mb n) (hmr n) (hmb n)
      dr.C db.C dr.c db.c lr lb α dr.C_pos dr.c_pos hlr hlb
    let Pn := problemaMuestral mr mb base sr.Z sb.Z
    let rr := fun n => Real.sqrt 2 * escalaAuxiliarRaiz dr.c 2 (mr n)
    let rb := fun n => Real.sqrt 2 * escalaAuxiliarRaiz db.c 1 (mb n)
    let Cm := fun n => factorCoberturaCuadrado (mr n) (mb n) dr.C db.C (rr n) (rb n)
    let a := fun n => (base n).regularizadorR
    (∀ n, CotasHolder (base n) (Hm n) U Γ α Sf Sg) →
    (∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (Pn ω n).perdidaEmpirica (v n ω : H) ≤ ε n ∧
      (Pn ω n).regularidadTotal (v n ω : H) ≤ Rstar ω ∧
      (Pn ω n).EsMinimizadorAproximado (Hm n) (hm n ω : H) (δ n)) →
    (∀ᶠ n in atTop, ε n + δ n ≤ K * a n) →
    ∀ᵐ ω ∂P,
      let er := fun n x => D.L (hm n ω : H) x - D.f x
      let eb := fun n y => D.B (hm n ω : H) y - D.g y
      let loss := fun n => (Pn ω n).perdidaPoblacional (hm n ω : H)
      (∀ᶠ n in atTop, (Pn ω n).regularidadTotal (hm n ω : H) ≤ Rstar ω + K ∧
        D.seminormaL (hm n ω : H) ≤ Real.sqrt (Rstar ω + K) ∧
        D.seminormaB (hm n ω : H) ≤ Real.sqrt (Rstar ω + K) ∧
        loss n ≤ Cm n * (a n * (Rstar ω + K)) +
          3 * lr * rr n ^ (2 * α) * Sf ^ 2 + 3 * lb * rb n ^ (2 * α) * Sg ^ 2) ∧
      (loss =O[atTop] (fun n => (mr n : ℝ) ^ (-(α / 2)))) ∧
      (Tendsto (fun n => supResiduo U (er n)) atTop (nhds 0) ∧
       Tendsto (fun n => supResiduo Γ (eb n)) atTop (nhds 0)) ∧
      (((fun n => supResiduo U (er n)) =O[atTop]
         (fun n => (mr n : ℝ) ^ (-(α ^ 2 / (2 * (2 * α + 2)))))) ∧
       ((fun n => supResiduo Γ (eb n)) =O[atTop]
         (fun n => (mr n : ℝ) ^ (-(α ^ 2 / (2 * (2 * α + 1))))))) := by
  intro base Pn rr rb Cm a hHolder hvar htol
  have hcoverR := dr.cobertura_prefijos_ae P μr U 2 ε₀ sr (by norm_num) hε₀ mr hmr hgr
  have hcoverB := db.cobertura_prefijos_ae P μb Γ 1 ε₀ sb (by norm_num) hε₀ mb hmb hgb
  have hsupportR := muestras_en_soporte_ae P μr sr.Z U dr.concentrada sr.medible sr.ley
  have hsupportB := muestras_en_soporte_ae P μb sb.Z Γ db.concentrada sb.medible sb.ley
  have hrpos (n : ℕ) : 0 < rr n := radio38_pos dr.c 2 (mr n) dr.c_pos (hmr n)
  have hbpos (n : ℕ) : 0 < rb n := radio38_pos db.c 1 (mb n) db.c_pos (hmb n)
  have hapos (n : ℕ) : 0 < a n :=
    peso38_pos (mr n) (mb n) dr.C db.C (rr n) (rb n) lr lb α dr.C_pos (hmr n) (hrpos n) hlr
  have hCm (n : ℕ) : 0 ≤ Cm n := by
    have hr : 0 ≤ dr.C * (mr n : ℝ) * rr n ^ 2 :=
      mul_nonneg (mul_nonneg dr.C_pos.le (Nat.cast_nonneg _)) (sq_nonneg _)
    exact mul_nonneg (by norm_num) (hr.trans (le_max_left _ _))
  have hK : 0 ≤ K := by
    obtain ⟨n, hn⟩ := htol.exists
    exact nonneg_of_mul_nonneg_left ((add_nonneg (hε n) (hδ n)).trans hn) (hapos n)
  have hSf := (hHolder 0).1
  have hSg := (hHolder 0).2.1
  have hcr := dr.c_pos
  have hcb := db.c_pos
  have hContF := continuo_de_cota_holder U D.f Sf α hα (hHolder 0).2.2.2.1
  have hContG := continuo_de_cota_holder Γ D.g Sg α hα (hHolder 0).2.2.2.2
  have hmTop : Tendsto mr atTop atTop := tendsto_atTop_mono' atTop hgr tendsto_id
  filter_upwards [hcoverR, hcoverB, hsupportR, hsupportB, hvar]
    with ω hcovR hcovB hsupR hsupB hvarω
  dsimp only
  obtain ⟨n, _, hRv, _⟩ := hvarω.exists
  have hRstar : 0 ≤ Rstar ω := ((Pn ω n).regularidadTotal_nonneg (v n ω : H)).trans hRv
  let R := Rstar ω + K
  have hR : 0 ≤ R := add_nonneg hRstar hK
  let er := fun n x => D.L (hm n ω : H) x - D.f x
  let eb := fun n y => D.B (hm n ω : H) y - D.g y
  let loss := fun n => (Pn ω n).perdidaPoblacional (hm n ω : H)
  have hstep : ∀ᶠ n in atTop,
      (Pn ω n).regularidadTotal (hm n ω : H) ≤ R ∧
      (Pn ω n).PoblacionIntegrable (hm n ω : H) ∧
      loss n ≤ Cm n * (a n * R) +
        3 * lr * rr n ^ (2 * α) * Sf ^ 2 + 3 * lb * rb n ^ (2 * α) * Sg ^ 2 := by
    filter_upwards [hcovR, hcovB, hvarω, htol] with n hr hb hv hnTol
    obtain ⟨hvε, hvR, hmin⟩ := hv
    have hκ : (ε n + δ n) / a n ≤ K := (div_le_iff₀ (hapos n)).2 hnTol
    have hreg := ((Pn ω n).cotas_minimizador_aproximado (Hm n) (hm n ω : H) (v n ω : H)
      (a n) (ε n) (δ n) (Rstar ω) (hapos n) rfl rfl hmin (v n ω).2 hvε hvR).1
    have hCand := (hHolder n).2.2.1 (hm n ω : H) (hm n ω).2
    have hContL := continuo_de_cota_holder U (D.L (hm n ω : H)) _ α hα hCand.2.2.1
    have hContB := continuo_de_cota_holder Γ (D.B (hm n ω : H)) _ α hα hCand.2.2.2
    have hInt := poblacionIntegrable_de_holder_acotado (Pn ω n) (Hm n) U Γ
      dr.acotado db.acotado (soporte_no_vacio μr U dr.concentrada)
      (soporte_no_vacio μb Γ db.concentrada) dr.concentrada db.concentrada
      α Sf Sg hα (hHolder n) _ (hm n ω).2
      (aestronglyMeasurable_residuo_sq_de_continuidad μr U dr.medible
        dr.concentrada _ _ hContL hContF)
      (aestronglyMeasurable_residuo_sq_de_continuidad μb Γ db.medible
        db.concentrada _ _ hContB hContG)
    have hpop := perdidaPoblacional_aproximada_bajo_cobertura (Pn ω n) (Hm n) U Γ
      dr.medible db.medible dr.concentrada db.concentrada
      α (rr n) (rb n) ε₀ ε₀ dr.C db.C Sf Sg (ε n) (δ n) (Rstar ω) hα
      (hrpos n) (hbpos n) hr.1 hb.1 dr.C_pos db.C_pos
      (fun i => hsupR i) (fun i => hsupB i) hr.2 hb.2 dr.superior db.superior
      (hHolder n) _ _ hmin (v n ω).2 hvε hvR hInt rfl rfl
    change loss n ≤ Cm n * (a n * (Rstar ω + (ε n + δ n) / a n)) +
      3 * lr * rr n ^ (2 * α) * Sf ^ 2 + 3 * lb * rb n ^ (2 * α) * Sg ^ 2 at hpop
    have hRκ := add_le_add_right hκ (Rstar ω)
    refine ⟨hreg.trans hRκ, hInt, hpop.trans ?_⟩
    exact add_le_add_left (add_le_add_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRκ (hapos n).le) (hCm n)) _) _
  let C := 3 *
    (lr * (Real.sqrt 2 * dr.c ^ (-(1 / (2 : ℝ)))) ^ (2 * α) +
      lb * (Real.sqrt 2 * db.c ^ (-(1 / (1 : ℝ)))) ^ (2 * α) * Ksize ^ (α / 2)) *
    (R + Sf ^ 2 + Sg ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrate : ∀ᶠ n in atTop, 0 ≤ loss n ∧ loss n ≤ C * (mr n : ℝ) ^ (-(α / 2)) := by
    filter_upwards [hstep, hrel] with n hn hrelN
    exact ⟨(Pn ω n).perdidaPoblacional_nonneg _ hn.2.1,
      tasa_de_cota_cobertura (mr n) (mb n) dr.C db.C dr.c db.c lr lb α Sf Sg
        R Ksize (loss n) (hmr n) (hmb n) dr.C_pos dr.c_pos db.c_pos
        hlr hlb hα hR hKsize hrelN hn.2.2⟩
  have hholder (n : ℕ) (hn : (Pn ω n).regularidadTotal (hm n ω : H) ≤ R) :=
    holder_residuos_de_regularidad (Pn ω n) (Hm n) U Γ α Sf Sg R
      (hHolder n) _ (hm n ω).2 hn
  have hquad : ∀ᶠ n in atTop,
      (Integrable (fun x => er n x ^ 2) μr ∧
       (∀ x ∈ U, ∀ y ∈ U, |er n x - er n y| ≤ (Real.sqrt R + Sf) * dist x y ^ α) ∧
       (∫ x, er n x ^ 2 ∂μr) ≤ (C / lr) * (mr n : ℝ) ^ (-(α / 2))) ∧
      (Integrable (fun y => eb n y ^ 2) μb ∧
       (∀ x ∈ Γ, ∀ y ∈ Γ, |eb n x - eb n y| ≤ (Real.sqrt R + Sg) * dist x y ^ α) ∧
       (∫ y, eb n y ^ 2 ∂μb) ≤ (C / lb) * (mr n : ℝ) ^ (-(α / 2))) := by
    filter_upwards [hstep, hrate] with n hn hrateN
    have hr : 0 ≤ ∫ x, er n x ^ 2 ∂μr := integral_nonneg fun _ => sq_nonneg _
    have hb : 0 ≤ ∫ y, eb n y ^ 2 ∂μb := integral_nonneg fun _ => sq_nonneg _
    have hsum := hrateN.2
    change lr * (∫ x, er n x ^ 2 ∂μr) + lb * (∫ y, eb n y ^ 2 ∂μb) ≤ _ at hsum
    refine ⟨⟨hn.2.1.1, (hholder n hn.1).2.1, ?_⟩, ⟨hn.2.1.2, (hholder n hn.1).2.2, ?_⟩⟩
    · rw [div_mul_eq_mul_div₀]
      exact (le_div_iff₀ hlr).2 (by nlinarith [mul_nonneg hlb.le hb])
    · rw [div_mul_eq_mul_div₀]
      exact (le_div_iff₀ hlb).2 (by nlinarith [mul_nonneg hlr.le hr])
  have hr := tasa_supResiduo_de_integral μr U dr.medible er mr hmTop α 2 (α / 2)
    (Real.sqrt R + Sf) (C / lr) (dr.c * (2 * Real.sqrt 2)⁻¹ ^ (2 : ℝ))
    (2 * Real.sqrt 2 * ε₀) hα (by norm_num) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (masa_bola_inferior_potencia μr U dr.c 2 ε₀ hε₀ dr.particiones) (hquad.mono fun _ h => h.1)
  have hb := tasa_supResiduo_de_integral μb Γ db.medible eb mr hmTop α 1 (α / 2)
    (Real.sqrt R + Sg) (C / lb) (db.c * (2 * Real.sqrt 2)⁻¹ ^ (1 : ℝ))
    (2 * Real.sqrt 2 * ε₀) hα (by norm_num) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (masa_bola_inferior_potencia μb Γ db.c 1 ε₀ hε₀ db.particiones) (hquad.mono fun _ h => h.2)
  have hexp (s : ℝ) : -(α / 2 * α / (2 * α + s)) =
      -(α ^ 2 / (2 * (2 * α + s))) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hexp] at hr hb
  refine ⟨?_, isBigO_de_cota_eventual _ _ C (hrate.mono fun _ hn =>
    ⟨hn.1, by positivity, hn.2⟩), ⟨hr.1, hb.1⟩, hr.2, hb.2⟩
  exact hstep.mono fun n hn => ⟨hn.1, (hholder n hn.1).1.1, (hholder n hn.1).1.2, hn.2.2⟩

#check DatosMasa38.cobertura_prefijos_ae
#check holder_residuos_de_regularidad
#check proposicion310_dim2
#print axioms DatosMasa38.cobertura_prefijos_ae
#print axioms holder_residuos_de_regularidad
#print axioms proposicion310_dim2

end TesisPINN
