import TesisPINN.OcupacionLogaritmica
import TesisPINN.Teorema38

/-! Generalización con radios logarítmicos. La parte poblacional usa
dimensiones de masa 2 y 1. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Filter Asymptotics

/-- Potencia de un radio de (3.59), para una dimensión de masa arbitraria. -/
theorem potencia_radioLog (D c s κ α : ℝ) (m : ℕ)
    (hD : 0 ≤ D) (hc : 0 < c) (hκ : 0 ≤ κ) :
    radioCoberturaLog D c s κ m ^ (2 * α) =
      (D ^ (2 * α) * (κ / c) ^ (2 * α / s)) *
        (Real.log (m : ℝ) / m) ^ (2 * α / s) := by
  have hlog := Real.log_natCast_nonneg m
  have hbase : κ * Real.log (m : ℝ) / (c * m) =
      (κ / c) * (Real.log (m : ℝ) / m) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  unfold radioCoberturaLog escalaAuxiliarLog
  rw [Real.mul_rpow hD (by positivity), ← Real.rpow_mul (by positivity),
    show (1 / s) * (2 * α) = 2 * α / s by ring, hbase,
    Real.mul_rpow (by positivity) (by positivity)]
  ring

theorem radioLog_tendsto_cero (D c s κ : ℝ) (hs : 0 < s)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => radioCoberturaLog D c s κ (m n)) atTop (nhds 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have ht := hlog.comp (tendsto_natCast_atTop_atTop.comp hm)
  have hbase : Tendsto (fun n => κ * Real.log (m n : ℝ) / (c * (m n : ℝ)))
      atTop (nhds 0) := by
    simpa [mul_div_assoc, div_div, mul_comm c] using (ht.const_mul κ).div_const c
  simpa [radioCoberturaLog, escalaAuxiliarLog] using
    (hbase.rpow_const_nhds_zero (show 0 < 1 / s by positivity)).const_mul D

/-- Factor de (3.60) en 2D, escrito directamente en función de los tamaños. -/
theorem factor_cobertura_log_dim2 (mr mb : ℕ) (Cr Cb cr cb κ : ℝ)
    (hcr : 0 < cr) (hcb : 0 < cb) (hκ : 0 < κ) (hmr : 3 ≤ mr) (hmb : 3 ≤ mb) :
    factorCoberturaCuadrado mr mb Cr Cb
      (radioCoberturaLog (Real.sqrt 2) cr 2 κ mr)
      (radioCoberturaLog (Real.sqrt 2) cb 1 κ mb) =
    3 * max ((2 * Cr * κ / cr) * Real.log (mr : ℝ))
      ((Real.sqrt 2 * Cb * κ / cb) * Real.log (mb : ℝ)) := by
  have hmr' : (0 : ℝ) < mr := Nat.cast_pos.mpr (by omega)
  have hmb' : (0 : ℝ) < mb := Nat.cast_pos.mpr (by omega)
  have hr := escalaAuxiliarLog_masa cr 2 κ mr hcr (by norm_num) hκ hmr
  have hb := escalaAuxiliarLog_masa cb 1 κ mb hcb (by norm_num) hκ hmb
  have hr' : escalaAuxiliarLog cr 2 κ mr ^ 2 = (κ * Real.log (mr : ℝ) / mr) / cr :=
    (eq_div_iff hcr.ne').2 (by simpa [Real.rpow_two, mul_comm] using hr)
  have hb' : escalaAuxiliarLog cb 1 κ mb = (κ * Real.log (mb : ℝ) / mb) / cb :=
    (eq_div_iff hcb.ne').2 (by simpa [mul_comm] using hb)
  unfold factorCoberturaCuadrado radioCoberturaLog
  rw [mul_pow, Real.sq_sqrt (by norm_num), hr', hb']
  congr 2 <;> field_simp [hcr.ne', hcb.ne', hmr'.ne', hmb'.ne']

/-- Los pesos positivos en los tamaños admisibles tienden a cero. El
factor de cobertura crece a infinito y su producto con el peso tiende a cero. -/
theorem limites_peso_log_dim2 (mr mb : ℕ → ℕ) (hmr : Tendsto mr atTop atTop)
    (hmb : Tendsto mb atTop atTop) (Cr Cb cr cb κ lr lb α : ℝ)
    (hCr : 0 < Cr) (hcr : 0 < cr) (hcb : 0 < cb)
    (hκ : 0 < κ) (hlr : 0 < lr) (hα : 0 < α) :
    let r := fun n => radioCoberturaLog (Real.sqrt 2) cr 2 κ (mr n)
    let b := fun n => radioCoberturaLog (Real.sqrt 2) cb 1 κ (mb n)
    let C := fun n => factorCoberturaCuadrado (mr n) (mb n) Cr Cb (r n) (b n)
    let a := fun n => pesoRegularizacionIgual lr lb (r n) (b n) α (C n)
    Tendsto C atTop atTop ∧ Tendsto a atTop (nhds 0) ∧
      Tendsto (fun n => C n * a n) atTop (nhds 0) ∧
      (∀ᶠ n in atTop, 0 < C n ∧ 0 < a n) := by
  intro r b C a
  have hsize := (hmr.eventually (eventually_ge_atTop (3 : ℕ))).and
    (hmb.eventually (eventually_ge_atTop (3 : ℕ)))
  have hC : Tendsto C atTop atTop := by
    have ht := Filter.Tendsto.const_mul_atTop
      (show 0 < 3 * (2 * Cr * κ / cr) by positivity)
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmr))
    apply tendsto_atTop_mono' atTop _ ht
    filter_upwards [hsize] with n hn
    change _ ≤ factorCoberturaCuadrado (mr n) (mb n) Cr Cb (r n) (b n)
    rw [factor_cobertura_log_dim2 (mr n) (mb n) Cr Cb cr cb κ hcr hcb hκ hn.1 hn.2]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  have hr := radioLog_tendsto_cero (Real.sqrt 2) cr 2 κ (by norm_num) mr hmr
  have hb := radioLog_tendsto_cero (Real.sqrt 2) cb 1 κ (by norm_num) mb hmb
  have hrLim : Tendsto (fun n => lr * r n ^ (2 * α)) atTop (nhds 0) := by
    simpa using (hr.rpow_const_nhds_zero (show 0 < 2 * α by positivity)).const_mul lr
  have hbLim : Tendsto (fun n => lb * b n ^ (2 * α)) atTop (nhds 0) := by
    simpa using (hb.rpow_const_nhds_zero (show 0 < 2 * α by positivity)).const_mul lb
  have hrpos (n : ℕ) (hn : 3 ≤ mr n) : 0 < r n := by
    have hmr' : (0 : ℝ) < mr n := Nat.cast_pos.mpr (by omega)
    have hlog : 0 < Real.log (mr n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < mr n by omega))
    dsimp [r, radioCoberturaLog, escalaAuxiliarLog]
    positivity
  have hprod : Tendsto (fun n => C n * a n) atTop (nhds 0) := by
    have hmax : Tendsto (fun n => max (lr * r n ^ (2 * α)) (lb * b n ^ (2 * α)))
        atTop (nhds 0) := by
      simpa using hrLim.max hbLim
    have hlim : Tendsto (fun n => 3 * max (lr * r n ^ (2 * α)) (lb * b n ^ (2 * α)))
        atTop (nhds 0) := by simpa using hmax.const_mul 3
    apply hlim.congr'
    filter_upwards [hsize] with n hn
    exact (factor_mul_peso_igual (mr n) (mb n) Cr Cb (r n) (b n)
      lr lb α hCr (hrpos n hn.1) (by omega)).symm
  have ha : ∀ᶠ n in atTop, 1 ≤ C n ∧ 0 < a n := by
    filter_upwards [hC.eventually (eventually_ge_atTop (1 : ℝ)), hsize] with n hn hs
    exact ⟨hn, peso38_pos (mr n) (mb n) Cr Cb (r n) (b n) lr lb α
      hCr (by omega) (hrpos n hs.1) hlr⟩
  refine ⟨hC, ?_, hprod, ha.mono fun _ h => ⟨zero_lt_one.trans_le h.1, h.2⟩⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod
    (ha.mono fun _ h => h.2.le) (ha.mono fun _ h => le_mul_of_one_le_left h.2.le h.1)

/-- Familia determinista con los dos pesos de (3.60). -/
def Operadores38.baseLog {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Operadores38 H X Y) (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (Cr Cb cr cb κ lr lb α : ℝ) (hCr : 0 < Cr) (hcr : 0 < cr)
    (hκ : 0 < κ) (hlr : 0 < lr) (hlb : 0 < lb) : ProblemaPINN H X Y mr mb :=
  let r := radioCoberturaLog (Real.sqrt 2) cr 2 κ mr
  let b := radioCoberturaLog (Real.sqrt 2) cb 1 κ mb
  let C := factorCoberturaCuadrado mr mb Cr Cb r b
  let a := pesoRegularizacionIgual lr lb r b α C
  have hC : 0 ≤ C := mul_nonneg (by norm_num)
    ((show 0 ≤ Cr * (mr : ℝ) * r ^ 2 by positivity).trans (le_max_left _ _))
  have hr : 0 ≤ r := by
    dsimp [r, radioCoberturaLog, escalaAuxiliarLog]
    have := Real.log_natCast_nonneg mr
    positivity
  have ha : 0 ≤ a :=
    (div_nonneg (show 0 ≤ 3 * lr * r ^ (2 * α) by positivity) hC).trans (le_max_left _ _)
  { D.base μr μb mr mb hmr hmb Cr Cb cr cb lr lb α hCr hcr hlr hlb with
    regularizadorR := a
    regularizadorB := a
    regularizadorR_nonneg := ha
    regularizadorB_nonneg := ha }

private theorem cota_con_pesos_iguales
    {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {mr mb : ℕ}
    (P : ProblemaPINN H X Y mr mb) (h : H) (r b α Cr Cb Sf Sg : ℝ)
    (hr : 0 < r) (hCr : 0 < Cr)
    (hObj : ObjetivoCoberturaIntegral P r b α Cr Cb Sf Sg h) :
    let C := factorCoberturaCuadrado mr mb Cr Cb r b
    let a := pesoRegularizacionIgual P.lambdaR P.lambdaB r b α C
    P.regularizadorR = a → P.regularizadorB = a →
      P.perdidaPoblacional h ≤ C * P.funcionalRegularizado h +
        3 * P.lambdaR * r ^ (2 * α) * Sf ^ 2 + 3 * P.lambdaB * b ^ (2 * α) * Sg ^ 2 := by
  intro C a haR haB
  have hC : 0 ≤ C := mul_nonneg (by norm_num)
    ((show 0 ≤ Cr * (mr : ℝ) * r ^ 2 by positivity).trans (le_max_left _ _))
  have hR := mul_le_mul_of_nonneg_right
    (pesoInterior_le_igual P.lambdaR P.lambdaB r b α C) (sq_nonneg (P.seminormaL h))
  have hB := mul_le_mul_of_nonneg_right
    (pesoFrontera_le_igual P.lambdaR P.lambdaB r b α C) (sq_nonneg (P.seminormaB h))
  have hJ : P.perdidaEmpirica h + pesoCobertura P.lambdaR r α C * P.regularidadInterior h +
      pesoCobertura P.lambdaB b α C * P.regularidadFrontera h ≤ P.funcionalRegularizado h := by
    unfold ProblemaPINN.funcionalRegularizado
    rw [haR, haB]
    exact add_le_add (add_le_add_right hR _) hB
  exact hObj.trans (add_le_add_left (add_le_add_left (mul_le_mul_of_nonneg_left hJ hC) _) _)

/-- Proposición 3.14 para residuos escalares en dimensión dos.
La cota finita vale simultáneamente para todos los candidatos admisibles.
La tasa casi segura usa comparadores exactos y mínimos globales del
funcional con los pesos logarítmicos. -/
theorem proposicion314_dim2
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
    (κ lr lb α Sf Sg : ℝ) (hκ : 2 < κ) (hlr : 0 < lr) (hlb : 0 < lb)
    (hα : 0 < α) (_hαone : α ≤ 1)
    (Hm : ℕ → Set H) (hm v : ∀ n, Ω → Hm n)
    (_hMeasHm : ∀ n, Measurable (fun ω => (hm n ω : H)))
    (_hMeasV : ∀ n, Measurable (fun ω => (v n ω : H))) :
    let base := fun n => D.baseLog μr μb (mr n) (mb n) (hmr n) (hmb n)
      dr.C db.C dr.c db.c κ lr lb α dr.C_pos dr.c_pos (by linarith) hlr hlb
    let Pn := problemaMuestral mr mb base sr.Z sb.Z
    let r := fun n => radioCoberturaLog (Real.sqrt 2) dr.c 2 κ (mr n)
    let b := fun n => radioCoberturaLog (Real.sqrt 2) db.c 1 κ (mb n)
    let C := fun n => factorCoberturaCuadrado (mr n) (mb n) dr.C db.C (r n) (b n)
    let admR := fun n => RadioLogAdmisible (Real.sqrt 2) dr.c 2 κ ε₀ ε₀ (mr n)
    let admB := fun n => RadioLogAdmisible (Real.sqrt 2) db.c 1 κ ε₀ ε₀ (mb n)
    (∀ n, CotasHolder (base n) (Hm n) U Γ α Sf Sg) →
    (∀ n, admR n → admB n → ∃ E : Set Ω, MeasurableSet E ∧
      1 - mayoranteFalloLog κ (mr n) - mayoranteFalloLog κ (mb n) ≤ P.real E ∧
      ∀ ω ∈ E, ∀ h ∈ Hm n,
        (Pn ω n).perdidaPoblacional h ≤ C n * (Pn ω n).funcionalRegularizado h +
          3 * lr * r n ^ (2 * α) * Sf ^ 2 + 3 * lb * b n ^ (2 * α) * Sg ^ 2) ∧
    (∀ᵐ ω ∂P, ∀ᶠ n in atTop, admR n ∧ admB n ∧
      MuestrasCubren U (fun i : Fin (mr n) => sr.Z i ω) (r n) ∧
      MuestrasCubren Γ (fun i : Fin (mb n) => sb.Z i ω) (b n)) ∧
    ((∀ᵐ ω ∂P, ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n in atTop,
        (Pn ω n).EsMinimizadorGlobal (Hm n) (hm n ω : H) ∧
        (Pn ω n).ComparadorExacto (Hm n) (v n ω : H) ∧
        (Pn ω n).regularidadTotal (v n ω : H) ≤ R) →
      ∀ᵐ ω ∂P, (fun n => (Pn ω n).perdidaPoblacional (hm n ω : H)) =O[atTop]
        (fun n => (Real.log (mr n : ℝ) / mr n) ^ α +
          (Real.log (mb n : ℝ) / mb n) ^ (2 * α))) := by
  intro base Pn r b C admR admB hHolder
  have hκpos : 0 < κ := by linarith
  have hD : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hlogR := lema313_cobertura_logaritmica P μr sr.Z sr.medible sr.indep sr.ley
    U (Real.sqrt 2) dr.c 2 κ ε₀ ε₀ hD dr.c_pos (by norm_num) hκ hε₀ hε₀
    dr.particiones.particionesOcupacionLog mr hgr
  have hlogB := lema313_cobertura_logaritmica P μb sb.Z sb.medible sb.indep sb.ley
    Γ (Real.sqrt 2) db.c 1 κ ε₀ ε₀ hD db.c_pos (by norm_num) hκ hε₀ hε₀
    db.particiones.particionesOcupacionLog mb hgb
  have hcov : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, admR n ∧ admB n ∧
      MuestrasCubren U (fun i : Fin (mr n) => sr.Z i ω) (r n) ∧
      MuestrasCubren Γ (fun i : Fin (mb n) => sb.Z i ω) (b n) :=
    (hlogR.2.and hlogB.2).mono fun _ h =>
      (h.1.and h.2).mono fun _ hn => ⟨hn.1.1, hn.2.1, hn.1.2, hn.2.2⟩
  have hsupR := muestras_en_soporte_ae P μr sr.Z U dr.concentrada sr.medible sr.ley
  have hsupB := muestras_en_soporte_ae P μb sb.Z Γ db.concentrada sb.medible sb.ley
  let S : Set Ω := {ω | (∀ i, sr.Z i ω ∈ U) ∧ ∀ j, sb.Z j ω ∈ Γ}
  have hmS : MeasurableSet S := by
    rw [show S = (⋂ i, sr.Z i ⁻¹' U) ∩ (⋂ j, sb.Z j ⁻¹' Γ) by
      ext ω
      simp [S]]
    exact (MeasurableSet.iInter fun i => dr.medible.preimage (sr.medible i)).inter
      (MeasurableSet.iInter fun j => db.medible.preimage (sb.medible j))
  have hSzero : P.real Sᶜ = 0 := by
    rw [measureReal_def, mem_ae_iff.mp (show S ∈ ae P from hsupR.and hsupB),
      ENNReal.toReal_zero]
  have hContF := continuo_de_cota_holder U D.f Sf α hα (hHolder 0).2.2.2.1
  have hContG := continuo_de_cota_holder Γ D.g Sg α hα (hHolder 0).2.2.2.2
  have hInt (ω : Ω) (n : ℕ) (h : H) (hh : h ∈ Hm n) : (Pn ω n).PoblacionIntegrable h := by
    have hCand := (hHolder n).2.2.1 h hh
    have hContL := continuo_de_cota_holder U (D.L h) _ α hα hCand.2.2.1
    have hContB := continuo_de_cota_holder Γ (D.B h) _ α hα hCand.2.2.2
    exact poblacionIntegrable_de_holder_acotado (Pn ω n) (Hm n) U Γ
      dr.acotado db.acotado (soporte_no_vacio μr U dr.concentrada)
      (soporte_no_vacio μb Γ db.concentrada) dr.concentrada db.concentrada
      α Sf Sg hα (hHolder n) h hh
      (aestronglyMeasurable_residuo_sq_de_continuidad μr U dr.medible
        dr.concentrada _ _ hContL hContF)
      (aestronglyMeasurable_residuo_sq_de_continuidad μb Γ db.medible
        db.concentrada _ _ hContB hContG)
  refine ⟨?_, hcov, ?_⟩
  · intro n hnR hnB
    obtain ⟨Kr, cellsR, hmR, hpR, hcR⟩ := hlogR.1 (mr n) hnR
    obtain ⟨Kb, cellsB, hmB, hpB, hcB⟩ := hlogB.1 (mb n) hnB
    let Er := todasCeldasOcupadas sr.Z (mr n) cellsR
    let Eb := todasCeldasOcupadas sb.Z (mb n) cellsB
    let E := (Er ∩ Eb) ∩ S
    have hmEr : MeasurableSet Er := by simpa only [Er, compl_compl] using hmR.compl
    have hmEb : MeasurableSet Eb := by simpa only [Eb, compl_compl] using hmB.compl
    have hmE : MeasurableSet E := (hmEr.inter hmEb).inter hmS
    have hpE : P.real Eᶜ ≤ mayoranteFalloLog κ (mr n) + mayoranteFalloLog κ (mb n) := by
      change P.real ((Er ∩ Eb) ∩ S)ᶜ ≤ _
      rw [Set.compl_inter, Set.compl_inter]
      have hp := measureReal_union_le (μ := P) (Erᶜ ∪ Ebᶜ) Sᶜ
      rw [hSzero, add_zero] at hp
      exact hp.trans ((measureReal_union_le Erᶜ Ebᶜ).trans (add_le_add hpR hpB))
    refine ⟨E, hmE, ?_, ?_⟩
    · rw [probReal_compl_eq_one_sub hmE] at hpE
      linarith
    · intro ω hω h hh
      obtain ⟨⟨hωR, hωB⟩, hωS⟩ := hω
      have hobj := objetivoCoberturaIntegral_de_hipotesis (Pn ω n) (Hm n) U Γ
        dr.medible db.medible dr.concentrada db.concentrada
        α (r n) (b n) ε₀ ε₀ dr.C db.C Sf Sg hα
        hnR.2.2.2.2.1 hnB.2.2.2.2.1 hnR.2.2.2.2.2 hnB.2.2.2.2.2 dr.C_pos db.C_pos
        (fun i => hωS.1 i) (fun i => hωS.2 i) (hcR ω hωR) (hcB ω hωB)
        dr.superior db.superior (hHolder n) h hh (hInt ω n h hh)
      exact cota_con_pesos_iguales (Pn ω n) h (r n) (b n) α dr.C db.C Sf Sg
        hnR.2.2.2.2.1 dr.C_pos hobj rfl rfl
  · intro hvar
    filter_upwards [hcov, hsupR, hsupB, hvar] with ω hcovω hsupRω hsupBω hvarω
    obtain ⟨R, hR, hvarω⟩ := hvarω
    let Ar := 3 * lr * ((Real.sqrt 2) ^ (2 * α) * (κ / dr.c) ^ α) * (R + Sf ^ 2)
    let Ab := 3 * lb * ((Real.sqrt 2) ^ (2 * α) * (κ / db.c) ^ (2 * α)) * (R + Sg ^ 2)
    have hcr := dr.c_pos
    have hcb := db.c_pos
    have hAr : 0 ≤ Ar := by dsimp [Ar]; positivity
    have hAb : 0 ≤ Ab := by dsimp [Ab]; positivity
    apply isBigO_de_cota_eventual _ _ (Ar + Ab)
    filter_upwards [hcovω, hvarω] with n hn hmin
    obtain ⟨hnR, hnB, hcR, hcB⟩ := hn
    have hrpos : 0 < r n := hnR.2.2.2.2.1
    have hbpos : 0 < b n := hnB.2.2.2.2.1
    have hI := hInt ω n (hm n ω : H) (hm n ω).2
    have hpop := perdidaPoblacional_minimizador_bajo_cobertura (Pn ω n) (Hm n) U Γ
      dr.medible db.medible dr.concentrada db.concentrada
      α (r n) (b n) ε₀ ε₀ dr.C db.C Sf Sg R hα hrpos hbpos
      hnR.2.2.2.2.2 hnB.2.2.2.2.2 dr.C_pos db.C_pos
      (fun i => hsupRω i) (fun i => hsupBω i) hcR hcB dr.superior db.superior
      (hHolder n) _ _ hmin.1 hmin.2.1 hmin.2.2 hI rfl rfl
    have hCa := factor_mul_peso_igual (mr n) (mb n) dr.C db.C (r n) (b n)
      lr lb α dr.C_pos hrpos (hmr n)
    change (Pn ω n).perdidaPoblacional (hm n ω : H) ≤
      C n * (pesoRegularizacionIgual lr lb (r n) (b n) α (C n) * R) +
        3 * lr * r n ^ (2 * α) * Sf ^ 2 + 3 * lb * b n ^ (2 * α) * Sg ^ 2 at hpop
    rw [← mul_assoc, hCa] at hpop
    have hrr : 0 ≤ lr * r n ^ (2 * α) := by positivity
    have hbb : 0 ≤ lb * b n ^ (2 * α) := by positivity
    have hsum : (Pn ω n).perdidaPoblacional (hm n ω : H) ≤
        3 * lr * r n ^ (2 * α) * (R + Sf ^ 2) + 3 * lb * b n ^ (2 * α) * (R + Sg ^ 2) := by
      have hmax := max_le (le_add_of_nonneg_right hbb) (le_add_of_nonneg_left hrr)
      have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax
        (by norm_num : (0 : ℝ) ≤ 3)) hR
      nlinarith only [hpop, hmul]
    have hpr := potencia_radioLog (Real.sqrt 2) dr.c 2 κ α (mr n) hD.le dr.c_pos hκpos.le
    have hpb := potencia_radioLog (Real.sqrt 2) db.c 1 κ α (mb n) hD.le db.c_pos hκpos.le
    rw [show 2 * α / (2 : ℝ) = α by ring] at hpr
    rw [div_one] at hpb
    change r n ^ (2 * α) = _ at hpr
    change b n ^ (2 * α) = _ at hpb
    rw [hpr, hpb] at hsum
    have hnr : 0 ≤ (Real.log (mr n : ℝ) / mr n) ^ α :=
      Real.rpow_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) _
    have hnb : 0 ≤ (Real.log (mb n : ℝ) / mb n) ^ (2 * α) :=
      Real.rpow_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) _
    refine ⟨(Pn ω n).perdidaPoblacional_nonneg _ hI, add_nonneg hnr hnb, ?_⟩
    calc
      _ ≤ Ar * (Real.log (mr n : ℝ) / mr n) ^ α +
          Ab * (Real.log (mb n : ℝ) / mb n) ^ (2 * α) := by
        dsimp [Ar, Ab]
        nlinarith only [hsum]
      _ ≤ _ := by nlinarith only [mul_nonneg hAr hnb, mul_nonneg hAb hnr]

#check potencia_radioLog
#check factor_cobertura_log_dim2
#check limites_peso_log_dim2
#check proposicion314_dim2
#print axioms potencia_radioLog
#print axioms factor_cobertura_log_dim2
#print axioms limites_peso_log_dim2
#print axioms proposicion314_dim2

end TesisPINN
