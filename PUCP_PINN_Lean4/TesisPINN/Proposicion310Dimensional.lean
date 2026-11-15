import TesisPINN.Teorema38Dimensional
import TesisPINN.Proposicion310
import TesisPINN.Corolario312

/-! Proposición 3.10 con los exponentes de masa libres. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Set Filter Asymptotics
open scoped Topology

/-- El peso común de (3.23) tiende a cero en las escalas de P3.10. -/
theorem pesoRaizDimensional_tendsto
    (mr mb : ℕ → ℕ) (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (hTr : Tendsto mr atTop atTop) (hTb : Tendsto mb atTop atTop)
    (D Cr Cb cr cb sr sb lr lb α : ℝ) (hD : 0 < D)
    (hCr : 0 < Cr) (hcr : 0 < cr) (hcb : 0 < cb) (hsr : 0 < sr) (hsb : 0 < sb)
    (hlr : 0 < lr) (hα : 0 < α) :
    let rr := fun n => radioRaizDimensional D cr sr (mr n)
    let rb := fun n => radioRaizDimensional D cb sb (mb n)
    let F := fun n => factorCoberturaDimensional (mr n) (mb n) Cr Cb (rr n) (rb n) sr sb
    Tendsto (fun n => pesoRegularizacionIgual lr lb (rr n) (rb n) α (F n)) atTop (𝓝 0) := by
  intro rr rb F
  have hpos (n : ℕ) : 0 < rr n := radioRaizDimensional_pos _ _ _ _ hD hcr (hmr n)
  have hF (n : ℕ) : 0 < F n := factorCoberturaDimensional_pos _ _ _ _ _ _ _ _ (hmr n) hCr (hpos n)
  have hlim (m : ℕ → ℕ) (c s : ℝ) (hc : 0 < c) (hs : 0 < s)
      (hm : ∀ n, 0 < m n) (hT : Tendsto m atTop atTop) :
      Tendsto (fun n => radioRaizDimensional D c s (m n)) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun x hx => Eventually.of_forall fun n =>
      hx.trans (radioRaizDimensional_pos _ _ _ _ hD hc (hm n)), fun x hx => ?_⟩
    exact (radioRaizDimensional_eventual D c s (x / 2) m hD hc hs (by positivity) hm hT).mono
      (fun _ hn => hn.trans_lt (by linarith))
  have hsR : Tendsto (fun n => 3 * lr * rr n ^ (2 * α)) atTop (𝓝 0) := by
    simpa using ((hlim mr cr sr hcr hsr hmr hTr).rpow_const_nhds_zero
      (show 0 < 2 * α by positivity)).const_mul (3 * lr)
  have hsB : Tendsto (fun n => 3 * lb * rb n ^ (2 * α)) atTop (𝓝 0) := by
    simpa using ((hlim mb cb sb hcb hsb hmb hTb).rpow_const_nhds_zero
      (show 0 < 2 * α by positivity)).const_mul (3 * lb)
  let a := fun n => pesoRegularizacionIgual lr lb (rr n) (rb n) α (F n)
  have hprod : Tendsto (fun n => F n * a n) atTop (𝓝 0) := by
    have h := hsR.max hsB
    refine (show Tendsto (fun n => max (3 * lr * rr n ^ (2 * α)) (3 * lb * rb n ^ (2 * α)))
      atTop (𝓝 0) by simpa using h).congr' (Eventually.of_forall fun n => ?_)
    exact (producto_peso_igual_dimensional _ _ _ _ _ _ (hF n)).symm
  have hcoef : 0 < 3 * (Cr / cr * D ^ sr) := by positivity
  have hmrReal : Tendsto (fun n => (mr n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hTr
  have hlarge := ((Real.tendsto_sqrt_atTop.comp hmrReal).const_mul_atTop hcoef).eventually
    (eventually_ge_atTop (1 : ℝ))
  have hfLarge : ∀ᶠ n in atTop, 1 ≤ F n := by
    filter_upwards [hlarge] with n hn
    show _ ≤ factorCoberturaDimensional (mr n) (mb n) Cr Cb (rr n) (rb n) sr sb
    rw [factorCoberturaDimensional_raiz _ _ _ _ _ _ _ _ _ hD.le hcr hcb hsr hsb (hmr n) (hmb n)]
    exact hn.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
  have ha (n : ℕ) : 0 ≤ a n := (pesoCobertura_nonneg _ _ _ _ hlr.le (hpos n).le (hF n).le).trans
    (le_max_left _ _)
  exact squeeze_zero' (Eventually.of_forall ha) (hfLarge.mono fun n hn =>
    le_mul_of_one_le_left (ha n) hn) hprod

/-- (3.39)–(3.41) con radios y masas independientes. La misma comparación
vale con radios raíz o logarítmicos y sus correspondientes pesos iguales. -/
theorem cotas310_dimensional_bajo_cobertura
    {H X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (μr : Measure X) [IsProbabilityMeasure μr] (μb : Measure Y) [IsProbabilityMeasure μb]
    (U : Set X) (Γ : Set Y) (D sr sb ε₀ : ℝ)
    (dr : DatosMasaDimensional μr U D sr ε₀) (db : DatosMasaDimensional μb Γ D sb ε₀)
    (op : Operadores38 H X Y) (Hm : Set H)
    {mr mb : ℕ} (hmr : 0 < mr) (hmb : 0 < mb)
    (lr lb α Sf Sg rr rb ε δ R : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (hr : 0 < rr) (hb : 0 < rb) (hr₀ : rr ≤ ε₀) (hb₀ : rb ≤ ε₀)
    (xr : Fin mr → X) (xb : Fin mb → Y) (h v : H) :
    let F := factorCoberturaDimensional mr mb dr.C db.C rr rb sr sb
    let a := pesoRegularizacionIgual lr lb rr rb α F
    let P := op.problemaDimensional μr μb hmr hmb lr lb α rr rb F hlr hlb hr hb
      (factorCoberturaDimensional_pos _ _ _ _ _ _ _ _ hmr dr.C_pos hr) true xr xb
    op.CotasHolder34 Hm U Γ α Sf Sg → CoberturaDimensional P U Γ rr rb →
    P.EsMinimizadorAproximado Hm h δ → v ∈ Hm →
    P.perdidaEmpirica v ≤ ε → P.regularidadTotal v ≤ R →
    P.regularidadTotal h ≤ R + (ε + δ) / a ∧
    P.funcionalRegularizado h ≤ a * (R + (ε + δ) / a) ∧
    P.perdidaPoblacional h ≤ F * (a * (R + (ε + δ) / a)) +
      3 * lr * rr ^ (2 * α) * Sf ^ 2 + 3 * lb * rb ^ (2 * α) * Sg ^ 2 := by
  intro F a P hHolder hcov hmin hv hε hR
  have hF : 0 < F := factorCoberturaDimensional_pos _ _ _ _ _ _ _ _ hmr dr.C_pos hr
  have ha : 0 < a := (show 0 < pesoCobertura lr rr α F from by unfold pesoCobertura; positivity).trans_le
    (le_max_left _ _)
  obtain ⟨hreg, hJ⟩ := P.cotas_minimizador_aproximado Hm h v a ε δ R ha rfl rfl hmin hv hε hR
  have hpop := cota34_dimensional_bajo_cobertura μr μb U Γ D sr sb ε₀ dr db op Hm hmr hmb
    lr lb α Sf Sg rr rb hlr hlb hα hr hb hr₀ hb₀ true xr xb hHolder hcov h hmin.1
  change P.perdidaPoblacional h ≤ F * P.funcionalRegularizado h +
    3 * lr * rr ^ (2 * α) * Sf ^ 2 + 3 * lb * rb ^ (2 * α) * Sg ^ 2 at hpop
  exact ⟨hreg, hJ, hpop.trans (add_le_add_left
    (add_le_add_left (mul_le_mul_of_nonneg_left hJ hF.le) _) _)⟩

/-- P3.10 con las tolerancias (3.42), conservando los tamaños originales. -/
theorem proposicion310_dimensional
    {Ω H X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    [PseudoMetricSpace X] [PseudoMetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] (U : Set X) (Γ : Set Y) (D sr sb ε₀ : ℝ)
    (dr : DatosMasaDimensional μr U D sr ε₀) (db : DatosMasaDimensional μb Γ D sb ε₀)
    (Zr : Muestreo38 P μr) (Zb : Muestreo38 P μb) (op : Operadores38 H X Y)
    (hD : 1 ≤ D) (hsr : 0 < sr) (hsb : 0 < sb) (hε₀ : 0 < ε₀)
    (mr mb : ℕ → ℕ) (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (hgr : ∀ᶠ n in atTop, n ≤ mr n) (hgb : ∀ᶠ n in atTop, n ≤ mb n)
    (lr lb α Sf Sg Ksize : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α) (hKsize : 0 < Ksize)
    (hrel : ∀ᶠ n in atTop, (mr n : ℝ) ≤ Ksize * (mb n : ℝ) ^ (sr / sb))
    (Hm : ℕ → Set H) (h v : ∀ n, Ω → Hm n)
    (_hMeas : ∀ n, Measurable (fun ω => (h n ω : H)))
    (_vMeas : ∀ n, Measurable (fun ω => (v n ω : H)))
    (ε δ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hδ : ∀ n, 0 ≤ δ n)
    (Rstar : Ω → ℝ) (K : ℝ) :
    let rr := fun n => radioRaizDimensional D dr.c sr (mr n)
    let rb := fun n => radioRaizDimensional D db.c sb (mb n)
    let F := fun n => factorCoberturaDimensional (mr n) (mb n) dr.C db.C (rr n) (rb n) sr sb
    let a := fun n => pesoRegularizacionIgual lr lb (rr n) (rb n) α (F n)
    let Pn := fun ω n => op.problemaRaizDimensional μr μb (hmr n) (hmb n) D sr sb dr.C db.C
      dr.c db.c lr lb α (zero_lt_one.trans_le hD) dr.C_pos dr.c_pos db.c_pos hlr hlb true
      (fun i => Zr.Z i ω) (fun i => Zb.Z i ω)
    (∀ n, op.CotasHolder34 (Hm n) U Γ α Sf Sg) →
    (∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (Pn ω n).perdidaEmpirica (v n ω : H) ≤ ε n ∧
      (Pn ω n).regularidadTotal (v n ω : H) ≤ Rstar ω ∧
      (Pn ω n).EsMinimizadorAproximado (Hm n) (h n ω : H) (δ n)) →
    (∀ᶠ n in atTop, ε n + δ n ≤ K * a n) →
    ∀ᵐ ω ∂P,
      let er := fun n x => op.L (h n ω : H) x - op.f x
      let eb := fun n y => op.B (h n ω : H) y - op.g y
      let loss := fun n => (Pn ω n).perdidaPoblacional (h n ω : H)
      (∀ᶠ n in atTop, (Pn ω n).regularidadTotal (h n ω : H) ≤ Rstar ω + K ∧
        op.seminormaL (h n ω : H) ≤ Real.sqrt (Rstar ω + K) ∧
        op.seminormaB (h n ω : H) ≤ Real.sqrt (Rstar ω + K) ∧
        loss n ≤ F n * (a n * (Rstar ω + K)) +
          3 * lr * rr n ^ (2 * α) * Sf ^ 2 + 3 * lb * rb n ^ (2 * α) * Sg ^ 2) ∧
      (loss =O[atTop] (fun n => (mr n : ℝ) ^ (-(α / sr)))) ∧
      (Tendsto (fun n => supResiduo U (er n)) atTop (𝓝 0) ∧
       Tendsto (fun n => supResiduo Γ (eb n)) atTop (𝓝 0)) ∧
      (((fun n => supResiduo U (er n)) =O[atTop]
         (fun n => (mr n : ℝ) ^ (-(α ^ 2 / (sr * (2 * α + sr)))))) ∧
       ((fun n => supResiduo Γ (eb n)) =O[atTop]
         (fun n => (mr n : ℝ) ^ (-(α ^ 2 / (sr * (2 * α + sb))))))) := by
  intro rr rb F a Pn hHolder hvar htol
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hmrTop := tendsto_atTop_mono' atTop hgr tendsto_id
  have hmbTop := tendsto_atTop_mono' atTop hgb tendsto_id
  have hsmallR := radioRaizDimensional_eventual D dr.c sr ε₀ mr hDp dr.c_pos hsr hε₀ hmr hmrTop
  have hsmallB := radioRaizDimensional_eventual D db.c sb ε₀ mb hDp db.c_pos hsb hε₀ hmb hmbTop
  have hcovR := cobertura_raiz_dimensional_ae P μr Zr U D sr ε₀ dr hD hsr hε₀ mr hmr hgr
  have hcovB := cobertura_raiz_dimensional_ae P μb Zb Γ D sb ε₀ db hD hsb hε₀ mb hmb hgb
  have hsuR := muestras_en_soporte_ae P μr Zr.Z U dr.concentrada Zr.medible Zr.ley
  have hsuB := muestras_en_soporte_ae P μb Zb.Z Γ db.concentrada Zb.medible Zb.ley
  have hr (n : ℕ) : 0 < rr n := radioRaizDimensional_pos _ _ _ _ hDp dr.c_pos (hmr n)
  have hb (n : ℕ) : 0 < rb n := radioRaizDimensional_pos _ _ _ _ hDp db.c_pos (hmb n)
  have hF (n : ℕ) : 0 < F n := factorCoberturaDimensional_pos _ _ _ _ _ _ _ _ (hmr n) dr.C_pos (hr n)
  have ha (n : ℕ) : 0 < a n := (show 0 < pesoCobertura lr (rr n) α (F n) from by
    have hr' := hr n
    have hF' := hF n
    unfold pesoCobertura
    positivity).trans_le (le_max_left _ _)
  have hK : 0 ≤ K := by
    obtain ⟨n, hn⟩ := htol.exists
    exact nonneg_of_mul_nonneg_left ((add_nonneg (hε n) (hδ n)).trans hn) (ha n)
  filter_upwards [hvar, hcovR, hcovB, hsuR, hsuB] with ω hvarω hcR hcB hsrω hsbω
  obtain ⟨n₀, _, hRv, _⟩ := hvarω.exists
  have hRstar : 0 ≤ Rstar ω := ((Pn ω n₀).regularidadTotal_nonneg _).trans hRv
  let R := Rstar ω + K
  have hR : 0 ≤ R := add_nonneg hRstar hK
  let er := fun n x => op.L (h n ω : H) x - op.f x
  let eb := fun n y => op.B (h n ω : H) y - op.g y
  let loss := fun n => (Pn ω n).perdidaPoblacional (h n ω : H)
  have hstep : ∀ᶠ n in atTop, (Pn ω n).regularidadTotal (h n ω : H) ≤ R ∧
      loss n ≤ F n * (a n * R) + 3 * lr * rr n ^ (2 * α) * Sf ^ 2 +
        3 * lb * rb n ^ (2 * α) * Sg ^ 2 := by
    filter_upwards [hvarω, hcR, hcB, hsmallR, hsmallB, htol] with n hv hcr hcb hrr hbb hn
    obtain ⟨hvε, hvR, hmin⟩ := hv
    have hh := cotas310_dimensional_bajo_cobertura μr μb U Γ D sr sb ε₀ dr db op (Hm n)
      (hmr n) (hmb n) lr lb α Sf Sg (rr n) (rb n) (ε n) (δ n) (Rstar ω) hlr hlb hα
      (hr n) (hb n) hrr hbb _ _ _ _ (hHolder n)
      ⟨fun i => hsrω i, fun i => hsbω i, hcr, hcb⟩ hmin (v n ω).2 hvε hvR
    have hκ : Rstar ω + (ε n + δ n) / a n ≤ R :=
      add_le_add_right ((div_le_iff₀ (ha n)).2 hn) _
    refine ⟨hh.1.trans hκ, hh.2.2.trans ?_⟩
    exact add_le_add_left (add_le_add_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hκ (ha n).le) (hF n).le) _) _
  have hSpecs := hstep.mono fun n hn =>
    holder_residuos_de_regularidad (Pn ω n) (Hm n) U Γ α Sf Sg R (hHolder n)
      _ (h n ω).2 hn.1
  have hInt (n : ℕ) : (Pn ω n).PoblacionIntegrable (h n ω : H) := by
    have hh := (hHolder n).2.2.1 _ (h n ω).2
    exact poblacionIntegrable_de_holder_acotado (Pn ω n) (Hm n) U Γ dr.acotado db.acotado
      (soporte_no_vacio μr U dr.concentrada) (soporte_no_vacio μb Γ db.concentrada)
      dr.concentrada db.concentrada α Sf Sg hα (hHolder n) _ (h n ω).2
      (aestronglyMeasurable_residuo_sq_de_continuidad μr U dr.medible dr.concentrada _ _
        (continuo_de_cota_holder U _ _ α hα hh.2.2.1)
        (continuo_de_cota_holder U _ Sf α hα (hHolder n).2.2.2.1))
      (aestronglyMeasurable_residuo_sq_de_continuidad μb Γ db.medible db.concentrada _ _
        (continuo_de_cota_holder Γ _ _ α hα hh.2.2.2)
        (continuo_de_cota_holder Γ _ Sg α hα (hHolder n).2.2.2.2))
  let C := constante38Dimensional D dr.c db.c sr sb lr lb α Sf Sg R Ksize
  let b := fun n => (mr n : ℝ) ^ (-(α / sr))
  have hLos : ∀ᶠ n in atTop, loss n ≤ C * b n := by
    filter_upwards [hstep, hrel] with n hn hrel'
    have hp := hn.2
    have hprod : F n * a n = max (3 * lr * rr n ^ (2 * α)) (3 * lb * rb n ^ (2 * α)) :=
      producto_peso_igual_dimensional _ _ _ _ _ _ (hF n)
    rw [← mul_assoc, hprod] at hp
    have hpR := (hr n).le
    have hpB := (hb n).le
    have hmax : max (3 * lr * rr n ^ (2 * α)) (3 * lb * rb n ^ (2 * α)) ≤
        3 * lr * rr n ^ (2 * α) + 3 * lb * rb n ^ (2 * α) :=
      max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
    have hsum : loss n ≤ 3 * lr * rr n ^ (2 * α) * (R + Sf ^ 2) +
        3 * lb * rb n ^ (2 * α) * (R + Sg ^ 2) := by
      linarith only [hp, mul_le_mul_of_nonneg_right hmax hR]
    exact cota_dimensional_de_radios D dr.c db.c sr sb lr lb α Sf Sg R Ksize _ (mr n) (mb n) hDp.le
      dr.c_pos db.c_pos hsr hsb hlb.le hα hR hKsize (hmr n) (hmb n) hrel' hsum
  have hb₀ (n : ℕ) : 0 ≤ b n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hO : loss =O[atTop] b := isBigO_de_cota_eventual _ _ C
    (hLos.mono fun n hn => ⟨(Pn ω n).perdidaPoblacional_nonneg _ (hInt n), hb₀ n, hn⟩)
  have hEr := energia_isBigO_de_perdida μr er lr C hlr loss b hb₀ hLos
    (fun n => le_add_of_nonneg_right (mul_nonneg hlb.le (integral_nonneg fun _ => sq_nonneg (eb n _))))
  have hEb := energia_isBigO_de_perdida μb eb lb C hlb loss b hb₀ hLos
    (fun n => le_add_of_nonneg_left (mul_nonneg hlr.le (integral_nonneg fun _ => sq_nonneg (er n _))))
  have hSf := (hHolder 0).1
  have hSg := (hHolder 0).2.1
  have hkr := dr.c_pos
  have hkb := db.c_pos
  have hI := lema39_tasa μr U dr.medible (Real.sqrt R + Sf) α
    (dr.c * (2 * D)⁻¹ ^ sr) sr (2 * D * ε₀) (by positivity) hα (by positivity) (by positivity)
    (masa_bola_inferior_dimensional μr U D dr.c sr ε₀ hDp dr.particiones) hsr (α / sr) (by positivity)
    er mr hmrTop (hSpecs.mono fun n hn => ⟨(hInt n).1, hn.2.1⟩) hEr
  have hB := lema39_tasa μb Γ db.medible (Real.sqrt R + Sg) α
    (db.c * (2 * D)⁻¹ ^ sb) sb (2 * D * ε₀) (by positivity) hα (by positivity) (by positivity)
    (masa_bola_inferior_dimensional μb Γ D db.c sb ε₀ hDp db.particiones) hsb (α / sr) (by positivity)
    eb mr hmrTop (hSpecs.mono fun n hn => ⟨(hInt n).2, hn.2.2⟩) hEb
  have hexp (s : ℝ) : α * (α / sr) / (2 * α + s) = α ^ 2 / (sr * (2 * α + s)) := by
    rw [← mul_div_assoc, div_div]
    congr 1
    ring
  rw [hexp sr] at hI
  rw [hexp sb] at hB
  have hmReal : Tendsto (fun n => (mr n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hmrTop
  refine ⟨?_, hO, ⟨hI.trans_tendsto ((tendsto_rpow_neg_atTop (by positivity)).comp hmReal),
    hB.trans_tendsto ((tendsto_rpow_neg_atTop (by positivity)).comp hmReal)⟩, hI, hB⟩
  filter_upwards [hstep, hSpecs] with n hs hspec
  exact ⟨hs.1, hspec.1.1, hspec.1.2, hs.2⟩

theorem proposicion310_dim2_de_dimensional
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
  have hD : 1 ≤ Real.sqrt 2 := by simp
  have hf (ω : Ω) (n : ℕ) :
      D.problemaRaizDimensional μr μb (hmr n) (hmb n) (Real.sqrt 2) 2 1 dr.C db.C dr.c db.c
        lr lb α (zero_lt_one.trans_le hD) dr.C_pos dr.c_pos db.c_pos hlr hlb true
        (fun i => sr.Z i ω) (fun i => sb.Z i ω) = Pn ω n := by
    rw [problemaRaizDimensional_igual_dim2]
    rfl
  have hrel' : ∀ᶠ n in atTop, (mr n : ℝ) ≤ Ksize * (mb n : ℝ) ^ ((2 : ℝ) / 1) := by
    simpa only [div_one, Real.rpow_two] using hrel
  have h := proposicion310_dimensional P μr μb U Γ (Real.sqrt 2) 2 1 ε₀
    dr.toDimensional db.toDimensional sr sb D hD (by norm_num) (by norm_num) hε₀
    mr mb hmr hmb hgr hgb lr lb α Sf Sg Ksize hlr hlb hα hKsize hrel'
    Hm hm v _hMeasHm _hMeasV ε δ hε hδ Rstar K
  dsimp only [DatosMasa38.toDimensional] at h
  simp only [hf, factorCoberturaDimensional_dim2, radioRaizDimensional] at h
  exact h hHolder hvar htol

theorem proposicion310_dimension_ge_dos
    {Ω H X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    [PseudoMetricSpace X] [PseudoMetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] (U : Set X) (Γ : Set Y) (d : ℕ) (hd : 2 ≤ d) (ε₀ : ℝ)
    (dr : DatosMasaDimensional μr U (Real.sqrt d) (d : ℝ) ε₀) (db : DatosMasaDimensional μb Γ (Real.sqrt d) ((d : ℝ) - 1) ε₀)
    (Zr : Muestreo38 P μr) (Zb : Muestreo38 P μb) (op : Operadores38 H X Y)
    (hε₀ : 0 < ε₀)
    (mr mb : ℕ → ℕ) (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (hgr : ∀ᶠ n in atTop, n ≤ mr n) (hgb : ∀ᶠ n in atTop, n ≤ mb n)
    (lr lb α Sf Sg Ksize : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α) (hKsize : 0 < Ksize)
    (hrel : ∀ᶠ n in atTop, (mr n : ℝ) ≤ Ksize * (mb n : ℝ) ^ ((d : ℝ) / ((d : ℝ) - 1)))
    (Hm : ℕ → Set H) (h v : ∀ n, Ω → Hm n)
    (_hMeas : ∀ n, Measurable (fun ω => (h n ω : H)))
    (_vMeas : ∀ n, Measurable (fun ω => (v n ω : H)))
    (ε δ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hδ : ∀ n, 0 ≤ δ n)
    (Rstar : Ω → ℝ) (K : ℝ) :
    let rr := fun n => radioRaizDimensional (Real.sqrt d) dr.c (d : ℝ) (mr n)
    let rb := fun n => radioRaizDimensional (Real.sqrt d) db.c ((d : ℝ) - 1) (mb n)
    let F := fun n => factorCoberturaDimensional (mr n) (mb n) dr.C db.C (rr n) (rb n) (d : ℝ) ((d : ℝ) - 1)
    let a := fun n => pesoRegularizacionIgual lr lb (rr n) (rb n) α (F n)
    let Pn := fun ω n => op.problemaRaizDimensional μr μb (hmr n) (hmb n) (Real.sqrt d) (d : ℝ) ((d : ℝ) - 1) dr.C db.C
      dr.c db.c lr lb α (Real.sqrt_pos.2 (Nat.cast_pos.mpr (by omega))) dr.C_pos dr.c_pos db.c_pos hlr hlb true
      (fun i => Zr.Z i ω) (fun i => Zb.Z i ω)
    (∀ n, op.CotasHolder34 (Hm n) U Γ α Sf Sg) →
    (∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (Pn ω n).perdidaEmpirica (v n ω : H) ≤ ε n ∧
      (Pn ω n).regularidadTotal (v n ω : H) ≤ Rstar ω ∧
      (Pn ω n).EsMinimizadorAproximado (Hm n) (h n ω : H) (δ n)) →
    (∀ᶠ n in atTop, ε n + δ n ≤ K * a n) →
    ∀ᵐ ω ∂P,
      let er := fun n x => op.L (h n ω : H) x - op.f x
      let eb := fun n y => op.B (h n ω : H) y - op.g y
      let loss := fun n => (Pn ω n).perdidaPoblacional (h n ω : H)
      (∀ᶠ n in atTop, (Pn ω n).regularidadTotal (h n ω : H) ≤ Rstar ω + K ∧
        op.seminormaL (h n ω : H) ≤ Real.sqrt (Rstar ω + K) ∧
        op.seminormaB (h n ω : H) ≤ Real.sqrt (Rstar ω + K) ∧
        loss n ≤ F n * (a n * (Rstar ω + K)) +
          3 * lr * rr n ^ (2 * α) * Sf ^ 2 + 3 * lb * rb n ^ (2 * α) * Sg ^ 2) ∧
      (loss =O[atTop] (fun n => (mr n : ℝ) ^ (-(α / (d : ℝ))))) ∧
      (Tendsto (fun n => supResiduo U (er n)) atTop (𝓝 0) ∧
       Tendsto (fun n => supResiduo Γ (eb n)) atTop (𝓝 0)) ∧
      (((fun n => supResiduo U (er n)) =O[atTop]
         (fun n => (mr n : ℝ) ^ (-(α ^ 2 / ((d : ℝ) * (2 * α + (d : ℝ))))))) ∧
       ((fun n => supResiduo Γ (eb n)) =O[atTop]
         (fun n => (mr n : ℝ) ^ (-(α ^ 2 / ((d : ℝ) * (2 * α + ((d : ℝ) - 1)))))))) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : 1 ≤ Real.sqrt (d : ℝ) := by
    have h : (1 : ℝ) ≤ d := by linarith
    simpa using Real.sqrt_le_sqrt h
  exact proposicion310_dimensional P μr μb U Γ (Real.sqrt d) d ((d : ℝ) - 1) ε₀ dr db
    Zr Zb op hD (by linarith) (by linarith) hε₀ mr mb hmr hmb hgr hgb lr lb α Sf Sg Ksize
    hlr hlb hα hKsize hrel Hm h v _hMeas _vMeas ε δ hε hδ Rstar K

section Corolario312

variable {H F G X Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [PseudoMetricSpace X] [PseudoMetricSpace Y] {U : Set X} {Γ : Set Y} {α : ℝ}

/-- C3.12 suministra las premisas de aproximación fuerte para los mismos
prefijos y pesos que usa la P3.10 dimensional. -/
theorem corolario312_premisas310_dimensional
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure Ω) (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] (D sr sb ε₀ : ℝ)
    (dr : DatosMasaDimensional μr U D sr ε₀) (db : DatosMasaDimensional μb Γ D sb ε₀)
    (hD : 1 ≤ D) (hsr : 0 < sr) (hsb : 0 < sb)
    (Zr : Muestreo38 P μr) (Zb : Muestreo38 P μb)
    (Er : RealizacionHolder312 F X U α) (Eb : RealizacionHolder312 G Y Γ α)
    (L : H →L[ℝ] F) (B : H →L[ℝ] G) (u : H) (f : X → ℝ) (g : Y → ℝ)
    (hf : EqOn (Er.eval (L u)) f U) (hg : EqOn (Eb.eval (B u)) g Γ)
    (lr lb : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (mr mb : ℕ → ℕ) (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (hTr : Tendsto mr atTop atTop) (hTb : Tendsto mb atTop atTop)
    (Hm : ℕ → Set H) (h : ∀ n, Ω → Hm n) (v : ∀ n, Hm n)
    (A : ℝ) (hA : 0 ≤ A) (δ : ℕ → ℝ) (Kδ : ℝ) :
    let op := operadores312 Er Eb L B f g
    let rr := fun n => radioRaizDimensional D dr.c sr (mr n)
    let rb := fun n => radioRaizDimensional D db.c sb (mb n)
    let Fm := fun n => factorCoberturaDimensional (mr n) (mb n) dr.C db.C (rr n) (rb n) sr sb
    let a := fun n => pesoRegularizacionIgual lr lb (rr n) (rb n) α (Fm n)
    let Pn := fun ω n => op.problemaRaizDimensional μr μb (hmr n) (hmb n) D sr sb dr.C db.C
      dr.c db.c lr lb α (zero_lt_one.trans_le hD) dr.C_pos dr.c_pos db.c_pos hlr hlb true
      (fun i => Zr.Z i ω) (fun i => Zb.Z i ω)
    (∀ n, ‖(v n : H) - u‖ ≤ A * Real.sqrt (a n)) →
    (∀ᵐ ω ∂P, ∀ᶠ n in atTop, (Pn ω n).EsMinimizadorAproximado (Hm n) (h n ω : H) (δ n)) →
    (∀ᶠ n in atTop, δ n ≤ Kδ * a n) →
    ∃ K R, 0 ≤ K ∧ 0 ≤ R ∧
      (∀ n, op.CotasHolder34 (Hm n) U Γ α ‖L u‖ ‖B u‖) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        (Pn ω n).perdidaEmpirica (v n : H) ≤ K * a n ∧
        (Pn ω n).regularidadTotal (v n : H) ≤ R ∧
        (Pn ω n).EsMinimizadorAproximado (Hm n) (h n ω : H) (δ n)) ∧
      (∀ᶠ n in atTop, K * a n + δ n ≤ (K + Kδ) * a n) := by
  intro op rr rb Fm a Pn hv hmin hδ
  have ha := pesoRaizDimensional_tendsto mr mb hmr hmb hTr hTb D dr.C db.C dr.c db.c sr sb lr lb α
    (zero_lt_one.trans_le hD) dr.C_pos dr.c_pos db.c_pos hsr hsb hlr hα
  have ha₀ (n : ℕ) : 0 ≤ a n := by
    have hr := radioRaizDimensional_pos D dr.c sr (mr n) (zero_lt_one.trans_le hD) dr.c_pos (hmr n)
    have hF := factorCoberturaDimensional_pos (mr n) (mb n) dr.C db.C (rr n) (rb n) sr sb
      (hmr n) dr.C_pos hr
    exact (pesoCobertura_nonneg _ _ _ _ hlr.le hr.le hF.le).trans (le_max_left _ _)
  obtain ⟨K, R, hK, hR, hb⟩ := corolario312 Er Eb L B u f g hf hg lr lb hlr.le hlb.le
    a ha₀ ha (fun n => v n) A hA hv
  refine ⟨K, R, hK, hR, ?_, ?_, hδ.mono fun n hn => ?_⟩
  · intro n
    refine ⟨norm_nonneg _, norm_nonneg _, fun w _ => ?_, ?_, ?_⟩
    · exact ⟨(Er.seminorma_le (L w)).1, (Eb.seminorma_le (B w)).1,
        seminormaInterior_cota U α _ ⟨_, Er.holder (L w)⟩ hα,
        seminormaInterior_cota Γ α _ ⟨_, Eb.holder (B w)⟩ hα⟩
    · intro x hx y hy
      change |f x - f y| ≤ ‖L u‖ * dist x y ^ α
      rw [← hf hx, ← hf hy]
      exact (Er.holder (L u)).2 x hx y hy
    · intro x hx y hy
      change |g x - g y| ≤ ‖B u‖ * dist x y ^ α
      rw [← hg hx, ← hg hy]
      exact (Eb.holder (B u)).2 x hx y hy
  · have hr := muestras_en_soporte_ae P μr Zr.Z U dr.concentrada Zr.medible Zr.ley
    have hb' := muestras_en_soporte_ae P μb Zb.Z Γ db.concentrada Zb.medible Zb.ley
    filter_upwards [hmin, hr, hb'] with ω hω hsr hsb
    filter_upwards [hω] with n hn
    obtain ⟨hE, hR⟩ := hb n (hmr n) (hmb n) (Pn ω n).xr (Pn ω n).xb
      (fun i => hsr i) (fun i => hsb i)
    exact ⟨hE, hR, hn⟩
  · rw [add_mul]
    exact add_le_add_right hn _

end Corolario312

#check corolario312_premisas310_dimensional
#print axioms corolario312_premisas310_dimensional
#print axioms pesoRaizDimensional_tendsto
#check proposicion310_dimension_ge_dos
#print axioms proposicion310_dimension_ge_dos
#check proposicion310_dim2_de_dimensional
#print axioms proposicion310_dim2_de_dimensional
#check proposicion310_dimensional
#print axioms cotas310_dimensional_bajo_cobertura
#print axioms proposicion310_dimensional

end TesisPINN
