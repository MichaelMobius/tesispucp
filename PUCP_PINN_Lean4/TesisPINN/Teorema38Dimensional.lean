import TesisPINN.Teorema34Dimensional
import TesisPINN.Lema39Global
import TesisPINN.Teorema38Evento

/-! Teorema 3.8 para dos exponentes positivos de masa. -/

noncomputable section

namespace TesisPINN

open Set MeasureTheory Filter Asymptotics
open scoped Topology

theorem radioRaizDimensional_eventual (D c s ε₀ : ℝ) (m : ℕ → ℕ)
    (hD : 0 < D) (hc : 0 < c) (hs : 0 < s) (hε₀ : 0 < ε₀)
    (hm : ∀ n, 0 < m n) (hTop : Tendsto m atTop atTop) :
    ∀ᶠ n in atTop, radioRaizDimensional D c s (m n) ≤ ε₀ := by
  have hr : Tendsto (fun n => (m n : ℝ) ^ (-(1 / (2 * s)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (show 0 < 1 / (2 * s) by positivity)).comp
      (tendsto_natCast_atTop_atTop.comp hTop)
  have hlim : Tendsto (fun n => radioRaizDimensional D c s (m n)) atTop (𝓝 0) := by
    simp_rw [radioRaizDimensional, escalaAuxiliarRaiz_eq_potencias _ _ _ hc hs (hm _), ← mul_assoc]
    simpa only [mul_zero] using hr.const_mul (D * c ^ (-(1 / s)))
  exact (hlim.eventually (Iio_mem_nhds hε₀)).mono fun _ hn => le_of_lt hn

theorem cobertura_raiz_dimensional_ae
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [PseudoMetricSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure X) [IsProbabilityMeasure μ]
    (Z : Muestreo38 P μ) (U : Set X) (D s ε₀ : ℝ)
    (dm : DatosMasaDimensional μ U D s ε₀) (hD : 1 ≤ D) (hs : 0 < s) (hε₀ : 0 < ε₀)
    (m : ℕ → ℕ) (hm : ∀ n, 0 < m n) (hg : ∀ᶠ n in atTop, n ≤ m n) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      MuestrasCubren U (fun i : Fin (m n) => Z.Z i ω) (radioRaizDimensional D dm.c s (m n)) := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hc := dm.c_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (radioRaizDimensional_eventual D dm.c s ε₀ m hDp hc hs hε₀ hm
      (tendsto_atTop_mono' atTop hg tendsto_id))
  let M := fun n => m (n + N)
  have hη (n : ℕ) : 0 < escalaAuxiliarRaiz dm.c s (M n) := by
    have hpos : (0 : ℝ) < M n := Nat.cast_pos.mpr (hm (n + N))
    unfold escalaAuxiliarRaiz
    positivity
  choose K cells hcell using fun n => dm.particiones _ (hη n)
    (escala_le_de_radio_dimensional D _ ε₀ hD (hη n) (hN (n + N) (by omega)))
  have hg' : ∀ᶠ n in atTop, n ≤ M n :=
    ((tendsto_add_atTop_nat N).eventually hg).mono fun n hn => (Nat.le_add_right n N).trans hn
  have hp (n : ℕ) (i : Fin (K n)) : 1 / Real.sqrt (M n : ℝ) ≤ μ.real (cells n i) :=
    (escalaAuxiliarRaiz_masa dm.c s (M n) hc hs (hm (n + N))).symm.trans_le ((hcell n).2.2.2.2.1 i)
  have hae := cobertura_eventual_escala_raiz P μ Z.Z K M cells (fun _ => U)
    (fun n => radioRaizDimensional D dm.c s (M n)) (fun n => (hcell n).1)
    (fun n => (hcell n).2.1) (fun n => (hcell n).2.2.1)
    (fun n => (hcell n).2.2.2.2.2) (fun n => hm (n + N)) hg' hp Z.medible Z.indep Z.ley
  exact hae.mono fun _ ho => eventual_en_cola N ho

/-- Paso de comparabilidad de (3.31), sin identificar los dos tamaños. -/
theorem tasa_frontera_dimensional_le (mr mb : ℕ) (sr sb K α : ℝ)
    (hmr : 0 < mr) (hmb : 0 < mb) (hr : 0 < sr) (hb : 0 < sb) (hK : 0 < K) (hα : 0 < α)
    (hrel : (mr : ℝ) ≤ K * (mb : ℝ) ^ (sr / sb)) :
    (mb : ℝ) ^ (-(α / sb)) ≤ K ^ (α / sr) * (mr : ℝ) ^ (-(α / sr)) := by
  have hm : (0 : ℝ) < mr := Nat.cast_pos.mpr hmr
  have hn : (0 : ℝ) < mb := Nat.cast_pos.mpr hmb
  have hp := Real.rpow_le_rpow hm.le hrel (div_nonneg hα.le hr.le)
  rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul hn.le,
    show sr / sb * (α / sr) = α / sb by field_simp] at hp
  rw [Real.rpow_neg hn.le, Real.rpow_neg hm.le, ← div_eq_mul_inv, ← one_div]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hn _) (Real.rpow_pos_of_pos hm _)).2
  simpa using hp

theorem producto_peso_igual_dimensional (lr lb rr rb α F : ℝ) (hF : 0 < F) :
    F * max (pesoCobertura lr rr α F) (pesoCobertura lb rb α F) =
      max (3 * lr * rr ^ (2 * α)) (3 * lb * rb ^ (2 * α)) := by
  rw [mul_max_of_nonneg _ _ hF.le, pesoCobertura, pesoCobertura,
    mul_div_cancel₀ _ hF.ne', mul_div_cancel₀ _ hF.ne']

/-- Una conclusión casi segura admite un evento medible de probabilidad uno
contenido en el conjunto donde se cumple, incluso sin medir ese conjunto. -/
theorem evento_prob_uno_de_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {p : Ω → Prop} (hp : ∀ᵐ ω ∂P, p ω) :
    ∃ A : Set Ω, MeasurableSet A ∧ P A = 1 ∧ ∀ ω ∈ A, p ω := by
  obtain ⟨N, hN, hm, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  refine ⟨Nᶜ, hm.compl, by rw [prob_compl_eq_one_sub hm, hzero, tsub_zero], ?_⟩
  intro ω hω
  by_contra! hfalse
  exact hω (hN hfalse)

private theorem cotas_minimo_igual
    {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {mr mb : ℕ}
    (P : ProblemaPINN H X Y mr mb) (Hm : Set H) (h v : H) (a R : ℝ)
    (hmin : P.EsMinimizadorGlobal Hm h) (hv : P.ComparadorExacto Hm v)
    (hreg : P.regularidadTotal v ≤ R) (ha : 0 < a)
    (hR : P.regularizadorR = a) (hB : P.regularizadorB = a) :
    P.regularidadTotal h ≤ R ∧ P.funcionalRegularizado h ≤ a * R := by
  refine ⟨(P.regularidad_minimizador_le_comparador Hm h v hmin hv a ha hR hB).trans hreg, ?_⟩
  rw [P.funcional_pesos_iguales h a hR hB]
  exact (P.comparacion_con_interpolador Hm h v hmin hv a hR hB).trans
    (mul_le_mul_of_nonneg_left hreg ha.le)

/-- Cota explícita de (3.26) una vez que el escalamiento de tamaños es válido. -/
def constante38Dimensional (D cr cb sr sb lr lb α Sf Sg R K : ℝ) : ℝ :=
  3 * (lr * (D * cr ^ (-(1 / sr))) ^ (2 * α) * (R + Sf ^ 2) +
    lb * (D * cb ^ (-(1 / sb))) ^ (2 * α) * (R + Sg ^ 2) * K ^ (α / sr))

/-- Conversión de una cota en radios a la tasa de (3.26) o (3.43). -/
theorem cota_dimensional_de_radios
    (D cr cb sr sb lr lb α Sf Sg R K L : ℝ) (mr mb : ℕ)
    (hD : 0 ≤ D) (hcr : 0 < cr) (hcb : 0 < cb)
    (hsr : 0 < sr) (hsb : 0 < sb) (hlb : 0 ≤ lb) (hα : 0 < α) (hR : 0 ≤ R)
    (hK : 0 < K) (hmr : 0 < mr) (hmb : 0 < mb)
    (hrel : (mr : ℝ) ≤ K * (mb : ℝ) ^ (sr / sb))
    (hsum : L ≤ 3 * lr * radioRaizDimensional D cr sr mr ^ (2 * α) * (R + Sf ^ 2) +
      3 * lb * radioRaizDimensional D cb sb mb ^ (2 * α) * (R + Sg ^ 2)) :
    L ≤ constante38Dimensional D cr cb sr sb lr lb α Sf Sg R K * (mr : ℝ) ^ (-(α / sr)) := by
  let rr := radioRaizDimensional D cr sr mr
  let rb := radioRaizDimensional D cb sb mb
  change L ≤ 3 * lr * rr ^ (2 * α) * (R + Sf ^ 2) + 3 * lb * rb ^ (2 * α) * (R + Sg ^ 2) at hsum
  have ht := mul_le_mul_of_nonneg_left
    (tasa_frontera_dimensional_le mr mb sr sb K α hmr hmb hsr hsb hK hα hrel)
    (show 0 ≤ 3 * lb * (D * cb ^ (-(1 / sb))) ^ (2 * α) * (R + Sg ^ 2) by positivity)
  have hpr : rr ^ (2 * α) = (D * cr ^ (-(1 / sr))) ^ (2 * α) * (mr : ℝ) ^ (-(α / sr)) := by
    rw [radioRaizDimensional_potencia _ _ _ _ _ hD hcr hsr hmr]
    congr 2
    ring
  have hpb : rb ^ (2 * α) = (D * cb ^ (-(1 / sb))) ^ (2 * α) * (mb : ℝ) ^ (-(α / sb)) := by
    rw [radioRaizDimensional_potencia _ _ _ _ _ hD hcb hsb hmb]
    congr 2
    ring
  rw [hpr, hpb] at hsum
  unfold constante38Dimensional
  linarith only [hsum, ht]

theorem cota38_dimensional_bajo_cobertura
    {H X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (μr : Measure X) [IsProbabilityMeasure μr] (μb : Measure Y) [IsProbabilityMeasure μb]
    (U : Set X) (Γ : Set Y) (D sr sb ε₀ : ℝ)
    (dr : DatosMasaDimensional μr U D sr ε₀) (db : DatosMasaDimensional μb Γ D sb ε₀)
    (op : Operadores38 H X Y) (Hm : Set H) (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (lr lb α Sf Sg R K : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (hD : 0 < D) (hsr : 0 < sr) (hsb : 0 < sb) (hR : 0 ≤ R) (hK : 0 < K)
    (hrel : (mr : ℝ) ≤ K * (mb : ℝ) ^ (sr / sb))
    (hradR : radioRaizDimensional D dr.c sr mr ≤ ε₀)
    (hradB : radioRaizDimensional D db.c sb mb ≤ ε₀)
    (hrg : op.CotasHolder34 Hm U Γ α Sf Sg)
    (xr : Fin mr → X) (xb : Fin mb → Y) (h v : H) :
    let P := op.problemaRaizDimensional μr μb hmr hmb D sr sb dr.C db.C dr.c db.c lr lb α
      hD dr.C_pos dr.c_pos db.c_pos hlr hlb true xr xb
    CoberturaDimensional P U Γ (radioRaizDimensional D dr.c sr mr) (radioRaizDimensional D db.c sb mb) →
    P.EsMinimizadorGlobal Hm h → P.ComparadorExacto Hm v → P.regularidadTotal v ≤ R →
    P.perdidaPoblacional h ≤ constante38Dimensional D dr.c db.c sr sb lr lb α Sf Sg R K *
      (mr : ℝ) ^ (-(α / sr)) := by
  intro P hcov hmin hv hreg
  let rr := radioRaizDimensional D dr.c sr mr
  let rb := radioRaizDimensional D db.c sb mb
  let F := factorCoberturaDimensional mr mb dr.C db.C rr rb sr sb
  have hrr : 0 < rr := radioRaizDimensional_pos _ _ _ _ hD dr.c_pos hmr
  have hrb : 0 < rb := radioRaizDimensional_pos _ _ _ _ hD db.c_pos hmb
  have hF : 0 < F := factorCoberturaDimensional_pos _ _ _ _ _ _ _ _ hmr dr.C_pos hrr
  let a := max (pesoCobertura lr rr α F) (pesoCobertura lb rb α F)
  have ha : 0 < a := (show 0 < pesoCobertura lr rr α F from by unfold pesoCobertura; positivity).trans_le
    (le_max_left _ _)
  have hJ := (cotas_minimo_igual P Hm h v a R hmin hv hreg ha rfl rfl).2
  have hcota := cota34_dimensional_bajo_cobertura μr μb U Γ D sr sb ε₀ dr db op Hm hmr hmb
    lr lb α Sf Sg rr rb hlr hlb hα hrr hrb hradR hradB true xr xb hrg hcov h hmin.1
  change P.perdidaPoblacional h ≤ F * P.funcionalRegularizado h +
    3 * lr * rr ^ (2 * α) * Sf ^ 2 + 3 * lb * rb ^ (2 * α) * Sg ^ 2 at hcota
  have hJR := mul_le_mul_of_nonneg_left hJ hF.le
  rw [← mul_assoc, producto_peso_igual_dimensional _ _ _ _ _ _ hF] at hJR
  have leSum : max (3 * lr * rr ^ (2 * α)) (3 * lb * rb ^ (2 * α)) ≤
      3 * lr * rr ^ (2 * α) + 3 * lb * rb ^ (2 * α) :=
    max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
  have hJ' := hJR.trans (mul_le_mul_of_nonneg_right leSum hR)
  have hsum : P.perdidaPoblacional h ≤
      3 * lr * rr ^ (2 * α) * (R + Sf ^ 2) + 3 * lb * rb ^ (2 * α) * (R + Sg ^ 2) := by
    linarith only [hcota, hJ']
  exact cota_dimensional_de_radios D dr.c db.c sr sb lr lb α Sf Sg R K _ mr mb hD.le
    dr.c_pos db.c_pos hsr hsb hlb.le hα hR hK hmr hmb hrel hsum

/-- (3.26) en un evento medible común de muestra finita. -/
theorem teorema38_evento_dimensional
    {Ω H X Y : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] (U : Set X) (Γ : Set Y) (D sr sb ε₀ : ℝ)
    (dr : DatosMasaDimensional μr U D sr ε₀) (db : DatosMasaDimensional μb Γ D sb ε₀)
    (Zr : Muestreo38 P μr) (Zb : Muestreo38 P μb) (op : Operadores38 H X Y) (Hm : Set H)
    (hD : 1 ≤ D) (hsr : 0 < sr) (hsb : 0 < sb)
    (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (lr lb α Sf Sg K : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α) (hK : 0 < K)
    (hrel : (mr : ℝ) ≤ K * (mb : ℝ) ^ (sr / sb))
    (hradR : radioRaizDimensional D dr.c sr mr ≤ ε₀)
    (hradB : radioRaizDimensional D db.c sb mb ≤ ε₀)
    (hHolder : op.CotasHolder34 Hm U Γ α Sf Sg) :
    let Pω := fun ω => op.problemaRaizDimensional μr μb hmr hmb D sr sb dr.C db.C dr.c db.c lr lb α
      (zero_lt_one.trans_le hD) dr.C_pos dr.c_pos db.c_pos hlr hlb true
      (fun i => Zr.Z i ω) (fun i => Zb.Z i ω)
    ∃ A : Set Ω, MeasurableSet A ∧ 1 - falloRaiz34 mr - falloRaiz34 mb ≤ P.real A ∧
      ∀ ω ∈ A, ∀ (h v : H) (R : ℝ), 0 ≤ R →
        (Pω ω).EsMinimizadorGlobal Hm h → (Pω ω).ComparadorExacto Hm v →
        (Pω ω).regularidadTotal v ≤ R →
        (Pω ω).perdidaPoblacional h ≤ constante38Dimensional D dr.c db.c sr sb lr lb α Sf Sg R K *
          (mr : ℝ) ^ (-(α / sr)) := by
  intro Pω
  obtain ⟨A, hA, hp, hc⟩ := evento_cobertura34_dimensional P μr μb U Γ D sr sb ε₀ dr db Zr Zb
    hD hsr hsb mr mb hmr hmb hradR hradB
  refine ⟨A, hA, hp, fun ω hω h v R hR hmin hv hreg => ?_⟩
  exact cota38_dimensional_bajo_cobertura μr μb U Γ D sr sb ε₀ dr db op Hm mr mb hmr hmb
    lr lb α Sf Sg R K hlr hlb hα (zero_lt_one.trans_le hD) hsr hsb hR hK
    hrel hradR hradB hHolder _ _ h v (hc ω hω) hmin hv hreg

theorem energia_isBigO_de_perdida {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (r : ℕ → X → ℝ) (w C : ℝ) (hw : 0 < w)
    (loss b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hLos : ∀ᶠ n in atTop, loss n ≤ C * b n)
    (hE : ∀ n, w * (∫ x, r n x ^ 2 ∂μ) ≤ loss n) :
    (fun n => ∫ x, r n x ^ 2 ∂μ) =O[atTop] b := by
  apply isBigO_de_cota_eventual _ _ (C / w)
  filter_upwards [hLos] with n hn
  refine ⟨integral_nonneg (fun _ => sq_nonneg _), hb n, ?_⟩
  calc
    _ ≤ C * b n / w := (le_div_iff₀ hw).2 (by rw [mul_comm]; exact (hE n).trans hn)
    _ = _ := by ring

/-- (3.26)–(3.28) para dos exponentes positivos de masa. Tomar el factor
geométrico √d y exponentes d y d-1 da la instancia normativa. -/
theorem teorema38_dimensional
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
    (lr lb α Sf Sg K : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α) (hK : 0 < K)
    (hrel : ∀ᶠ n in atTop, (mr n : ℝ) ≤ K * (mb n : ℝ) ^ (sr / sb))
    (Hm : ℕ → Set H) (h v : ∀ n, Ω → Hm n)
    (_hh : ∀ n, Measurable (fun ω => (h n ω : H)))
    (_hv : ∀ n, Measurable (fun ω => (v n ω : H)))
    (hHolder : ∀ n, op.CotasHolder34 (Hm n) U Γ α Sf Sg) :
    let Pn := fun ω n => op.problemaRaizDimensional μr μb (hmr n) (hmb n) D sr sb dr.C db.C
      dr.c db.c lr lb α (zero_lt_one.trans_le hD) dr.C_pos dr.c_pos db.c_pos hlr hlb true
      (fun i => Zr.Z i ω) (fun i => Zb.Z i ω)
    (∀ᵐ ω ∂P, ∃ R : ℝ, 0 ≤ R ∧ ∀ n,
      (Pn ω n).EsMinimizadorGlobal (Hm n) (h n ω : H) ∧
      (Pn ω n).ComparadorExacto (Hm n) (v n ω : H) ∧
      (Pn ω n).regularidadTotal (v n ω : H) ≤ R) →
    ∀ᵐ ω ∂P,
      let er := fun n x => op.L (h n ω : H) x - op.f x
      let eb := fun n y => op.B (h n ω : H) y - op.g y
      ((fun n => (Pn ω n).perdidaPoblacional (h n ω : H)) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α / sr)))) ∧
      (Tendsto (fun n => supResiduo U (er n)) atTop (𝓝 0) ∧
       Tendsto (fun n => supResiduo Γ (eb n)) atTop (𝓝 0)) ∧
      (((fun n => supResiduo U (er n)) =O[atTop]
         (fun n => (mr n : ℝ) ^ (-(α ^ 2 / (sr * (2 * α + sr)))))) ∧
       ((fun n => supResiduo Γ (eb n)) =O[atTop]
         (fun n => (mr n : ℝ) ^ (-(α ^ 2 / (sr * (2 * α + sb))))))) := by
  intro Pn hvar
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hmrTop := tendsto_atTop_mono' atTop hgr tendsto_id
  have hmbTop := tendsto_atTop_mono' atTop hgb tendsto_id
  have hsmallR := radioRaizDimensional_eventual D dr.c sr ε₀ mr hDp dr.c_pos hsr hε₀ hmr hmrTop
  have hsmallB := radioRaizDimensional_eventual D db.c sb ε₀ mb hDp db.c_pos hsb hε₀ hmb hmbTop
  have hcovR := cobertura_raiz_dimensional_ae P μr Zr U D sr ε₀ dr hD hsr hε₀ mr hmr hgr
  have hcovB := cobertura_raiz_dimensional_ae P μb Zb Γ D sb ε₀ db hD hsb hε₀ mb hmb hgb
  have hsuR := muestras_en_soporte_ae P μr Zr.Z U dr.concentrada Zr.medible Zr.ley
  have hsuB := muestras_en_soporte_ae P μb Zb.Z Γ db.concentrada Zb.medible Zb.ley
  filter_upwards [hvar, hcovR, hcovB, hsuR, hsuB] with ω hvarω hcR hcB hsrω hsbω
  obtain ⟨R, hR, hvarω⟩ := hvarω
  let er := fun n x => op.L (h n ω : H) x - op.f x
  let eb := fun n y => op.B (h n ω : H) y - op.g y
  let loss := fun n => (Pn ω n).perdidaPoblacional (h n ω : H)
  let b := fun n => (mr n : ℝ) ^ (-(α / sr))
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
  let C := constante38Dimensional D dr.c db.c sr sb lr lb α Sf Sg R K
  have hLos : ∀ᶠ n in atTop, loss n ≤ C * b n := by
    filter_upwards [hcR, hcB, hsmallR, hsmallB, hrel] with n hcr hcb hrr hrb hrel'
    obtain ⟨hmin, hcomp, hb⟩ := hvarω n
    exact cota38_dimensional_bajo_cobertura μr μb U Γ D sr sb ε₀ dr db op (Hm n)
      (mr n) (mb n) (hmr n) (hmb n) lr lb α Sf Sg R K hlr hlb hα hDp hsr hsb hR hK
      hrel' hrr hrb (hHolder n) _ _ _ _
      ⟨fun i => hsrω i, fun i => hsbω i, hcr, hcb⟩ hmin hcomp hb
  have hb (n : ℕ) : 0 ≤ b n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hOb : loss =O[atTop] b := isBigO_de_cota_eventual _ _ C
    (hLos.mono fun n hn => ⟨(Pn ω n).perdidaPoblacional_nonneg _ (hInt n), hb n, hn⟩)
  have hH (n : ℕ) :
      (∀ x ∈ U, ∀ y ∈ U, |er n x - er n y| ≤ (Real.sqrt R + Sf) * dist x y ^ α) ∧
      (∀ x ∈ Γ, ∀ y ∈ Γ, |eb n x - eb n y| ≤ (Real.sqrt R + Sg) * dist x y ^ α) := by
    let rr := radioRaizDimensional D dr.c sr (mr n)
    let rb := radioRaizDimensional D db.c sb (mb n)
    let F := factorCoberturaDimensional (mr n) (mb n) dr.C db.C rr rb sr sb
    have hrr : 0 < rr := radioRaizDimensional_pos _ _ _ _ hDp dr.c_pos (hmr n)
    have hF : 0 < F := factorCoberturaDimensional_pos _ _ _ _ _ _ _ _ (hmr n) dr.C_pos hrr
    let a := max (pesoCobertura lr rr α F) (pesoCobertura lb rb α F)
    have ha : 0 < a := (show 0 < pesoCobertura lr rr α F from by unfold pesoCobertura; positivity).trans_le
      (le_max_left _ _)
    have hreg := (cotas_minimo_igual (Pn ω n) (Hm n) _ _ a R (hvarω n).1 (hvarω n).2.1
      (hvarω n).2.2 ha rfl rfl).1
    have hc := (hHolder n).2.2.1 _ (h n ω).2
    change op.seminormaL (h n ω : H) ^ 2 + op.seminormaB (h n ω : H) ^ 2 ≤ R at hreg
    have hsR := (Real.le_sqrt hc.1 hR).2 (by linarith [sq_nonneg (op.seminormaB (h n ω : H))])
    have hsB := (Real.le_sqrt hc.2.1 hR).2 (by linarith [sq_nonneg (op.seminormaL (h n ω : H))])
    constructor
    · intro x hx y hy
      exact (holder_resta U _ _ _ _ α hc.2.2.1 (hHolder n).2.2.2.1 x hx y hy).trans
        (mul_le_mul_of_nonneg_right (add_le_add_left hsR _) (Real.rpow_nonneg dist_nonneg _))
    · intro x hx y hy
      exact (holder_resta Γ _ _ _ _ α hc.2.2.2 (hHolder n).2.2.2.2 x hx y hy).trans
        (mul_le_mul_of_nonneg_right (add_le_add_left hsB _) (Real.rpow_nonneg dist_nonneg _))
  have hEr := energia_isBigO_de_perdida μr er lr C hlr loss b hb hLos
    (fun n => le_add_of_nonneg_right (mul_nonneg hlb.le (integral_nonneg fun _ => sq_nonneg (eb n _))))
  have hEb := energia_isBigO_de_perdida μb eb lb C hlb loss b hb hLos
    (fun n => le_add_of_nonneg_left (mul_nonneg hlr.le (integral_nonneg fun _ => sq_nonneg (er n _))))
  have hSf := (hHolder 0).1
  have hSg := (hHolder 0).2.1
  have hkr := dr.c_pos
  have hkb := db.c_pos
  have hr := lema39_tasa μr U dr.medible (Real.sqrt R + Sf) α
    (dr.c * (2 * D)⁻¹ ^ sr) sr (2 * D * ε₀) (by positivity) hα (by positivity) (by positivity)
    (masa_bola_inferior_dimensional μr U D dr.c sr ε₀ hDp dr.particiones) hsr (α / sr) (by positivity)
    er mr hmrTop (Eventually.of_forall fun n => ⟨(hInt n).1, (hH n).1⟩) hEr
  have hB := lema39_tasa μb Γ db.medible (Real.sqrt R + Sg) α
    (db.c * (2 * D)⁻¹ ^ sb) sb (2 * D * ε₀) (by positivity) hα (by positivity) (by positivity)
    (masa_bola_inferior_dimensional μb Γ D db.c sb ε₀ hDp db.particiones) hsb (α / sr) (by positivity)
    eb mr hmrTop (Eventually.of_forall fun n => ⟨(hInt n).2, (hH n).2⟩) hEb
  have hexp (s : ℝ) : α * (α / sr) / (2 * α + s) = α ^ 2 / (sr * (2 * α + s)) := by
    rw [← mul_div_assoc, div_div]
    congr 1
    ring
  rw [hexp sr] at hr
  rw [hexp sb] at hB
  have hmReal : Tendsto (fun n => (mr n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmrTop
  exact ⟨hOb, ⟨hr.trans_tendsto ((tendsto_rpow_neg_atTop (by positivity)).comp hmReal),
    hB.trans_tendsto ((tendsto_rpow_neg_atTop (by positivity)).comp hmReal)⟩, hr, hB⟩

/-- En dimensión dos el problema con (3.23) es el de la familia anterior. -/
theorem problemaRaizDimensional_igual_dim2
    {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (op : Operadores38 H X Y) (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] (mr mb : ℕ)
    (hmr : 0 < mr) (hmb : 0 < mb)
    (Cr Cb cr cb lr lb α : ℝ) (hCr : 0 < Cr) (hcr : 0 < cr) (hcb : 0 < cb)
    (hlr : 0 < lr) (hlb : 0 < lb) (xr : Fin mr → X) (xb : Fin mb → Y) :
    op.problemaRaizDimensional μr μb hmr hmb (Real.sqrt 2) 2 1 Cr Cb cr cb lr lb α
      (by positivity) hCr hcr hcb hlr hlb true xr xb =
    op.problemaIgual μr μb mr mb hmr hmb Cr Cb cr cb lr lb α hCr hcr hlr hlb xr xb := by
  simp only [Operadores38.problemaRaizDimensional, Operadores38.problemaDimensional,
    Operadores38.problemaIgual, Operadores38.base, pesoRegularizacionIgual,
    radioRaizDimensional, factorCoberturaDimensional_dim2]
  rfl

theorem teorema38_dim2_de_dimensional
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
    (lr lb α Sf Sg K : ℝ) (hlr : 0 < lr) (hlb : 0 < lb)
    (hα : 0 < α) (_hαone : α ≤ 1) (hK : 0 < K)
    (hrel : ∀ᶠ n in atTop, (mr n : ℝ) ≤ K * (mb n : ℝ) ^ 2)
    (Hm : ℕ → Set H) (hm g : ∀ n, Ω → Hm n)
    (hMeasHm : ∀ n, Measurable (fun ω => (hm n ω : H)))
    (hMeasG : ∀ n, Measurable (fun ω => (g n ω : H))) :
    let base := fun n => D.base μr μb (mr n) (mb n) (hmr n) (hmb n)
      dr.C db.C dr.c db.c lr lb α dr.C_pos dr.c_pos hlr hlb
    let Pn := problemaMuestral mr mb base sr.Z sb.Z
    (∀ n, CotasHolder (base n) (Hm n) U Γ α Sf Sg) →
    (∀ᵐ ω ∂P, ∃ R : ℝ, 0 ≤ R ∧ ∀ n,
      (Pn ω n).EsMinimizadorGlobal (Hm n) (hm n ω : H) ∧
      (Pn ω n).ComparadorExacto (Hm n) (g n ω : H) ∧
      (Pn ω n).regularidadTotal (g n ω : H) ≤ R) →
    ∀ᵐ ω ∂P,
      let er := fun n x => D.L (hm n ω : H) x - D.f x
      let eb := fun n y => D.B (hm n ω : H) y - D.g y
      ((fun n => (Pn ω n).perdidaPoblacional (hm n ω : H)) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α / 2)))) ∧
      (Tendsto (fun n => supResiduo U (er n)) atTop (nhds 0) ∧
       Tendsto (fun n => supResiduo Γ (eb n)) atTop (nhds 0)) ∧
      (((fun n => supResiduo U (er n)) =O[atTop]
         (fun n => (mr n : ℝ) ^ (-(α ^ 2 / (2 * (2 * α + 2)))))) ∧
       ((fun n => supResiduo Γ (eb n)) =O[atTop]
         (fun n => (mr n : ℝ) ^ (-(α ^ 2 / (2 * (2 * α + 1))))))) := by
  intro base Pn hHolder hvar
  have hD : 1 ≤ Real.sqrt 2 := by simp
  have hf (ω : Ω) (n : ℕ) :
      D.problemaRaizDimensional μr μb (hmr n) (hmb n) (Real.sqrt 2) 2 1 dr.C db.C dr.c db.c
        lr lb α (zero_lt_one.trans_le hD) dr.C_pos dr.c_pos db.c_pos hlr hlb true
        (fun i => sr.Z i ω) (fun i => sb.Z i ω) = Pn ω n := by
    rw [problemaRaizDimensional_igual_dim2]
    rfl
  have hrel' : ∀ᶠ n in atTop, (mr n : ℝ) ≤ K * (mb n : ℝ) ^ ((2 : ℝ) / 1) := by
    simpa only [div_one, Real.rpow_two] using hrel
  have h := teorema38_dimensional P μr μb U Γ (Real.sqrt 2) 2 1 ε₀ dr.toDimensional db.toDimensional
    sr sb D hD (by norm_num) (by norm_num) hε₀ mr mb hmr hmb hgr hgb lr lb α Sf Sg K
    hlr hlb hα hK hrel' Hm hm g hMeasHm hMeasG (fun n => hHolder n)
  dsimp only [DatosMasa38.toDimensional] at h
  simp only [hf] at h
  exact h hvar

theorem teorema38_dimension_ge_dos
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
    (lr lb α Sf Sg K : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α) (hK : 0 < K)
    (hrel : ∀ᶠ n in atTop, (mr n : ℝ) ≤ K * (mb n : ℝ) ^ ((d : ℝ) / ((d : ℝ) - 1)))
    (Hm : ℕ → Set H) (h v : ∀ n, Ω → Hm n)
    (_hh : ∀ n, Measurable (fun ω => (h n ω : H)))
    (_hv : ∀ n, Measurable (fun ω => (v n ω : H)))
    (hHolder : ∀ n, op.CotasHolder34 (Hm n) U Γ α Sf Sg) :
    let Pn := fun ω n => op.problemaRaizDimensional μr μb (hmr n) (hmb n) (Real.sqrt d) (d : ℝ) ((d : ℝ) - 1) dr.C db.C
      dr.c db.c lr lb α (Real.sqrt_pos.2 (Nat.cast_pos.mpr (by omega))) dr.C_pos dr.c_pos db.c_pos hlr hlb true
      (fun i => Zr.Z i ω) (fun i => Zb.Z i ω)
    (∀ᵐ ω ∂P, ∃ R : ℝ, 0 ≤ R ∧ ∀ n,
      (Pn ω n).EsMinimizadorGlobal (Hm n) (h n ω : H) ∧
      (Pn ω n).ComparadorExacto (Hm n) (v n ω : H) ∧
      (Pn ω n).regularidadTotal (v n ω : H) ≤ R) →
    ∀ᵐ ω ∂P,
      let er := fun n x => op.L (h n ω : H) x - op.f x
      let eb := fun n y => op.B (h n ω : H) y - op.g y
      ((fun n => (Pn ω n).perdidaPoblacional (h n ω : H)) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α / (d : ℝ))))) ∧
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
  exact teorema38_dimensional P μr μb U Γ (Real.sqrt d) d ((d : ℝ) - 1) ε₀ dr db
    Zr Zb op hD (by linarith) (by linarith) hε₀ mr mb hmr hmb hgr hgb lr lb α Sf Sg K
    hlr hlb hα hK hrel Hm h v _hh _hv hHolder

#check teorema38_dimension_ge_dos
#print axioms teorema38_dimension_ge_dos
#check teorema38_dim2_de_dimensional
#print axioms teorema38_dim2_de_dimensional
#check teorema38_evento_dimensional
#check teorema38_dimensional
#print axioms teorema38_evento_dimensional
#print axioms teorema38_dimensional
#print axioms evento_prob_uno_de_ae
#print axioms problemaRaizDimensional_igual_dim2

end TesisPINN
