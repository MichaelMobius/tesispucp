import TesisPINN.ConvergenciaUniforme
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Integración de (3.26)–(3.28) en dimensión dos. -/

noncomputable section

namespace TesisPINN

open MeasureTheory ProbabilityTheory Filter Asymptotics

/-- Datos de masa de la Hipótesis 3.2 en un soporte. -/
structure DatosMasa38 {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (U : Set X) (s ε₀ : ℝ) where
  c : ℝ
  C : ℝ
  c_pos : 0 < c
  C_pos : 0 < C
  medible : MeasurableSet U
  acotado : Bornology.IsBounded U
  concentrada : μ Uᶜ = 0
  superior : MasaBolaSuperior μ U ε₀ C s
  particiones : ParticionesMinimas μ U c s ε₀

/-- Una sucesión i.i.d. sobre el espacio común. -/
structure Muestreo38 {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Measure X) where
  Z : ℕ → Ω → X
  medible : ∀ i, Measurable (Z i)
  indep : iIndepFun Z P
  ley : ∀ i, Measure.map (Z i) P = μ

/-- Operadores, datos y seminormas fijos entre tamaños muestrales. -/
structure Operadores38 (H X Y : Type*) where
  L : H → X → ℝ
  f : X → ℝ
  B : H → Y → ℝ
  g : Y → ℝ
  seminormaL : H → ℝ
  seminormaB : H → ℝ

theorem radio38_pos (c s : ℝ) (m : ℕ) (hc : 0 < c) (hm : 0 < m) :
    0 < Real.sqrt 2 * escalaAuxiliarRaiz c s m := by
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  unfold escalaAuxiliarRaiz
  positivity

theorem peso38_pos (mr mb : ℕ) (Cr Cb r b lr lb α : ℝ)
    (hCr : 0 < Cr) (hmr : 0 < mr) (hr : 0 < r) (hlr : 0 < lr) :
    0 < pesoRegularizacionIgual lr lb r b α (factorCoberturaCuadrado mr mb Cr Cb r b) := by
  have hr' : 0 < Cr * (mr : ℝ) * r ^ 2 := by positivity
  have hCm : 0 < factorCoberturaCuadrado mr mb Cr Cb r b :=
    mul_pos (by norm_num) (hr'.trans_le (le_max_left _ _))
  have hp : 0 < pesoCobertura lr r α (factorCoberturaCuadrado mr mb Cr Cb r b) := by
    unfold pesoCobertura
    positivity
  exact hp.trans_le (pesoInterior_le_igual lr lb r b α _)

/-- Base determinista de `problemaMuestral`. Sus campos de puntos se
reemplazan por los prefijos realizados en esa única definición. -/
def Operadores38.base {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Operadores38 H X Y)
    (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (Cr Cb cr cb lr lb α : ℝ) (hCr : 0 < Cr) (hcr : 0 < cr)
    (hlr : 0 < lr) (hlb : 0 < lb) : ProblemaPINN H X Y mr mb :=
  let r := Real.sqrt 2 * escalaAuxiliarRaiz cr 2 mr
  let b := Real.sqrt 2 * escalaAuxiliarRaiz cb 1 mb
  let a := pesoRegularizacionIgual lr lb r b α (factorCoberturaCuadrado mr mb Cr Cb r b)
  have ha : 0 < a := peso38_pos mr mb Cr Cb r b lr lb α hCr hmr
    (radio38_pos cr 2 mr hcr hmr) hlr
  { L := D.L
    f := D.f
    B := D.B
    g := D.g
    xr := fun _ => Classical.choice (nonempty_of_isProbabilityMeasure μr)
    xb := fun _ => Classical.choice (nonempty_of_isProbabilityMeasure μb)
    μr := μr
    μb := μb
    μr_prob := measure_univ
    μb_prob := measure_univ
    seminormaL := D.seminormaL
    seminormaB := D.seminormaB
    lambdaR := lr
    lambdaB := lb
    regularizadorR := a
    regularizadorB := a
    mr_pos := hmr
    mb_pos := hmb
    lambdaR_pos := hlr
    lambdaB_pos := hlb
    regularizadorR_nonneg := ha.le
    regularizadorB_nonneg := ha.le }

theorem continuo_de_cota_holder {X : Type*} [PseudoMetricSpace X]
    (U : Set X) (f : X → ℝ) (A α : ℝ) (hα : 0 < α)
    (h : ∀ x ∈ U, ∀ y ∈ U, |f x - f y| ≤ A * dist x y ^ α) :
    ContinuousOn f U := by
  apply Metric.continuousOn_iff.mpr
  intro x hx ε hε
  have hc : Continuous (fun y : X => A * dist y x ^ α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      (continuous_id.dist continuous_const))
  have hev : ∀ᶠ y in nhds x, A * dist y x ^ α < ε :=
    hc.continuousAt.tendsto.eventually (Iio_mem_nhds (by
      simpa [Real.zero_rpow hα.ne'] using hε))
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun y hy hyδ => ?_⟩
  rw [Real.dist_eq]
  exact (h y hy x hx).trans_lt (hd hyδ)

theorem eventual_en_cola {p : ℕ → Prop} (N : ℕ)
    (h : ∀ᶠ n in atTop, p (n + N)) : ∀ᶠ n in atTop, p n := by
  show {n | p n} ∈ (atTop : Filter ℕ)
  rw [← map_add_atTop_eq_nat N]
  exact h

theorem soporte_no_vacio {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (U : Set X) (hμ : μ Uᶜ = 0) :
    U.Nonempty := by
  by_contra h
  have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  simp [he] at hμ

/-- Teorema 3.8, dimensión dos. Se especializan las particiones de todas
las escalas en una cola de tamaños, sin exigir radios pequeños al inicio. -/
theorem teorema38_dim2
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
    (hα : 0 < α) (hαone : α ≤ 1) (hK : 0 < K)
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
  have hContL (ω : Ω) (n : ℕ) : ContinuousOn (D.L (hm n ω : H)) U :=
    continuo_de_cota_holder U _ _ α hα
      ((hHolder n).2.2.1 _ (hm n ω).2).2.2.1
  have hContB (ω : Ω) (n : ℕ) : ContinuousOn (D.B (hm n ω : H)) Γ :=
    continuo_de_cota_holder Γ _ _ α hα
      ((hHolder n).2.2.1 _ (hm n ω).2).2.2.2
  have hContF : ContinuousOn D.f U :=
    continuo_de_cota_holder U _ Sf α hα (hHolder 0).2.2.2.1
  have hContG : ContinuousOn D.g Γ :=
    continuo_de_cota_holder Γ _ Sg α hα (hHolder 0).2.2.2.2
  have hsmallR := radio_cobertura_eventualmente_pequeno dr.c 2 ε₀ mr
    dr.c_pos (by norm_num) hε₀ hmr hgr
  have hsmallB := radio_cobertura_eventualmente_pequeno db.c 1 ε₀ mb
    db.c_pos (by norm_num) hε₀ hmb hgb
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hsmallR.and hsmallB)
  let mR := fun n => mr (n + N)
  let mB := fun n => mb (n + N)
  have hη (η : ℝ) (hp : 0 < Real.sqrt 2 * η)
      (h : Real.sqrt 2 * η ≤ ε₀) : 0 < η ∧ η ≤ ε₀ := by
    have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
    have hs1 : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hpos : 0 < η := pos_of_mul_pos_right hp hs.le
    exact ⟨hpos, (le_mul_of_one_le_left hpos.le hs1).trans h⟩
  have hηr (n : ℕ) := hη _ (radio38_pos dr.c 2 (mR n) dr.c_pos (hmr (n + N)))
    (hN (n + N) (by omega)).1
  have hηb (n : ℕ) := hη _ (radio38_pos db.c 1 (mB n) db.c_pos (hmb (n + N)))
    (hN (n + N) (by omega)).2
  choose Kr cellsR hR using fun n =>
    dr.particiones _ (hηr n).1 (hηr n).2
  choose Kb cellsB hB using fun n =>
    db.particiones _ (hηb n).1 (hηb n).2
  have hgr' : ∀ᶠ n in atTop, n ≤ mR n :=
    ((tendsto_add_atTop_nat N).eventually hgr).mono (fun n hn => by dsimp [mR]; omega)
  have hgb' : ∀ᶠ n in atTop, n ≤ mB n :=
    ((tendsto_add_atTop_nat N).eventually hgb).mono (fun n hn => by dsimp [mB]; omega)
  have h26tail := tasa_poblacional_eventual_casi_segura P μr μb sr.Z sb.Z
    mR mB Kr Kb cellsR cellsB U Γ (fun n => base (n + N))
    (fun n => Hm (n + N)) (fun n ω => (hm (n + N) ω : H))
    (fun n ω => (g (n + N) ω : H))
    (fun n => hMeasHm (n + N)) (fun n => hMeasG (n + N))
    dr.c db.c dr.C db.C ε₀ lr lb α Sf Sg K
    dr.c_pos db.c_pos dr.C_pos db.C_pos hε₀ hlr hlb hα hαone hK
    dr.medible db.medible dr.acotado db.acotado dr.concentrada db.concentrada
    dr.superior db.superior
    (fun n => (hR n).1) (fun n => (hB n).1)
    (fun n => (hR n).2.1) (fun n => (hB n).2.1)
    (fun n => (hR n).2.2.1) (fun n => (hB n).2.2.1)
    (fun n => (hR n).2.2.2.2.2) (fun n => (hB n).2.2.2.2.2)
    (fun n => hmr (n + N)) (fun n => hmb (n + N)) hgr' hgb'
    (fun n => (hR n).2.2.2.2.1) (fun n => (hB n).2.2.2.2.1)
    sr.medible sb.medible sr.indep sb.indep sr.ley sb.ley
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ n => hHolder (n + N)) (fun ω n => hContL ω (n + N))
    (fun _ _ => hContF) (fun ω n => hContB ω (n + N)) (fun _ _ => hContG)
    (fun _ _ => rfl) (fun _ _ => rfl) ((tendsto_add_atTop_nat N).eventually hrel)
    (hvar.mono fun _ ⟨R, hR0, hh⟩ => ⟨R, hR0, Eventually.of_forall (fun n => hh (n + N))⟩)
  let loss := fun n ω => (Pn ω n).perdidaPoblacional (hm n ω : H)
  let t := fun n => (mr n : ℝ) ^ (-(α / 2))
  have h26both : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, 0 ≤ loss n ω ∧ loss n ω ≤ C * t n :=
    h26tail.mono fun _ ⟨C, hC, htail, _⟩ =>
      ⟨C, hC, eventual_en_cola N htail⟩
  have h26 : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, loss n ω ≤ C * t n :=
    h26both.mono fun _ ⟨C, hC, hb⟩ =>
    ⟨C, hC, hb.mono fun _ hn => hn.2⟩
  have hInt (ω : Ω) (n : ℕ) : (Pn ω n).PoblacionIntegrable (hm n ω : H) :=
    poblacionIntegrable_de_holder_acotado (Pn ω n) (Hm n) U Γ
      dr.acotado db.acotado (soporte_no_vacio μr U dr.concentrada)
      (soporte_no_vacio μb Γ db.concentrada) dr.concentrada db.concentrada
      α Sf Sg hα (hHolder n) _ (hm n ω).2
      (aestronglyMeasurable_residuo_sq_de_continuidad μr U dr.medible
        dr.concentrada _ _ (hContL ω n) hContF)
      (aestronglyMeasurable_residuo_sq_de_continuidad μb Γ db.medible
        db.concentrada _ _ (hContB ω n) hContG)
  have ha (ω : Ω) (n : ℕ) : 0 < (Pn ω n).regularizadorR :=
    peso38_pos (mr n) (mb n) dr.C db.C _ _ lr lb α dr.C_pos (hmr n)
      (radio38_pos dr.c 2 (mr n) dr.c_pos (hmr n)) hlr
  have hunif := convergencia_y_tasas_uniformes_ae P mr mb
    (tendsto_atTop_mono' atTop hgr tendsto_id) Pn
    (fun n ω => (hm n ω : H)) (fun n ω => (g n ω : H)) Hm
    μr μb U Γ dr.medible db.medible dr.c db.c ε₀ α Sf Sg lr lb
    dr.c_pos db.c_pos hε₀ hα (hHolder 0).1 (hHolder 0).2.1 hlr hlb
    dr.particiones db.particiones (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
    (hvar.mono fun ω ⟨R, hR0, hh⟩ => ⟨R, hR0, Eventually.of_forall fun n =>
      ⟨(hh n).1, (hh n).2.1, (hh n).2.2, hHolder n, hInt ω n, ha ω n, rfl⟩⟩)
    h26
  filter_upwards [h26both, hunif] with ω hpop hu
  obtain ⟨C, _, hC⟩ := hpop
  exact ⟨isBigO_de_cota_eventual _ _ C
    (hC.mono fun _ hn => ⟨hn.1, by positivity, hn.2⟩), hu⟩

/-- La pérdida de la familia integrada es medible en cada índice con
mensurabilidad conjunta de los operadores y mensurabilidad de los datos. -/
theorem measurable_perdida_problemaMuestral
    {H X Y Ω : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Ω]
    (mr mb : ℕ → ℕ) (base : ∀ n, ProblemaPINN H X Y (mr n) (mb n))
    (Zr : ℕ → Ω → X) (Zb : ℕ → Ω → Y) (h : ℕ → Ω → H)
    (n : ℕ) (hh : Measurable (h n))
    (hL : Measurable (fun p : H × X => (base n).L p.1 p.2))
    (hB : Measurable (fun p : H × Y => (base n).B p.1 p.2))
    (hf : Measurable (base n).f) (hg : Measurable (base n).g) :
    Measurable (fun ω => (problemaMuestral mr mb base Zr Zb ω n).perdidaPoblacional (h n ω)) :=
  measurable_perdidaPoblacional_seleccion (base n) (h n) hh hL hB hf hg

/-- Una enumeración densa reduce el supremo puntual de un residuo
continuo y acotado a un supremo numerable. -/
theorem measurable_supResiduo_de_denso
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    (U : Set X) (x : ℕ → U) (hx : DenseRange x) (f : Ω → X → ℝ)
    (hcont : ∀ ω, ContinuousOn (f ω) U)
    (hbound : ∀ ω, ∃ M : ℝ, ∀ y ∈ U, |f ω y| ≤ M)
    (hmeas : ∀ n, Measurable (fun ω => f ω (x n))) :
    Measurable (fun ω => supResiduo U (f ω)) := by
  have heq : (fun ω => supResiduo U (f ω)) = (fun ω => ⨆ n, |f ω (x n)|) := by
    funext ω
    obtain ⟨M, hM⟩ := hbound ω
    let q := ⨆ n, |f ω (x n)|
    have hbd : BddAbove (Set.range (fun n => |f ω (x n)|)) :=
      ⟨M, by rintro _ ⟨n, rfl⟩; exact hM (x n) (x n).2⟩
    have hq (n : ℕ) : |f ω (x n)| ≤ q := le_ciSup hbd n
    have hq0 : 0 ≤ q := (abs_nonneg _).trans (hq 0)
    have hc : Continuous (fun y : U => |f ω y|) :=
      (continuousOn_iff_continuous_domRestrict.1 (hcont ω)).abs
    have hall (y : U) : |f ω y| ≤ q :=
      hx.induction_on y (isClosed_le hc continuous_const) hq
    apply le_antisymm (supResiduo_le U (f ω) q hq0 (fun y hy => hall ⟨y, hy⟩)).2
    have hbu : BddAbove (insert 0 ((fun y => |f ω y|) '' U)) := by
      refine ⟨max 0 M, ?_⟩
      intro y hy
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · exact le_max_left _ _
      · obtain ⟨z, hz, rfl⟩ := hy
        exact (hM z hz).trans (le_max_right _ _)
    exact ciSup_le fun n =>
      le_csSup hbu (Set.mem_insert_of_mem _ ⟨x n, (x n).2, rfl⟩)
  rw [heq]
  exact Measurable.iSup (fun n => continuous_abs.measurable.comp (hmeas n))

/-- Una vez verificada la mensurabilidad de ambos supremos, el conjunto
exacto de convergencia uniforme es medible y tiene probabilidad uno. -/
theorem prob_uno_convergencia_sup
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r b : ℕ → Ω → ℝ)
    (hr : ∀ n, Measurable (r n)) (hb : ∀ n, Measurable (b n))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => r n ω) atTop (nhds 0) ∧
      Tendsto (fun n => b n ω) atTop (nhds 0)) :
    MeasurableSet {ω | Tendsto (fun n => r n ω) atTop (nhds 0) ∧
      Tendsto (fun n => b n ω) atTop (nhds 0)} ∧
    P {ω | Tendsto (fun n => r n ω) atTop (nhds 0) ∧
      Tendsto (fun n => b n ω) atTop (nhds 0)} = 1 := by
  have hzero : Measurable (fun _ : Ω => (0 : ℝ)) := measurable_const
  have hmR := measurableSet_tendsto_fun (l := (atTop : Filter ℕ)) hr hzero
  have hmB := measurableSet_tendsto_fun (l := (atTop : Filter ℕ)) hb hzero
  exact ⟨hmR.inter hmB, (prob_compl_eq_zero_iff (hmR.inter hmB)).mp (mem_ae_iff.mp hae)⟩

#print axioms TesisPINN.teorema38_dim2
#print axioms TesisPINN.measurable_perdida_problemaMuestral
#print axioms TesisPINN.measurable_supResiduo_de_denso
#print axioms TesisPINN.prob_uno_convergencia_sup

end TesisPINN
