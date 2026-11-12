import TesisPINN.EstabilidadEliptica
import TesisPINN.ProblemaInterior
import Mathlib.MeasureTheory.Measure.Support

/-! Transferencia de las tasas del Teorema 3.8 al error de Dirichlet. -/

noncomputable section

namespace TesisPINN

open Set Filter MeasureTheory Asymptotics
open scoped Topology

private theorem supResiduo_noNeg {X : Type*} (S : Set X) (v : X → ℝ) :
    0 ≤ supResiduo S v := by
  unfold supResiduo
  by_cases h : BddAbove (insert 0 ((fun x => |v x|) '' S))
  · exact le_csSup h (Set.mem_insert _ _)
  · rw [Real.sSup_of_not_bddAbove h]

/-- La concentración y las particiones a todas las escalas identifican
el soporte topológico cuando el dominio de muestreo es cerrado. -/
theorem soporte_de_DatosMasa38 {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {S : Set X} {s ε₀ : ℝ}
    (hS : IsClosed S) (hε₀ : 0 < ε₀) (D : DatosMasa38 μ S s ε₀) :
    μ.support = S := by
  refine subset_antisymm (μ.support_subset_of_isClosed hS (mem_ae_iff.mpr D.concentrada)) ?_
  intro x hx
  apply (Measure.mem_support_iff_forall x).2
  intro V hV
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hV
  let t := min r (2 * Real.sqrt 2 * ε₀)
  have ht : 0 < t := lt_min hr (by positivity)
  have hmass := masa_bola_inferior_potencia μ S D.c s ε₀ hε₀ D.particiones x hx t ht
    (min_le_right _ _)
  have hpos : 0 < (D.c * (2 * Real.sqrt 2)⁻¹ ^ s) * t ^ s := by
    have := D.c_pos
    positivity
  have hball : 0 < μ (Metric.ball x t ∩ S) :=
    pos_of_ne_zero fun h => by
      rw [measureReal_def, h, ENNReal.toReal_zero] at hmass
      exact (not_lt_of_ge hmass) hpos
  exact hball.trans_le (measure_mono (inter_subset_left.trans
    ((Metric.ball_subset_ball (min_le_left _ _)).trans hsub)))

/-- (3.68), con error `h-u` y residuos en sus dominios propios. -/
theorem cota318_error_dirichlet {d : ℕ} (L : OperadorEliptico d)
    {U : Set (EspacioEliptico d)} {lam B : ℝ}
    (hd : 0 < d) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hL : L.Datos U lam B)
    (u f g : EspacioEliptico d → ℝ) (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hEq : EqOn (L.aplica u) f U)
    (hDir : EqOn u g (frontier U)) :
    ∃ C > 0, ∀ h : EspacioEliptico d → ℝ, ContDiffOn ℝ 2 h U →
      ContinuousOn h (closure U) →
      (∃ M : ℝ, ∀ x ∈ U, |L.aplica h x - f x| ≤ M) →
      supResiduo (closure U) (fun x => h x - u x) ≤
        supResiduo (frontier U) (fun x => h x - g x) +
          C * supResiduo U (fun x => L.aplica h x - f x) := by
  obtain ⟨C, hC, hstab⟩ := lema317_estabilidad_uniforme L hd hU hUb hUne hL
  refine ⟨C, hC, fun h hh hhc hb => ?_⟩
  have hres : EqOn (L.aplica (fun x => h x - u x)) (fun x => L.aplica h x - f x) U := by
    intro x hx
    rw [L.aplica_resta (hh.contDiffAt (hU.mem_nhds hx))
      (hu.contDiffAt (hU.mem_nhds hx)), hEq hx]
  have hfront : EqOn (fun x => h x - u x) (fun x => h x - g x) (frontier U) :=
    fun _ hx => congrArg (fun a => _ - a) (hDir hx)
  obtain ⟨M, hM⟩ := hb
  have h := hstab _ (hh.sub hu) (hhc.sub huc)
    ⟨M, fun x hx => by rw [hres hx]; exact hM x hx⟩
  rwa [supResiduo_congr hres, supResiduo_congr hfront] at h

theorem cota318_error_dirichlet_Linfty {d : ℕ} (L : OperadorEliptico d)
    {U : Set (EspacioEliptico d)} {lam B : ℝ}
    (hd : 0 < d) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hL : L.Datos U lam B) (hLc : L.ContinuoEn U)
    (u f g : EspacioEliptico d → ℝ) (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hEq : EqOn (L.aplica u) f U)
    (hDir : EqOn u g (frontier U)) :
    ∃ C > 0, ∀ h : EspacioEliptico d → ℝ, ContDiffOn ℝ 2 h U →
      ContinuousOn h (closure U) →
      (∃ M : ℝ, ∀ x ∈ U, |L.aplica h x - f x| ≤ M) →
      supResiduo (closure U) (fun x => h x - u x) ≤
        supResiduo (frontier U) (fun x => h x - g x) +
          C * (eLpNormEssSup (fun x => L.aplica h x - f x) (volume.restrict U)).toReal := by
  obtain ⟨C, hC, hstab⟩ := cota318_error_dirichlet L hd hU hUb hUne hL u f g hu huc hEq hDir
  have hf := (L.aplica_continuo hU hLc hu).congr (fun _ hx => (hEq hx).symm)
  refine ⟨C, hC, fun h hh hhc hb => ?_⟩
  exact (supResiduo_eq_Linfty volume hU ((L.aplica_continuo hU hLc hh).sub hf) hb) ▸
    hstab h hh hhc hb

private theorem acotado_por_Holder {X : Type*} [PseudoMetricSpace X] {U : Set X}
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (v : X → ℝ) (α : ℝ) (hα : 0 < α) (hv : EsHolderInterior U α v) :
    ∃ M : ℝ, ∀ x ∈ U, |v x| ≤ M := by
  obtain ⟨x₀, hx₀⟩ := hUne
  let S := seminormaInterior U α v
  refine ⟨|v x₀| + S * (Metric.diam U) ^ α, fun x hx => ?_⟩
  have h := seminormaInterior_cota U α v hv hα x hx x₀ hx₀
  have hr := Real.rpow_le_rpow dist_nonneg (Metric.dist_le_diam_of_mem hUb hx hx₀) hα.le
  have hS := seminormaInterior_nonneg U α v hv
  calc
    |v x| = |v x - v x₀ + v x₀| := by rw [sub_add_cancel]
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by linarith only [h, mul_le_mul_of_nonneg_left hr hS]

/-- La tasa de frontera domina a la interior para las dimensiones de masa
de la tesis. Esta comparación es válida en toda dimensión `d ≥ 2`. -/
theorem exponente318_orden (d α : ℝ) (hd : 2 ≤ d) (hα : 0 < α) :
    α ^ 2 / (d * (2 * α + d)) ≤ α ^ 2 / (d * (2 * α + d - 1)) := by
  have h₀ : 0 < d * (2 * α + d - 1) := mul_pos (by linarith) (by linarith)
  apply div_le_div_of_nonneg_left (sq_nonneg α) h₀
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

private theorem transferencia318
    (mr : ℕ → ℕ) (hmr : ∀ n, 0 < mr n)
    (e r b : ℕ → ℝ) (C pr pb : ℝ) (hpr : pr ≤ pb)
    (he : ∀ n, 0 ≤ e n) (hc : ∀ n, e n ≤ b n + C * r n)
    (hr : Tendsto r atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hrO : r =O[atTop] fun n => (mr n : ℝ) ^ (-pr))
    (hbO : b =O[atTop] fun n => (mr n : ℝ) ^ (-pb)) :
    Tendsto e atTop (𝓝 0) ∧ e =O[atTop] fun n => (mr n : ℝ) ^ (-pr) := by
  have hscale : (fun n => (mr n : ℝ) ^ (-pb)) =O[atTop] fun n => (mr n : ℝ) ^ (-pr) := by
    apply IsBigO.of_bound'
    exact Eventually.of_forall fun n => by
      have hn : (1 : ℝ) ≤ mr n := by exact_mod_cast hmr n
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
        Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hpr)
  refine ⟨squeeze_zero he hc ?_, ?_⟩
  · simpa using hb.add (tendsto_const_nhds.mul hr)
  · have hmajor := (hbO.trans hscale).add (hrO.const_mul_left C)
    refine (IsBigO.of_bound' (Eventually.of_forall fun n => ?_)).trans hmajor
    rw [Real.norm_eq_abs, abs_of_nonneg (he n), Real.norm_eq_abs]
    exact (hc n).trans (le_abs_self _)

def operadores318 {H : Type*} (L : OperadorEliptico 2)
    (U : Set (EspacioEliptico 2)) (eval : H → EspacioEliptico 2 → ℝ)
    (f g : EspacioEliptico 2 → ℝ) (α : ℝ) : Operadores38 H (EspacioEliptico 2) (EspacioEliptico 2) where
  L h := L.aplica (eval h)
  B := eval
  f := f
  g := g
  seminormaL h := seminormaInterior U α (L.aplica (eval h))
  seminormaB h := seminormaInterior (frontier U) α (eval h)

/-- (3.69)–(3.70) en dimensión dos para una solución clásica dada.
La frontera en el Teorema 3.8 es toda la frontera geométrica. -/
theorem teorema318_dim2 {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μr μb : Measure (EspacioEliptico 2)) [IsProbabilityMeasure μr] [IsProbabilityMeasure μb]
    (U : Set (EspacioEliptico 2)) (hU : IsOpen U) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (dr : DatosMasa38 μr U 2 ε₀) (db : DatosMasa38 μb (frontier U) 1 ε₀)
    (sr : Muestreo38 P μr) (sb : Muestreo38 P μb)
    (L : OperadorEliptico 2) (lam B : ℝ) (hL : L.Datos U lam B)
    (eval : H → EspacioEliptico 2 → ℝ) (u f g : EspacioEliptico 2 → ℝ)
    (hu : ContDiffOn ℝ 2 u U) (huc : ContinuousOn u (closure U))
    (hEq : EqOn (L.aplica u) f U) (hDir : EqOn u g (frontier U))
    (mr mb : ℕ → ℕ) (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (hgr : ∀ᶠ n in atTop, n ≤ mr n) (hgb : ∀ᶠ n in atTop, n ≤ mb n)
    (lr lb α K : ℝ) (hlr : 0 < lr) (hlb : 0 < lb)
    (hα : 0 < α) (hαone : α < 1) (hK : 0 < K)
    (hrel : ∀ᶠ n in atTop, (mr n : ℝ) ≤ K * (mb n : ℝ) ^ 2)
    (Hm : ℕ → Set H) (hm v : ∀ n, Ω → Hm n)
    (hMeasHm : ∀ n, Measurable (fun ω => (hm n ω : H)))
    (hMeasV : ∀ n, Measurable (fun ω => (v n ω : H)))
    (hf : EsHolderInterior U α f) (hg : EsHolderInterior (frontier U) α g)
    (hCand : ∀ n h, h ∈ Hm n →
      ContDiffOn ℝ 2 (eval h) U ∧ ContinuousOn (eval h) (closure U) ∧
      EsHolderInterior U α (L.aplica (eval h)) ∧ EsHolderInterior (frontier U) α (eval h)) :
    let D := operadores318 L U eval f g α
    let base := fun n => D.base μr μb (mr n) (mb n) (hmr n) (hmb n)
      dr.C db.C dr.c db.c lr lb α dr.C_pos dr.c_pos hlr hlb
    let Pn := problemaMuestral mr mb base sr.Z sb.Z
    (∀ᵐ ω ∂P, ∃ R : ℝ, 0 ≤ R ∧ ∀ n,
      (Pn ω n).EsMinimizadorGlobal (Hm n) (hm n ω : H) ∧
      (Pn ω n).ComparadorExacto (Hm n) (v n ω : H) ∧
      (Pn ω n).regularidadTotal (v n ω : H) ≤ R) →
    μb.support = frontier U ∧ ∀ᵐ ω ∂P,
      let e := fun n => supResiduo (closure U) (fun x => eval (hm n ω : H) x - u x)
      Tendsto e atTop (𝓝 0) ∧
      e =O[atTop] fun n => (mr n : ℝ) ^ (-(α ^ 2 / (2 * (2 * α + 2)))) := by
  intro D base Pn hvar
  have hHolder (n : ℕ) : CotasHolder (base n) (Hm n) U (frontier U) α
      (seminormaInterior U α f) (seminormaInterior (frontier U) α g) := by
    refine ⟨seminormaInterior_nonneg _ _ _ hf, seminormaInterior_nonneg _ _ _ hg,
      fun h hh => ?_, seminormaInterior_cota _ _ _ hf hα, seminormaInterior_cota _ _ _ hg hα⟩
    obtain ⟨_, _, hr, hb⟩ := hCand n h hh
    exact ⟨seminormaInterior_nonneg _ _ _ hr, seminormaInterior_nonneg _ _ _ hb,
      seminormaInterior_cota _ _ _ hr hα, seminormaInterior_cota _ _ _ hb hα⟩
  have hs := teorema38_dim2 P μr μb U (frontier U) ε₀ hε₀ dr db sr sb D
    mr mb hmr hmb hgr hgb lr lb α _ _ K hlr hlb hα hαone.le hK hrel
    Hm hm v hMeasHm hMeasV hHolder hvar
  have hne := soporte_no_vacio μr U dr.concentrada
  obtain ⟨C, _, hest⟩ := cota318_error_dirichlet L (by decide) hU dr.acotado hne hL u f g
    hu huc hEq hDir
  refine ⟨soporte_de_DatosMasa38 μb isClosed_frontier hε₀ db, ?_⟩
  filter_upwards [hs] with ω hω
  obtain ⟨_, ⟨hr, hb⟩, hrO, hbO⟩ := hω
  refine transferencia318 mr hmr _ _ _ C _ _ ?_ (fun _ => supResiduo_noNeg _ _)
    (fun n => ?_) hr hb hrO hbO
  · simpa only [show 2 * α + 2 - 1 = 2 * α + 1 by ring] using
      exponente318_orden 2 α (by norm_num) hα
  · obtain ⟨hh, hhc, hHr, _⟩ := hCand n (hm n ω) (hm n ω).2
    have hres : EsHolderInterior U α (fun x => L.aplica (eval (hm n ω : H)) x - f x) :=
      ⟨_, add_nonneg (seminormaInterior_nonneg _ _ _ hHr) (seminormaInterior_nonneg _ _ _ hf),
        holder_resta U _ _ _ _ α (seminormaInterior_cota _ _ _ hHr hα)
          (seminormaInterior_cota _ _ _ hf hα)⟩
    exact hest _ hh hhc (acotado_por_Holder dr.acotado hne _ α hα hres)

#check cota318_error_dirichlet
#check cota318_error_dirichlet_Linfty
#check teorema318_dim2
#print axioms soporte_de_DatosMasa38
#print axioms cota318_error_dirichlet
#print axioms cota318_error_dirichlet_Linfty
#print axioms teorema318_dim2

end TesisPINN
