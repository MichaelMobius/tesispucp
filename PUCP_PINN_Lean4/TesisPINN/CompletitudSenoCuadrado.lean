import TesisPINN.BaseSenoCuadrado
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Completitud de los senos mediante aproximación uniforme en la clausura. -/

noncomputable section

namespace TesisPINN

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

def cosenoDirichlet (x : ℝ) : ℝ := Real.cos (Real.pi * (x + 1) / 2)

private theorem cosenoDirichlet_continuo : Continuous cosenoDirichlet := by
  unfold cosenoDirichlet
  fun_prop

private theorem cosenoDirichlet_inj : InjOn cosenoDirichlet (Icc (-1 : ℝ) 1) := by
  intro x hx y hy h
  have hp := Real.pi_pos
  have hmem (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) :
      Real.pi * (a + 1) / 2 ∈ Icc 0 Real.pi := by
    exact ⟨by nlinarith [ha.1], by nlinarith [ha.2]⟩
  have he := Real.strictAntiOn_cos.injOn (hmem x hx) (hmem y hy) h
  exact mul_left_cancel₀ hp.ne' (by linarith)

private theorem seno_primero_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < senoDirichlet 0 x := by
  have hp := Real.pi_pos
  unfold senoDirichlet frecuenciaSeno
  norm_num
  exact Real.sin_pos_of_pos_of_lt_pi
    (mul_pos (by positivity) (by linarith [hx.1]))
    (by nlinarith [mul_pos hp (show 0 < 1 - x by linarith [hx.2])])

private theorem seno_coseno_cero (x : ℝ) :
    cosenoDirichlet x * senoDirichlet 0 x = (1 / 2) * senoDirichlet 1 x := by
  have h : frecuenciaSeno 1 * (x + 1) = 2 * (Real.pi * (x + 1) / 2) := by
    norm_num [frecuenciaSeno]
    ring
  unfold cosenoDirichlet senoDirichlet
  rw [h, Real.sin_two_mul]
  norm_num [frecuenciaSeno]
  rw [show Real.pi / 2 * (x + 1) = Real.pi * (x + 1) / 2 by ring]
  ring

private theorem seno_coseno_succ (n : ℕ) (x : ℝ) :
    cosenoDirichlet x * senoDirichlet (n + 1) x =
      (1 / 2) * (senoDirichlet (n + 2) x + senoDirichlet n x) := by
  let t := Real.pi * (x + 1) / 2
  let u := frecuenciaSeno (n + 1) * (x + 1)
  have ha : frecuenciaSeno (n + 2) * (x + 1) = u + t := by
    dsimp [u, t, frecuenciaSeno]
    push_cast
    ring
  have hs : frecuenciaSeno n * (x + 1) = u - t := by
    dsimp [u, t, frecuenciaSeno]
    push_cast
    ring
  unfold cosenoDirichlet senoDirichlet
  change Real.cos t * Real.sin u =
    1 / 2 * (Real.sin (frecuenciaSeno (n + 2) * (x + 1)) +
      Real.sin (frecuenciaSeno n * (x + 1)))
  rw [ha, hs, Real.sin_add, Real.sin_sub]
  ring

private def senoEn {K : Type*} [TopologicalSpace K] (x : C(K, ℝ)) (n : ℕ) : C(K, ℝ) :=
  ⟨fun k => senoDirichlet n (x k), (senoDirichlet_suave n).continuous.comp x.continuous⟩

def cosenoEn {K : Type*} [TopologicalSpace K] (x : C(K, ℝ)) : C(K, ℝ) :=
  ⟨fun k => cosenoDirichlet (x k), cosenoDirichlet_continuo.comp x.continuous⟩

private theorem coseno_mul_seno_mem {K : Type*} [TopologicalSpace K]
    (S : Submodule ℝ C(K, ℝ)) (x a : C(K, ℝ))
    (h : ∀ n, a * senoEn x n ∈ S) (n : ℕ) :
    cosenoEn x * (a * senoEn x n) ∈ S := by
  cases n with
  | zero =>
    have he : cosenoEn x * (a * senoEn x 0) = (1 / 2 : ℝ) • (a * senoEn x 1) := by
      ext k
      change cosenoDirichlet (x k) * (a k * senoDirichlet 0 (x k)) =
        (1 / 2) * (a k * senoDirichlet 1 (x k))
      rw [mul_left_comm (cosenoDirichlet (x k)), seno_coseno_cero]
      ring
    rw [he]
    exact S.smul_mem _ (h 1)
  | succ n =>
    have he : cosenoEn x * (a * senoEn x (n + 1)) =
        (1 / 2 : ℝ) • (a * senoEn x (n + 2) + a * senoEn x n) := by
      ext k
      change cosenoDirichlet (x k) * (a k * senoDirichlet (n + 1) (x k)) =
        (1 / 2) * (a k * senoDirichlet (n + 2) (x k) + a k * senoDirichlet n (x k))
      rw [mul_left_comm (cosenoDirichlet (x k)), seno_coseno_succ]
      ring
    rw [he]
    exact S.smul_mem _ (S.add_mem (h (n + 2)) (h n))

private def preservaSubespacio {K : Type*} [TopologicalSpace K] (S : Submodule ℝ C(K, ℝ)) :
    Subalgebra ℝ C(K, ℝ) where
  carrier := {c | ∀ g ∈ S, c * g ∈ S}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb g hg
    rw [add_mul]
    exact S.add_mem (ha g hg) (hb g hg)
  mul_mem' := by
    intro a b ha hb g hg
    rw [mul_assoc]
    exact ha _ (hb g hg)
  algebraMap_mem' r := by
    intro g hg
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact S.smul_mem r hg

private theorem preserva_span {K ι : Type*} [TopologicalSpace K] (v : ι → C(K, ℝ))
    (c : C(K, ℝ)) (h : ∀ j, c * v j ∈ Submodule.span ℝ (range v)) :
    c ∈ preservaSubespacio (Submodule.span ℝ (range v)) := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact h j
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hx

private theorem span_senos_aproxima_producto {K ι : Type*} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (v : ι → C(K, ℝ)) (i₀ : ι)
    (hsep : (preservaSubespacio (Submodule.span ℝ (range v))).SeparatesPoints)
    (g : C(K, ℝ)) :
    v i₀ * g ∈ (Submodule.span ℝ (range v)).topologicalClosure := by
  let S := Submodule.span ℝ (range v)
  let M : C(K, ℝ) →L[ℝ] C(K, ℝ) := ContinuousLinearMap.mul ℝ C(K, ℝ) (v i₀)
  have hm := ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints
    (preservaSubespacio S) hsep g
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe] at hm
  have hc : IsClosed (M ⁻¹' (S.topologicalClosure : Set C(K, ℝ))) :=
    S.isClosed_topologicalClosure.preimage M.continuous
  refine closure_minimal ?_ hc hm
  intro a ha
  apply S.le_topologicalClosure
  change v i₀ * a ∈ S
  rw [mul_comm]
  exact ha _ (Submodule.subset_span (mem_range_self i₀))

/-- Una función del subespacio positiva casi en todas partes permite
trasladar la densidad uniforme del álgebra separadora a la norma L². -/
private theorem ortogonal_senos_compacto {K ι : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (v : ι → C(K, ℝ)) (i₀ : ι)
    (hsep : (preservaSubespacio (Submodule.span ℝ (range v))).SeparatesPoints)
    (hpos : ∀ᵐ x ∂μ, 0 < v i₀ x) (hbound : ∀ x, |v i₀ x| ≤ 1)
    (z : Lp ℝ 2 μ)
    (hz : ∀ i, inner ℝ (ContinuousMap.toLp 2 μ ℝ (v i)) z = 0) : z = 0 := by
  let J : C(K, ℝ) →L[ℝ] Lp ℝ 2 μ := ContinuousMap.toLp 2 μ ℝ
  let S := Submodule.span ℝ (range v)
  let w := v i₀
  let L : C(K, ℝ) →L[ℝ] ℝ := (innerSL ℝ z).comp J
  have hzero (a : C(K, ℝ)) (ha : a ∈ S) : inner ℝ z (J a) = 0 := by
    rw [real_inner_comm]
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      exact hz j
    | zero => simp
    | add a b _ _ ha hb => simp [inner_add_left, ha, hb]
    | smul r a _ ha => simp [real_inner_smul_left, ha]
  have hclosed : IsClosed {f : C(K, ℝ) | L f = 0} :=
    isClosed_singleton.preimage L.continuous
  have hL (f : C(K, ℝ)) : L (w * f) = 0 := by
    have hm : w * f ∈ closure (S : Set C(K, ℝ)) := span_senos_aproxima_producto v i₀ hsep f
    refine closure_minimal ?_ hclosed hm
    intro g hg
    exact hzero g hg
  have hmem : MemLp (fun x => z x * w x) 2 μ := by
    apply (Lp.memLp z).of_le ((Lp.aestronglyMeasurable z).mul w.continuous.aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      change |z x * w x| ≤ |z x|
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg (z x))
  let wz := hmem.toLp (fun x => z x * w x)
  have hinner (f : C(K, ℝ)) : inner ℝ wz (J f) = L (w * f) := by
    change inner ℝ wz (J f) = inner ℝ z (J (w * f))
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hmem.coeFn_toLp, ContinuousMap.coeFn_toLp (p := 2) μ (𝕜 := ℝ) f,
      ContinuousMap.coeFn_toLp (p := 2) μ (𝕜 := ℝ) (w * f)] with x hx hf hwf
    change wz x = _ at hx
    change J f x = _ at hf
    change J (w * f) x = _ at hwf
    rw [hx, hf, hwf]
    simp [RCLike.inner_apply, mul_left_comm, mul_comm]
  have hzclosed : IsClosed {a : Lp ℝ 2 μ | inner ℝ wz a = 0} :=
    isClosed_singleton.preimage (innerSL ℝ wz).continuous
  have hd : DenseRange J := ContinuousMap.toLp_denseRange ℝ μ ℝ (by norm_num)
  have hself : inner ℝ wz wz = 0 := by
    refine closure_minimal ?_ hzclosed (hd wz)
    rintro _ ⟨f, rfl⟩
    exact (hinner f).trans (hL f)
  have he : wz = 0 := inner_self_eq_zero.mp hself
  apply Lp.ext
  filter_upwards [hmem.coeFn_toLp, Lp.coeFn_zero ℝ 2 μ, hpos] with x hx h0 hp
  change wz x = _ at hx
  rw [he, h0] at hx
  rw [h0]
  exact (mul_eq_zero.mp hx.symm).resolve_right hp.ne'

private theorem ortogonal_senos_restringido {X ι : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {K : Set X} (hK : IsCompact K)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ K)
    (v : ι → C(K, ℝ)) (b : ι → Lp ℝ 2 μ) (i₀ : ι)
    (hsep : (preservaSubespacio (Submodule.span ℝ (range v))).SeparatesPoints)
    (hpos_ae : ∀ᵐ x ∂μ.comap ((↑) : K → X), 0 < v i₀ x)
    (hbound : ∀ x, |v i₀ x| ≤ 1)
    (hb : ∀ i, (fun x : K => b i x) =ᵐ[μ.comap ((↑) : K → X)] v i)
    (z : Lp ℝ 2 μ) (hz : ∀ i, inner ℝ (b i) z = 0) : z = 0 := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ν := μ.comap ((↑) : K → X)
  have hm : MeasurePreserving ((↑) : K → X) ν μ := by
    have h := measurePreserving_subtype_coe (μa := μ) hK.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hμ] at h
  let J : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 ν := Lp.compMeasurePreservingₗᵢ ℝ _ hm
  have hJ (i : ι) : J (b i) = ContinuousMap.toLp 2 ν ℝ (v i) := by
    apply Lp.ext
    exact ((Lp.coeFn_compMeasurePreserving (b i) hm).trans (hb i)).trans
      (ContinuousMap.coeFn_toLp ν (𝕜 := ℝ) (v i)).symm
  have he : J z = 0 := ortogonal_senos_compacto ν v i₀ hsep hpos_ae hbound (J z) (fun i => by
    rw [← hJ, J.inner_map_map]
    exact hz i)
  exact J.injective (by rw [he, map_zero])

/-- Densidad de continuas con soporte compacto dentro del dominio abierto.
Se formula en el subtipo abierto con la medida inducida por Lebesgue. -/
private theorem densidad_continuas_soporte_compacto {X : Type*} [MetricSpace X]
    [WeaklyLocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.Regular] :
    Dense {z : Lp ℝ 2 μ | ∃ f : X → ℝ, Continuous f ∧ HasCompactSupport f ∧
      (⇑z =ᵐ[μ] f)} := by
  intro z
  rw [EMetric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  obtain ⟨f, hcs, hdist, hc, hm⟩ :=
    (Lp.memLp z).exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hδ.ne'
  refine ⟨hm.toLp f, ⟨f, hc, hcs, hm.coeFn_toLp⟩, ?_⟩
  rw [← Lp.toLp_coeFn z (Lp.memLp z), Lp.edist_toLp_toLp]
  exact hdist.trans_lt hδε

private theorem cociente_seno_continuo {X : Type*} [TopologicalSpace X]
    {U : Set X} {f w : X → ℝ} (hf : Continuous f) (hw : Continuous w)
    (hs : tsupport f ⊆ U) (hp : ∀ x ∈ U, 0 < w x) :
    Continuous (fun x => f x / w x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hf.continuousAt.div hw.continuousAt (hp x hx).ne'
  · have hn : (tsupport f)ᶜ ∈ 𝓝 x :=
      isClosed_closure.isOpen_compl.mem_nhds (fun h => hx (hs h))
    refine (continuousAt_const (x := x) (y := (0 : ℝ))).congr ?_
    filter_upwards [hn] with y hy
    have hyf : f y = 0 := not_not.mp fun h => hy (subset_tsupport f h)
    simp [hyf]

def intervaloCerrado : Set ℝ := Icc (-1 : ℝ) 1

def coordenadaIntervalo : C(intervaloCerrado, ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def senosIntervalo := senoEn coordenadaIntervalo

theorem intervalo_densidad_continuas_soporte_compacto :
    let U := Ioo (-1 : ℝ) 1
    let μ := (volume : Measure ℝ).comap ((↑) : U → ℝ)
    Dense {z : Lp ℝ 2 μ | ∃ f : U → ℝ, Continuous f ∧ HasCompactSupport f ∧ (⇑z =ᵐ[μ] f)} := by
  dsimp
  letI : LocallyCompactSpace (Ioo (-1 : ℝ) 1) := isOpen_Ioo.locallyCompactSpace
  letI : ((volume : Measure ℝ).comap ((↑) : Ioo (-1 : ℝ) 1 → ℝ)).Regular :=
    Measure.Regular.comap' volume isOpen_Ioo.isOpenEmbedding_subtypeVal
  exact densidad_continuas_soporte_compacto _

theorem intervalo_cociente_seno_continuo {f : ℝ → ℝ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo (-1 : ℝ) 1) :
    Continuous (fun x => f x / senoDirichlet 0 x) :=
  cociente_seno_continuo hf (senoDirichlet_suave 0).continuous hs (fun _ => seno_primero_pos)

private theorem intervalo_separa :
    (preservaSubespacio (Submodule.span ℝ (range senosIntervalo))).SeparatesPoints := by
  intro x y hxy
  refine ⟨cosenoEn coordenadaIntervalo, ⟨_, ?_, rfl⟩, ?_⟩
  · apply preserva_span
    intro n
    simpa [senosIntervalo] using coseno_mul_seno_mem
      (Submodule.span ℝ (range senosIntervalo)) coordenadaIntervalo 1
      (fun k => by simpa [senosIntervalo] using
        Submodule.subset_span (R := ℝ) (mem_range_self (f := senosIntervalo) k)) n
  · intro he
    exact hxy (Subtype.ext (cosenoDirichlet_inj x.property y.property he))

/-- Los productos del primer seno con polinomios en el coseno están en el
subespacio generado por los modos continuos. -/
theorem intervalo_seno_mul_polinomio_mem (P : Polynomial ℝ) :
    senosIntervalo 0 * P.eval₂ (algebraMap ℝ C(intervaloCerrado, ℝ))
      (cosenoEn coordenadaIntervalo) ∈ Submodule.span ℝ (range senosIntervalo) := by
  let S := Submodule.span ℝ (range senosIntervalo)
  have hmem (k : ℕ) : senosIntervalo k ∈ S :=
    Submodule.subset_span (mem_range_self (f := senosIntervalo) k)
  have hc : cosenoEn coordenadaIntervalo ∈ preservaSubespacio S := by
    apply preserva_span
    intro n
    have h := coseno_mul_seno_mem S coordenadaIntervalo 1 (fun k => by
      rw [one_mul]
      exact hmem k) n
    rw [one_mul] at h
    exact h
  rw [mul_comm]
  change _ ∈ S
  rw [← Polynomial.aeval_def, ← smul_eq_mul]
  exact Polynomial.aeval_apply_smul_mem_of_le_comap' (hmem 0)
    P (cosenoEn coordenadaIntervalo) (fun a ha => hc a ha)

private theorem senoDirichletLp_eq_zero (z : Lp ℝ 2 volumenIntervaloSeno)
    (hz : ∀ i, inner ℝ (senoDirichletLp i) z = 0) : z = 0 := by
  let I := Ioo (-1 : ℝ) 1
  letI : IsFiniteMeasure volumenIntervaloSeno := by
    rw [isFiniteMeasure_restrict]
    simp
  have hI : ∀ᵐ x ∂volumenIntervaloSeno, x ∈ I := ae_restrict_mem measurableSet_Ioo
  have hK : ∀ᵐ x ∂volumenIntervaloSeno, x ∈ intervaloCerrado :=
    hI.mono fun _ hx => Ioo_subset_Icc_self hx
  have hμ : ∀ᵐ x : intervaloCerrado ∂volumenIntervaloSeno.comap Subtype.val,
      (x : ℝ) ∈ I := by
    have h := measurePreserving_subtype_coe (μa := volumenIntervaloSeno)
      (s := intervaloCerrado) measurableSet_Icc
    rw [Measure.restrict_eq_self_of_ae_mem hK] at h
    exact h.quasiMeasurePreserving.ae hI
  apply ortogonal_senos_restringido (K := intervaloCerrado) isCompact_Icc volumenIntervaloSeno
    hK senosIntervalo senoDirichletLp 0 intervalo_separa
  · exact hμ.mono fun x hx => seno_primero_pos hx
  · intro x
    exact Real.abs_sin_le_one _
  · intro i
    have h := measurePreserving_subtype_coe (μa := volumenIntervaloSeno)
      (s := intervaloCerrado) measurableSet_Icc
    rw [Measure.restrict_eq_self_of_ae_mem hK] at h
    exact h.quasiMeasurePreserving.ae (senoDirichletLp_ae i)
  · exact hz

/-- Los senos de frecuencias positivas son completos en Lebesgue sobre el intervalo abierto. -/
theorem senoDirichletLp_complete :
    (Submodule.span ℝ (range senoDirichletLp)).topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.orthogonal_eq_top_iff]
  apply le_antisymm _ bot_le
  intro z hz
  rw [Submodule.mem_bot]
  exact senoDirichletLp_eq_zero z fun i =>
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (mem_range_self i)) hz

def coordenadaCuadrado (i : Fin 2) : C(closure cuadrado, ℝ) :=
  ⟨fun x => (x : Plano) i,
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).continuous).comp continuous_subtype_val⟩

def senosCuadrado (p : ℕ × ℕ) : C(closure cuadrado, ℝ) :=
  senoEn (coordenadaCuadrado 0) p.1 * senoEn (coordenadaCuadrado 1) p.2

theorem cuadrado_densidad_continuas_soporte_compacto :
    let μ := (volume : Measure Plano).comap ((↑) : cuadrado → Plano)
    Dense {z : Lp ℝ 2 μ | ∃ f : cuadrado → ℝ, Continuous f ∧ HasCompactSupport f ∧ (⇑z =ᵐ[μ] f)} := by
  dsimp
  letI : LocallyCompactSpace cuadrado := cuadrado_abierto.locallyCompactSpace
  letI : ((volume : Measure Plano).comap ((↑) : cuadrado → Plano)).Regular :=
    Measure.Regular.comap' volume cuadrado_abierto.isOpenEmbedding_subtypeVal
  exact densidad_continuas_soporte_compacto _

theorem cuadrado_cociente_seno_continuo {f : Plano → ℝ} (hf : Continuous f)
    (hs : tsupport f ⊆ cuadrado) :
    Continuous (fun x => f x / modoSeno (0, 0) x) :=
  cociente_seno_continuo hf (modoSeno_suave (0, 0)).continuous hs fun _ hx =>
    mul_pos (seno_primero_pos (hx 0)) (seno_primero_pos (hx 1))

private theorem cuadrado_coseno_preserva (i : Fin 2) :
    cosenoEn (coordenadaCuadrado i) ∈
      preservaSubespacio (Submodule.span ℝ (range senosCuadrado)) := by
  let S := Submodule.span ℝ (range senosCuadrado)
  have h0 : cosenoEn (coordenadaCuadrado 0) ∈ preservaSubespacio S := by
    apply preserva_span
    intro p
    rw [show senosCuadrado p = senoEn (coordenadaCuadrado 1) p.2 *
      senoEn (coordenadaCuadrado 0) p.1 by exact mul_comm _ _]
    apply coseno_mul_seno_mem
    intro n
    rw [mul_comm]
    exact Submodule.subset_span (mem_range_self (f := senosCuadrado) (n, p.2))
  have h1 : cosenoEn (coordenadaCuadrado 1) ∈ preservaSubespacio S := by
    apply preserva_span
    intro p
    apply coseno_mul_seno_mem S (coordenadaCuadrado 1) (senoEn (coordenadaCuadrado 0) p.1)
    intro n
    exact Submodule.subset_span (mem_range_self (f := senosCuadrado) (p.1, n))
  fin_cases i
  · exact h0
  · exact h1

private theorem cuadrado_separa :
    (preservaSubespacio (Submodule.span ℝ (range senosCuadrado))).SeparatesPoints := by
  have hmem (x : closure cuadrado) (i : Fin 2) : (x : Plano) i ∈ intervaloCerrado := by
    generalize hval : (x : Plano) = y
    have hx : y ∈ closure cuadrado := hval ▸ x.property
    rw [clausura_cuadrado] at hx
    exact hx i
  intro x y hxy
  have hcoord : ∃ i : Fin 2, (x : Plano) i ≠ (y : Plano) i := by
    by_contra! h
    apply hxy
    apply Subtype.ext
    exact PiLp.ext h
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨cosenoEn (coordenadaCuadrado i), ⟨_, cuadrado_coseno_preserva i, rfl⟩, ?_⟩
  · exact fun he => hi (cosenoDirichlet_inj (hmem x i) (hmem y i) he)

/-- Todo elemento del álgebra generada por los dos cosenos, multiplicado por
el primer modo, es una combinación finita de modos tensoriales. -/
theorem cuadrado_seno_mul_polinomio_mem (P : C(closure cuadrado, ℝ))
    (hP : P ∈ Algebra.adjoin ℝ (range fun i : Fin 2 => cosenoEn (coordenadaCuadrado i))) :
    senosCuadrado (0, 0) * P ∈ Submodule.span ℝ (range senosCuadrado) := by
  let S := Submodule.span ℝ (range senosCuadrado)
  have hle : Algebra.adjoin ℝ (range fun i : Fin 2 => cosenoEn (coordenadaCuadrado i)) ≤
      preservaSubespacio S := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact cuadrado_coseno_preserva i
  rw [mul_comm]
  exact hle hP _ (Submodule.subset_span (mem_range_self (0, 0)))

private theorem mem_span_de_soporte {X ι : Type*} [TopologicalSpace X] {U K : Set X}
    (hK : IsCompact K) [T2Space X]
    (v : ι → C(K, ℝ)) (i₀ : ι)
    (hsep : (preservaSubespacio (Submodule.span ℝ (range v))).SeparatesPoints)
    {f w : X → ℝ} (hf : Continuous f) (hw : Continuous w)
    (hs : tsupport f ⊆ U) (hp : ∀ x ∈ U, 0 < w x)
    (hv : ∀ x : K, v i₀ x = w x) :
    (⟨fun x => f x, hf.comp continuous_subtype_val⟩ : C(K, ℝ)) ∈
      (Submodule.span ℝ (range v)).topologicalClosure := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let g : C(K, ℝ) :=
    ⟨fun x => f x / w x, (cociente_seno_continuo hf hw hs hp).comp continuous_subtype_val⟩
  have he : (⟨fun x => f x, hf.comp continuous_subtype_val⟩ : C(K, ℝ)) = v i₀ * g := by
    ext x
    change f x = v i₀ x * (f x / w x)
    rw [hv]
    by_cases hx : (x : X) ∈ U
    · field_simp [(hp x hx).ne']
    · have hfx : f x = 0 := not_not.mp fun h => hx (hs (subset_tsupport f h))
      simp [hfx]
  rw [he]
  exact span_senos_aproxima_producto v i₀ hsep g

theorem intervalo_aproxima_soporte_compacto {f : ℝ → ℝ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo (-1 : ℝ) 1) :
    (⟨fun x => f x, hf.comp continuous_subtype_val⟩ : C(intervaloCerrado, ℝ)) ∈
      (Submodule.span ℝ (range senosIntervalo)).topologicalClosure :=
  mem_span_de_soporte isCompact_Icc senosIntervalo 0 intervalo_separa hf
    (senoDirichlet_suave 0).continuous hs (fun _ => seno_primero_pos) (fun _ => rfl)

theorem cuadrado_aproxima_soporte_compacto {f : Plano → ℝ} (hf : Continuous f)
    (hs : tsupport f ⊆ cuadrado) :
    (⟨fun x => f x, hf.comp continuous_subtype_val⟩ : C(closure cuadrado, ℝ)) ∈
      (Submodule.span ℝ (range senosCuadrado)).topologicalClosure :=
  mem_span_de_soporte cuadrado_acotado.isCompact_closure senosCuadrado (0, 0) cuadrado_separa hf
    (modoSeno_suave (0, 0)).continuous hs
    (fun _ hx => mul_pos (seno_primero_pos (hx 0)) (seno_primero_pos (hx 1))) (fun _ => rfl)

/-- Los coeficientes seno distinguen cualquier elemento de L² del cuadrado. -/
theorem modoSenoLp_eq_zero_of_inner_eq_zero (z : Lp ℝ 2 volumenPoisson)
    (hz : ∀ p, inner ℝ (modoSenoLp p) z = 0) : z = 0 := by
  letI : IsFiniteMeasure volumenPoisson := by
    rw [isFiniteMeasure_restrict]
    exact ((measure_mono subset_closure).trans_lt
      (cuadrado_acotado.isCompact_closure.measure_lt_top (μ := (volume : Measure Plano)))).ne
  have hU : ∀ᵐ x ∂volumenPoisson, x ∈ cuadrado :=
    ae_restrict_mem cuadrado_abierto.measurableSet
  have hK : ∀ᵐ x ∂volumenPoisson, x ∈ closure cuadrado := hU.mono fun _ hx => subset_closure hx
  have hm := measurePreserving_subtype_coe (μa := volumenPoisson)
    (isClosed_closure (s := cuadrado)).measurableSet
  rw [Measure.restrict_eq_self_of_ae_mem hK] at hm
  apply ortogonal_senos_restringido cuadrado_acotado.isCompact_closure volumenPoisson
    hK senosCuadrado modoSenoLp (0, 0) cuadrado_separa
  · filter_upwards [hm.quasiMeasurePreserving.ae hU] with x hx
    change 0 < senoDirichlet 0 ((x : Plano) 0) * senoDirichlet 0 ((x : Plano) 1)
    exact mul_pos (seno_primero_pos (hx 0)) (seno_primero_pos (hx 1))
  · intro x
    exact abs_modoSeno_le_uno (0, 0) x
  · intro p
    exact hm.quasiMeasurePreserving.ae (grafoModoSeno_fnL_ae p)
  · exact hz

theorem modoSenoLp_complete :
    (Submodule.span ℝ (range modoSenoLp)).topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.orthogonal_eq_top_iff]
  apply le_antisymm _ bot_le
  intro z hz
  rw [Submodule.mem_bot]
  exact modoSenoLp_eq_zero_of_inner_eq_zero z fun p =>
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (mem_range_self p)) hz

/-- Base ortonormal completa sobre Lebesgue restringida al cuadrado abierto. -/
def baseHilbertSenoCuadrado : HilbertBasis (ℕ × ℕ) ℝ (Lp ℝ 2 volumenPoisson) :=
  HilbertBasis.mk modoSenoLp_ortonormal modoSenoLp_complete.ge

@[simp] theorem coe_baseHilbertSenoCuadrado : ⇑baseHilbertSenoCuadrado = modoSenoLp :=
  HilbertBasis.coe_mk _ _

#check senoDirichletLp_complete
#check modoSenoLp_complete
#print axioms senoDirichletLp_complete
#print axioms modoSenoLp_eq_zero_of_inner_eq_zero
#print axioms modoSenoLp_complete
#print axioms baseHilbertSenoCuadrado

end TesisPINN
