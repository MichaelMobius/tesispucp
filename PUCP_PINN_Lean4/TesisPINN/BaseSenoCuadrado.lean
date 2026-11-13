import TesisPINN.Proposicion321
import TesisPINN.DirichletLevantamiento
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! Modos seno de Dirichlet en el cuadrado. La frecuencia del índice `j`
es `j+1`. La medida de las clases espectrales es Lebesgue restringida. -/

noncomputable section

namespace TesisPINN

open Set Filter MeasureTheory EllipticPdes EllipticPdes.H1Graph
open EllipticPdes.Sobolev (partialD partialD_apply)
open scoped RealInnerProductSpace
open scoped Topology

def frecuenciaSeno (j : ℕ) : ℝ := ((j : ℝ) + 1) * Real.pi / 2

def senoDirichlet (j : ℕ) (x : ℝ) : ℝ := Real.sin (frecuenciaSeno j * (x + 1))

def modoSeno (p : ℕ × ℕ) (x : Plano) : ℝ :=
  senoDirichlet p.1 (x 0) * senoDirichlet p.2 (x 1)

def autovalorSeno (p : ℕ × ℕ) : ℝ :=
  Real.pi ^ 2 / 4 * (((p.1 : ℝ) + 1) ^ 2 + ((p.2 : ℝ) + 1) ^ 2)

theorem autovalorSeno_pos (p : ℕ × ℕ) : 0 < autovalorSeno p := by
  unfold autovalorSeno
  positivity

theorem senoDirichlet_suave (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (senoDirichlet j) := by
  unfold senoDirichlet
  fun_prop

theorem modoSeno_suave (p : ℕ × ℕ) : ContDiff ℝ (⊤ : ℕ∞) (modoSeno p) := by
  have hc (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plano => x i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).contDiff
  exact ((senoDirichlet_suave p.1).comp (hc 0)).mul ((senoDirichlet_suave p.2).comp (hc 1))

theorem senoDirichlet_extremos (j : ℕ) : senoDirichlet j (-1) = 0 ∧ senoDirichlet j 1 = 0 := by
  constructor
  · simp [senoDirichlet]
  · unfold senoDirichlet
    rw [show frecuenciaSeno j * ((1 : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) * Real.pi by
      unfold frecuenciaSeno; push_cast; ring]
    exact Real.sin_nat_mul_pi _

theorem modoSeno_cero_frontera (p : ℕ × ℕ) {x : Plano} (hx : x ∈ frontier cuadrado) :
    modoSeno p x = 0 := by
  rw [cuadrado_abierto.frontier_eq, clausura_cuadrado] at hx
  have h (i : Fin 2) : -1 ≤ x i ∧ x i ≤ 1 := hx.1 i
  have hbd : ∃ i : Fin 2, x i = -1 ∨ x i = 1 := by
    by_contra! hn
    apply hx.2
    intro i
    exact ⟨lt_of_le_of_ne (h i).1 (Ne.symm (hn i).1), lt_of_le_of_ne (h i).2 (hn i).2⟩
  obtain ⟨i, hi⟩ := hbd
  rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, hj⟩
  · subst i
    rcases hi with hi | hi
    · simp [modoSeno, hi, (senoDirichlet_extremos p.1).1]
    · simp [modoSeno, hi, (senoDirichlet_extremos p.1).2]
  · have h1 : i = 1 := by rw [hj, Subsingleton.elim j 0]; rfl
    rw [h1] at hi
    rcases hi with hi | hi
    · simp [modoSeno, hi, (senoDirichlet_extremos p.2).1]
    · simp [modoSeno, hi, (senoDirichlet_extremos p.2).2]

theorem abs_modoSeno_le_uno (p : ℕ × ℕ) (x : Plano) : |modoSeno p x| ≤ 1 := by
  unfold modoSeno senoDirichlet
  rw [abs_mul, ← mul_one (1 : ℝ)]
  exact mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one

private theorem analitica_dslope {f : ℝ → ℝ} (hf : ∀ x, AnalyticAt ℝ f x) (a x : ℝ) :
    AnalyticAt ℝ (dslope f a) x := by
  by_cases h : x = a
  · subst x
    obtain ⟨p, hp⟩ := hf a
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  · have hs : dslope f a =ᶠ[nhds x] fun y => (f y - f a) / (y - a) := by
      filter_upwards [(isClosed_singleton.isOpen_compl.mem_nhds h : {a}ᶜ ∈ nhds x)] with y hy
      rw [dslope_of_ne f (show y ≠ a from hy), slope_def_field]
    exact (((hf x).sub analyticAt_const).div
      (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr h)).congr hs.symm

private def cocienteSeno (j : ℕ) : ℝ → ℝ :=
  fun x => -dslope (dslope (senoDirichlet j) (-1)) 1 x

private theorem cocienteSeno_suave (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cocienteSeno j) := by
  have ha : ∀ x, AnalyticAt ℝ (senoDirichlet j) x := fun x =>
    Real.analyticAt_sin.comp (analyticAt_const.mul (analyticAt_id.add analyticAt_const))
  exact contDiff_iff_contDiffAt.mpr fun x =>
    ((analitica_dslope (analitica_dslope ha (-1)) 1 x).neg).contDiffAt

private theorem senoDirichlet_factor (j : ℕ) (x : ℝ) :
    senoDirichlet j x = (1 - x ^ 2) * cocienteSeno j x := by
  have h₁ (y : ℝ) := sub_smul_dslope (senoDirichlet j) (-1) y
  have h0 : dslope (senoDirichlet j) (-1) 1 = 0 := by
    specialize h₁ 1
    rw [smul_eq_mul, (senoDirichlet_extremos j).1, (senoDirichlet_extremos j).2] at h₁
    linarith
  have h₂ := sub_smul_dslope (dslope (senoDirichlet j) (-1)) 1 x
  rw [smul_eq_mul, h0, sub_zero] at h₂
  have hs := h₁ x
  rw [smul_eq_mul, (senoDirichlet_extremos j).1, sub_zero] at hs
  calc
    senoDirichlet j x = (x - -1) * dslope (senoDirichlet j) (-1) x := hs.symm
    _ = (1 - x ^ 2) * cocienteSeno j x := by rw [← h₂, cocienteSeno]; ring

private def cocienteModo (p : ℕ × ℕ) (x : Plano) : ℝ :=
  cocienteSeno p.1 (x 0) * cocienteSeno p.2 (x 1)

private theorem cocienteModo_suave (p : ℕ × ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cocienteModo p) := by
  have hc (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plano => x i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).contDiff
  exact ((cocienteSeno_suave p.1).comp (hc 0)).mul ((cocienteSeno_suave p.2).comp (hc 1))

def grafoModoSeno (p : ℕ × ℕ) : H01 (volume : Measure Plano) cuadrado :=
  ⟨psiGraph (cocienteModo p) (cocienteModo_suave p), psiGraph_mem_H01 _ _⟩

theorem grafoModoSeno_fnL_ae (p : ℕ × ℕ) :
    ⇑(fnL (grafoModoSeno p : H1Graph volume cuadrado)) =ᵐ[volumenPoisson] modoSeno p := by
  apply (psiGraph_fnL_ae (cocienteModo p) (cocienteModo_suave p)).trans
  apply Filter.EventuallyEq.of_eq
  funext x
  unfold modoSeno psiCuadrado cocienteModo
  rw [senoDirichlet_factor p.1 (x 0), senoDirichlet_factor p.2 (x 1)]
  ring

private theorem derivada_senoDirichlet (j : ℕ) (x : ℝ) :
    HasDerivAt (senoDirichlet j)
      (frecuenciaSeno j * Real.cos (frecuenciaSeno j * (x + 1))) x := by
  unfold senoDirichlet
  have h : HasDerivAt (fun y => frecuenciaSeno j * (y + 1)) (frecuenciaSeno j) x := by
    simpa using (((hasDerivAt_id x).add_const 1).const_mul (frecuenciaSeno j))
  simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin _).comp x h

private theorem derivada_cosDirichlet (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y => Real.cos (frecuenciaSeno j * (y + 1)))
      (-frecuenciaSeno j * senoDirichlet j x) x := by
  unfold senoDirichlet
  have h : HasDerivAt (fun y => frecuenciaSeno j * (y + 1)) (frecuenciaSeno j) x := by
    simpa using (((hasDerivAt_id x).add_const 1).const_mul (frecuenciaSeno j))
  simpa [Function.comp_def, mul_comm, neg_mul] using (Real.hasDerivAt_cos _).comp x h

private theorem parcial_separable {f g : ℝ → ℝ} {x : Plano} {a b : ℝ}
    (hf : HasDerivAt f a (x 0)) (hg : HasDerivAt g b (x 1)) (i : Fin 2) :
    partialD i (fun y => f (y 0) * g (y 1)) x =
      if i = 0 then a * g (x 1) else f (x 0) * b := by
  let p (j : Fin 2) : Plano →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) j
  have h₁ := hf.comp_hasFDerivAt x (p 0).hasFDerivAt
  have h₂ := hg.comp_hasFDerivAt x (p 1).hasFDerivAt
  have hd := (h₁.mul h₂).fderiv
  change fderiv ℝ (fun y => f (y 0) * g (y 1)) x = _ at hd
  rw [partialD_apply, hd]
  fin_cases i <;> simp [p, PiLp.single_apply] <;> ring

theorem modoSeno_ecuacion (p : ℕ × ℕ) (x : Plano) :
    -laplacianoClásico (modoSeno p) x = autovalorSeno p * modoSeno p x := by
  have h₀ : partialD 0 (modoSeno p) = fun x =>
      (frecuenciaSeno p.1 * Real.cos (frecuenciaSeno p.1 * (x 0 + 1))) * senoDirichlet p.2 (x 1) := by
    funext x
    unfold modoSeno
    simpa using parcial_separable (derivada_senoDirichlet p.1 (x 0))
      (derivada_senoDirichlet p.2 (x 1)) 0
  have h₁ : partialD 1 (modoSeno p) = fun x =>
      senoDirichlet p.1 (x 0) * (frecuenciaSeno p.2 * Real.cos (frecuenciaSeno p.2 * (x 1 + 1))) := by
    funext x
    unfold modoSeno
    simpa using parcial_separable (derivada_senoDirichlet p.1 (x 0))
      (derivada_senoDirichlet p.2 (x 1)) 1
  rw [← operadorPoisson_eq_laplacianoClásico, operadorPoisson.aplica_eq_suma]
  simp only [Fin.sum_univ_two, operadorPoisson, ite_true, Fin.zero_ne_one, Ne.symm Fin.zero_ne_one,
    ite_false, zero_mul, one_mul, zero_add, add_zero]
  rw [h₀, h₁, parcial_separable ((derivada_cosDirichlet p.1 (x 0)).const_mul _)
    (derivada_senoDirichlet p.2 (x 1)),
    parcial_separable (derivada_senoDirichlet p.1 (x 0))
    ((derivada_cosDirichlet p.2 (x 1)).const_mul _)]
  simp [autovalorSeno, modoSeno, frecuenciaSeno]
  ring

private theorem integral_cos_frecuencia (a : ℝ) (ha : a ≠ 0) (h : Real.sin (a * 2) = 0) :
    (∫ x : ℝ in (-1 : ℝ)..1, Real.cos (a * (x + 1))) = 0 := by
  have hd (x : ℝ) : HasDerivAt (fun y => Real.sin (a * (y + 1)) / a)
      (Real.cos (a * (x + 1))) x := by
    have hp : HasDerivAt (fun y => a * (y + 1)) a x := by
      simpa using ((hasDerivAt_id x).add_const 1).const_mul a
    convert (((Real.hasDerivAt_sin _).comp x hp).div_const a) using 1
    · rfl
    · field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((Real.continuous_cos.comp (continuous_const.mul (continuous_id.add continuous_const))).intervalIntegrable _ _)]
  norm_num [h]

theorem integral_senoDirichlet_mul (j k : ℕ) :
    (∫ x in Ioo (-1 : ℝ) 1, senoDirichlet j x * senoDirichlet k x) =
      if j = k then 1 else 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hplus : Real.sin ((frecuenciaSeno j + frecuenciaSeno k) * 2) = 0 := by
    rw [show (frecuenciaSeno j + frecuenciaSeno k) * 2 = ((j + k + 2 : ℕ) : ℝ) * Real.pi by
      unfold frecuenciaSeno; push_cast; ring]
    exact Real.sin_nat_mul_pi _
  have hdif : Real.sin ((frecuenciaSeno j - frecuenciaSeno k) * 2) = 0 := by
    rw [show (frecuenciaSeno j - frecuenciaSeno k) * 2 = ((j : ℤ) - (k : ℤ) : ℤ) * Real.pi by
      unfold frecuenciaSeno; push_cast; ring]
    exact Real.sin_int_mul_pi _
  have hpos (n : ℕ) : 0 < frecuenciaSeno n := by unfold frecuenciaSeno; positivity
  have hp := integral_cos_frecuencia _ (add_pos (hpos j) (hpos k)).ne' hplus
  have hcon (a : ℝ) : IntervalIntegrable (fun x => Real.cos (a * (x + 1))) volume (-1) 1 :=
    (Real.continuous_cos.comp (continuous_const.mul (continuous_id.add continuous_const))).intervalIntegrable _ _
  have htrig : (fun x => senoDirichlet j x * senoDirichlet k x) = fun x =>
      (1 / 2 : ℝ) * (Real.cos ((frecuenciaSeno j - frecuenciaSeno k) * (x + 1)) -
        Real.cos ((frecuenciaSeno j + frecuenciaSeno k) * (x + 1))) := by
    funext x
    have ht := Real.two_mul_sin_mul_sin (frecuenciaSeno j * (x + 1)) (frecuenciaSeno k * (x + 1))
    rw [← sub_mul, ← add_mul] at ht
    unfold senoDirichlet
    linarith only [ht]
  rw [htrig, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hcon _) (hcon _), hp, sub_zero]
  split_ifs with hjk
  · subst k
    norm_num [intervalIntegral.integral_const]
  · have hne : frecuenciaSeno j - frecuenciaSeno k ≠ 0 := by
      intro he
      apply hjk
      have h : ((j : ℝ) + 1) = (k : ℝ) + 1 := by
        unfold frecuenciaSeno at he
        apply (mul_right_cancel₀ Real.pi_pos.ne')
        linarith only [he]
      exact_mod_cast (add_right_cancel h : (j : ℝ) = (k : ℝ))
    rw [integral_cos_frecuencia _ hne hdif, mul_zero]

abbrev volumenIntervaloSeno : Measure ℝ := volume.restrict (Ioo (-1 : ℝ) 1)

private theorem senoDirichlet_memLp (j : ℕ) : MemLp (senoDirichlet j) 2 volumenIntervaloSeno := by
  letI : IsFiniteMeasure volumenIntervaloSeno := by
    rw [isFiniteMeasure_restrict]
    simp
  apply MemLp.of_bound (senoDirichlet_suave j).continuous.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => Real.abs_sin_le_one _

/-- Los senos en el intervalo, para volumen de Lebesgue sin normalizar. -/
def senoDirichletLp (j : ℕ) : Lp ℝ 2 volumenIntervaloSeno :=
  (senoDirichlet_memLp j).toLp (senoDirichlet j)

theorem senoDirichletLp_ae (j : ℕ) :
    ⇑(senoDirichletLp j) =ᵐ[volumenIntervaloSeno] senoDirichlet j :=
  (senoDirichlet_memLp j).coeFn_toLp

theorem senoDirichletLp_ortonormal : Orthonormal ℝ senoDirichletLp := by
  rw [orthonormal_iff_ite]
  intro j k
  rw [MeasureTheory.L2.inner_def, ← integral_senoDirichlet_mul]
  apply integral_congr_ae
  filter_upwards [(senoDirichlet_memLp j).coeFn_toLp, (senoDirichlet_memLp k).coeFn_toLp]
    with x hj hk
  change inner ℝ ((senoDirichletLp j) x) ((senoDirichletLp k) x) = _
  change (senoDirichletLp j) x = _ at hj
  change (senoDirichletLp k) x = _ at hk
  rw [hj, hk]
  simp [RCLike.inner_apply, mul_comm]

def modoSenoLp (p : ℕ × ℕ) : Lp ℝ 2 volumenPoisson :=
  fnL (grafoModoSeno p : H1Graph volume cuadrado)

private theorem integral_separable_cuadrado (f g : ℝ → ℝ) :
    (∫ x : Plano, f (x 0) * g (x 1) ∂volumenPoisson) =
      (∫ x, f x ∂volumenIntervaloSeno) * ∫ x, g x ∂volumenIntervaloSeno := by
  let e : Plano → ℝ × ℝ := fun x => (x 0, x 1)
  have he : MeasurePreserving e volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (ι := Fin 2))
  have hEmb : MeasurableEmbedding e :=
    ((MeasurableEquiv.finTwoArrow (α := ℝ)).measurableEmbedding.comp
      (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).toMeasurableEquiv.measurableEmbedding)
  let I := Ioo (-1 : ℝ) 1
  have hs : e ⁻¹' (I ×ˢ I) = cuadrado := by
    ext x
    simp [e, I, cuadrado, EllipticPdes.Poincare.euclBox, Fin.forall_fin_two]
  have hm := he.restrict_preimage (measurableSet_Ioo.prod measurableSet_Ioo :
    MeasurableSet (I ×ˢ I))
  rw [hs] at hm
  change MeasurePreserving e (volume.restrict cuadrado)
    (((volume : Measure ℝ).prod volume).restrict (I ×ˢ I)) at hm
  rw [← Measure.prod_restrict] at hm
  calc
    _ = ∫ z : ℝ × ℝ, f z.1 * g z.2 ∂volumenIntervaloSeno.prod volumenIntervaloSeno :=
      hm.integral_comp hEmb _
    _ = _ := integral_prod_mul f g

theorem modoSenoLp_ortonormal : Orthonormal ℝ modoSenoLp := by
  rw [orthonormal_iff_ite]
  intro p q
  rw [MeasureTheory.L2.inner_def]
  have hi : (fun x => inner ℝ (modoSenoLp p x) (modoSenoLp q x)) =ᵐ[volumenPoisson]
      (fun x => (senoDirichlet p.1 (x 0) * senoDirichlet q.1 (x 0)) *
        (senoDirichlet p.2 (x 1) * senoDirichlet q.2 (x 1))) := by
    filter_upwards [grafoModoSeno_fnL_ae p, grafoModoSeno_fnL_ae q] with x hp hq
    change inner ℝ ((fnL (grafoModoSeno p : H1Graph volume cuadrado)) x)
      ((fnL (grafoModoSeno q : H1Graph volume cuadrado)) x) = _
    rw [hp, hq]
    simp [modoSeno, RCLike.inner_apply]
    ring
  rw [integral_congr_ae hi, integral_separable_cuadrado
    (fun x => senoDirichlet p.1 x * senoDirichlet q.1 x)
    (fun x => senoDirichlet p.2 x * senoDirichlet q.2 x), integral_senoDirichlet_mul,
    integral_senoDirichlet_mul]
  rcases p with ⟨j, k⟩
  rcases q with ⟨l, m⟩
  by_cases hj : j = l <;> by_cases hk : k = m <;> simp [Prod.mk.injEq, hj, hk]

theorem modoSenoLp_norma (p : ℕ × ℕ) : ‖modoSenoLp p‖ = 1 :=
  modoSenoLp_ortonormal.norm_eq_one p

#check grafoModoSeno
#check modoSeno_ecuacion
#print axioms modoSeno_cero_frontera
#print axioms grafoModoSeno_fnL_ae
#print axioms modoSeno_ecuacion
#print axioms integral_senoDirichlet_mul
#print axioms senoDirichletLp_ortonormal
#print axioms modoSenoLp_ortonormal

end TesisPINN
