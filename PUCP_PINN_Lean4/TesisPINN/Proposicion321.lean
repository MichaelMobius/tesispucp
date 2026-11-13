import TesisPINN.Teorema318
import TesisPINN.ResiduoCuadrado

/-! Proposición 3.21: barrera cuadrática para Poisson en el cuadrado. -/

noncomputable section

namespace TesisPINN

open Set MeasureTheory Filter Asymptotics
open scoped Topology RealInnerProductSpace ENNReal
open EllipticPdes.Sobolev (partialD partialD_apply)

/-- Laplaciano positivo en las coordenadas canónicas de `Plano`. -/
def operadorPoisson : OperadorEliptico 2 where
  a _ i j := if i = j then 1 else 0
  b _ _ := 0
  c _ := 0

theorem parcial_eq_derivadaClásica (i : Fin 2) (v : Plano → ℝ) :
    partialD i v = derivadaClásica v i := by
  funext x
  simp [partialD_apply, derivadaClásica, basePlano, EuclideanSpace.basisFun_apply]

theorem operadorPoisson_eq_laplacianoClásico (v : Plano → ℝ) :
    operadorPoisson.aplica v = laplacianoClásico v := by
  funext x
  rw [operadorPoisson.aplica_eq_suma]
  simp [operadorPoisson, laplacianoClásico, parcial_eq_derivadaClásica, ite_mul]

theorem operadorPoisson_datos : operadorPoisson.Datos cuadrado 1 0 := by
  refine ⟨one_pos, le_rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx i j
    simp [operadorPoisson, eq_comm]
  · intro x hx ξ
    simp [operadorPoisson, ite_mul, pow_two]
  · simp [operadorPoisson]
  · simp [operadorPoisson]

theorem operadorPoisson_continuo : operadorPoisson.ContinuoEn cuadrado :=
  ⟨fun _ _ => continuousOn_const, fun _ => continuousOn_const, continuousOn_const⟩

private theorem cero_mem_cuadrado : (0 : Plano) ∈ cuadrado := by
  intro i
  change (-1 : ℝ) < 0 ∧ (0 : ℝ) < 1
  norm_num

/-- Clausura del producto de dos intervalos abiertos. -/
theorem clausura_cuadrado :
    closure cuadrado = {x : Plano | ∀ i, x i ∈ Icc (-1 : ℝ) 1} := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)
  change closure (e ⁻¹' (univ.pi fun _ => Ioo (-1 : ℝ) 1)) = _
  rw [← e.preimage_closure, closure_pi_set]
  simp [closure_Ioo (by norm_num : (-1 : ℝ) < 1), e, Set.preimage]

def barreraCuadratica321 (x : Plano) : ℝ := (2 - (x 0) ^ 2 - (x 1) ^ 2) / 4

theorem barreraCuadratica321_eq_norma (x : Plano) :
    barreraCuadratica321 x = (2 - ‖x‖ ^ 2) / 4 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  unfold barreraCuadratica321
  ring

theorem barreraCuadratica321_suave : ContDiff ℝ 2 barreraCuadratica321 := by
  unfold barreraCuadratica321
  fun_prop

theorem parcial_barreraCuadratica321 (i : Fin 2) :
    partialD i barreraCuadratica321 = fun x => -(x i) / 2 := by
  funext x
  have he : barreraCuadratica321 = fun x => (4 : ℝ)⁻¹ * (2 - ‖x‖ ^ 2) := by
    funext y
    rw [barreraCuadratica321_eq_norma]
    ring
  have hd : DifferentiableAt ℝ (fun y : Plano => 2 - ‖y‖ ^ 2) x :=
    (differentiableAt_const _).sub (differentiableAt_id.norm_sq)
  rw [he, partialD_apply, fderiv_const_mul hd, fderiv_const_sub, fderiv_norm_sq_apply]
  simp [EuclideanSpace.inner_single_right]
  ring

theorem segunda_parcial_barreraCuadratica321 (i j : Fin 2) (x : Plano) :
    partialD i (partialD j barreraCuadratica321) x = if i = j then -(1 / 2 : ℝ) else 0 := by
  rw [parcial_barreraCuadratica321, partialD_apply]
  have he : (fun y : Plano => -(y j) / 2) =
      fun y => -(1 / 2 : ℝ) * (PiLp.proj j : Plano →L[ℝ] ℝ) y := by
    funext y
    change -(y j) / 2 = -(1 / 2 : ℝ) * y j
    ring
  rw [he, fderiv_const_mul ((PiLp.proj j : Plano →L[ℝ] ℝ).differentiableAt),
    ContinuousLinearMap.fderiv]
  simp [PiLp.single_apply, Pi.single_apply, mul_ite]

theorem laplaciano_barreraCuadratica321 (x : Plano) :
    laplacianoClásico barreraCuadratica321 x = -1 := by
  rw [← operadorPoisson_eq_laplacianoClásico, operadorPoisson.aplica_eq_suma]
  norm_num [operadorPoisson, Fin.sum_univ_two, segunda_parcial_barreraCuadratica321]

theorem cotas_barreraCuadratica321 (x : Plano) (hx : x ∈ closure cuadrado) :
    0 ≤ barreraCuadratica321 x ∧ barreraCuadratica321 x ≤ 1 / 2 := by
  rw [clausura_cuadrado] at hx
  have h (i : Fin 2) : (x i) ^ 2 ≤ 1 := by
    have hi := abs_le.mpr (hx i)
    rw [← sq_abs (x i), ← one_pow 2]
    exact (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hi
  unfold barreraCuadratica321
  constructor
  · linarith [h 0, h 1]
  · linarith [sq_nonneg (x 0), sq_nonneg (x 1)]

theorem barreraCuadratica321_en_cero : barreraCuadratica321 0 = 1 / 2 := by
  norm_num [barreraCuadratica321_eq_norma]

/-- (3.76) con supremos puntuales y residuo acotado. -/
theorem proposicion321_barrera_cuadratica (v : Plano → ℝ)
    (hv : ContDiffOn ℝ 2 v cuadrado) (hvc : ContinuousOn v (closure cuadrado))
    (hb : ∃ M : ℝ, ∀ x ∈ cuadrado, |laplacianoClásico v x| ≤ M) :
    supResiduo (closure cuadrado) v ≤ supResiduo (frontier cuadrado) v +
      (1 / 2) * supResiduo cuadrado (laplacianoClásico v) := by
  have h := estabilidad_de_barrera operadorPoisson (by decide) cuadrado_abierto
    cuadrado_acotado ⟨0, cero_mem_cuadrado⟩ operadorPoisson_datos
    (1 / 2) (by norm_num) barreraCuadratica321 barreraCuadratica321_suave
    cotas_barreraCuadratica321
    (fun x _ => by rw [operadorPoisson_eq_laplacianoClásico, laplaciano_barreraCuadratica321])
    v hv hvc (by simpa only [operadorPoisson_eq_laplacianoClásico] using hb)
  simpa only [operadorPoisson_eq_laplacianoClásico] using h

theorem laplacianoClásico_continuo_cuadrado (v : Plano → ℝ)
    (hv : ContDiffOn ℝ 2 v cuadrado) : ContinuousOn (laplacianoClásico v) cuadrado := by
  rw [← operadorPoisson_eq_laplacianoClásico]
  exact operadorPoisson.aplica_continuo cuadrado_abierto operadorPoisson_continuo hv

theorem proposicion321_barrera_cuadratica_Linfty (v : Plano → ℝ)
    (hv : ContDiffOn ℝ 2 v cuadrado) (hvc : ContinuousOn v (closure cuadrado))
    (hb : ∃ M : ℝ, ∀ x ∈ cuadrado, |laplacianoClásico v x| ≤ M) :
    (eLpNormEssSup v (volume.restrict cuadrado)).toReal ≤ supResiduo (frontier cuadrado) v +
      (1 / 2) * (eLpNormEssSup (laplacianoClásico v) (volume.restrict cuadrado)).toReal := by
  obtain ⟨M, hM⟩ := cuadrado_acotado.isCompact_closure.exists_bound_of_continuousOn hvc
  have hc : ∀ x ∈ closure cuadrado, |v x| ≤ M := fun x hx => by simpa [Real.norm_eq_abs] using hM x hx
  rw [← supResiduo_eq_Linfty volume cuadrado_abierto (hvc.mono subset_closure)
    ⟨M, fun x hx => hc x (subset_closure hx)⟩,
    ← supResiduo_closure hvc ⟨M, hc⟩,
    ← supResiduo_eq_Linfty volume cuadrado_abierto (laplacianoClásico_continuo_cuadrado v hv) hb]
  exact proposicion321_barrera_cuadratica v hv hvc hb

/-- Para un dato continuo sobre un compacto, una medida de soporte completo
identifica la norma esencial con el supremo puntual. -/
theorem supResiduo_eq_Linfty_soporte (μ : Measure Plano) {S : Set Plano}
    (hs : μ.support = S) (hS : IsCompact S) {v : Plano → ℝ} (hv : ContinuousOn v S) :
    supResiduo S v = (eLpNormEssSup v μ).toReal := by
  have hSae : ∀ᵐ x ∂μ, x ∈ S := hs ▸ μ.support_mem_ae
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hv
  have hb : ∃ B : ℝ, ∀ x ∈ S, |v x| ≤ B :=
    ⟨M, fun x hx => by simpa [Real.norm_eq_abs] using hM x hx⟩
  have hfin := eLpNormEssSup_lt_top_of_ae_bound (hSae.mono hM)
  let F := (eLpNormEssSup v μ).toReal
  have ha : ∀ᵐ x ∂μ, |v x| ≤ F := by
    filter_upwards [enorm_ae_le_eLpNormEssSup v μ] with x hx
    simpa [F, Real.norm_eq_abs] using ENNReal.toReal_mono hfin.ne hx
  apply le_antisymm
  · refine (supResiduo_le S v F ENNReal.toReal_nonneg fun x hx => ?_).2
    by_contra! h
    have hnh : {y | F < |v y|} ∈ 𝓝[S] x := (hv x hx).abs.eventually (lt_mem_nhds h)
    obtain ⟨V, hV, hVS⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnh
    have hz : μ V = 0 := by
      have hVc : Vᶜ ∈ ae μ := by
        filter_upwards [hSae, ha] with y hy hFy
        exact fun hyV => (not_lt_of_ge hFy) (hVS ⟨hyV, hy⟩)
      simpa only [compl_compl] using mem_ae_iff.mp hVc
    exact (ne_of_gt ((Measure.mem_support_iff_forall x).mp (hs ▸ hx) V hV)) hz
  · have ha' : ∀ᵐ x ∂μ, ‖v x‖ ≤ supResiduo S v :=
      hSae.mono fun x hx => by simpa [Real.norm_eq_abs] using abs_le_supResiduo hx hb
    simpa [F, ENNReal.toReal_ofReal (supResiduo_nonneg_de_acotada hb)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound ha')

/-- (3.76) en norma esencial, incluso cuando el residuo es infinito. -/
theorem proposicion321_Linfty_extendido (μb : Measure Plano) (hμb : μb.support = frontier cuadrado)
    (v : Plano → ℝ) (hv : ContDiffOn ℝ 2 v cuadrado)
    (hvc : ContinuousOn v (closure cuadrado)) :
    eLpNormEssSup v (volume.restrict cuadrado) ≤ eLpNormEssSup v μb +
      ENNReal.ofReal (1 / 2) * eLpNormEssSup (laplacianoClásico v) (volume.restrict cuadrado) := by
  let μ := (volume : Measure Plano).restrict cuadrado
  let F := eLpNormEssSup (laplacianoClásico v) μ
  have hF : F ≤ ⊤ := le_top
  rcases eq_or_lt_of_le hF with htop | hfin
  · change _ ≤ _ + ENNReal.ofReal (1 / 2) * F
    rw [htop, ENNReal.mul_top (by norm_num), add_top]
    exact le_top
  · have hLv := laplacianoClásico_continuo_cuadrado v hv
    have ha : ∀ᵐ x ∂μ, |laplacianoClásico v x| ≤ F.toReal := by
      filter_upwards [enorm_ae_le_eLpNormEssSup (laplacianoClásico v) μ] with x hx
      simpa [F, Real.norm_eq_abs] using ENNReal.toReal_mono hfin.ne hx
    have hb : ∀ x ∈ cuadrado, |laplacianoClásico v x| ≤ F.toReal := by
      have heq : EqOn (fun x => min (|laplacianoClásico v x|) F.toReal)
          (fun x => |laplacianoClásico v x|) cuadrado :=
        Measure.eqOn_open_of_ae_eq (ha.mono fun _ hx => min_eq_left hx) cuadrado_abierto
          (hLv.abs.inf continuousOn_const) hLv.abs
      exact fun x hx => (heq hx).symm.trans_le (min_le_right _ _)
    have hcompact : IsCompact (frontier cuadrado) :=
      cuadrado_acotado.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
    have hbEq := supResiduo_eq_Linfty_soporte μb hμb hcompact (hvc.mono frontier_subset_closure)
    have hest := proposicion321_barrera_cuadratica_Linfty v hv hvc ⟨F.toReal, hb⟩
    rw [hbEq] at hest
    have hvfin : eLpNormEssSup v μ < ⊤ := by
      obtain ⟨M, hM⟩ := cuadrado_acotado.isCompact_closure.exists_bound_of_continuousOn hvc
      exact eLpNormEssSup_lt_top_of_ae_bound ((ae_restrict_mem cuadrado_abierto.measurableSet).mono
        fun x hx => hM x (subset_closure hx))
    calc
      _ = ENNReal.ofReal (eLpNormEssSup v μ).toReal := (ENNReal.ofReal_toReal hvfin.ne).symm
      _ ≤ ENNReal.ofReal ((eLpNormEssSup v μb).toReal + (1 / 2) * F.toReal) :=
        ENNReal.ofReal_le_ofReal hest
      _ ≤ _ := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hfin.ne]
        exact add_le_add_left ENNReal.ofReal_toReal_le _

/-- Cota del error para una solución clásica dada y datos de Dirichlet. -/
theorem error_poisson321 (u h f g : Plano → ℝ)
    (hu : ContDiffOn ℝ 2 u cuadrado) (hh : ContDiffOn ℝ 2 h cuadrado)
    (huc : ContinuousOn u (closure cuadrado)) (hhc : ContinuousOn h (closure cuadrado))
    (hEq : EqOn (laplacianoClásico u) f cuadrado) (hDir : EqOn u g (frontier cuadrado))
    (hb : ∃ M : ℝ, ∀ x ∈ cuadrado, |laplacianoClásico h x - f x| ≤ M) :
    supResiduo (closure cuadrado) (fun x => h x - u x) ≤
      supResiduo (frontier cuadrado) (fun x => h x - g x) +
        (1 / 2) * supResiduo cuadrado (fun x => laplacianoClásico h x - f x) := by
  have hr : EqOn (laplacianoClásico (fun x => h x - u x))
      (fun x => laplacianoClásico h x - f x) cuadrado := by
    intro x hx
    simp only [← operadorPoisson_eq_laplacianoClásico] at hEq ⊢
    rw [operadorPoisson.aplica_resta (hh.contDiffAt (cuadrado_abierto.mem_nhds hx))
      (hu.contDiffAt (cuadrado_abierto.mem_nhds hx)), hEq hx]
  have hg : EqOn (fun x => h x - u x) (fun x => h x - g x) (frontier cuadrado) :=
    fun _ hx => congrArg (fun a => _ - a) (hDir hx)
  obtain ⟨M, hM⟩ := hb
  have hest := proposicion321_barrera_cuadratica _ (hh.sub hu) (hhc.sub huc)
    ⟨M, fun x hx => by rw [hr hx]; exact hM x hx⟩
  rwa [supResiduo_congr hr, supResiduo_congr hg] at hest

theorem error_poisson321_dirichlet_exacto (u h f g : Plano → ℝ)
    (hu : ContDiffOn ℝ 2 u cuadrado) (hh : ContDiffOn ℝ 2 h cuadrado)
    (huc : ContinuousOn u (closure cuadrado)) (hhc : ContinuousOn h (closure cuadrado))
    (hEq : EqOn (laplacianoClásico u) f cuadrado) (hDir : EqOn u g (frontier cuadrado))
    (hhDir : EqOn h g (frontier cuadrado))
    (hb : ∃ M : ℝ, ∀ x ∈ cuadrado, |laplacianoClásico h x - f x| ≤ M) :
    supResiduo (closure cuadrado) (fun x => h x - u x) ≤
      (1 / 2) * supResiduo cuadrado (fun x => laplacianoClásico h x - f x) := by
  have he : EqOn (fun x => h x - g x) (fun _ => 0) (frontier cuadrado) :=
    fun _ hx => sub_eq_zero.mpr (hhDir hx)
  have hz : supResiduo (frontier cuadrado) (fun _ => 0) = 0 := by
    obtain ⟨ha, hb⟩ := supResiduo_le (frontier cuadrado) (fun _ => 0) 0 le_rfl
      (fun _ _ => by simp)
    exact le_antisymm hb ha
  simpa only [supResiduo_congr he, hz, zero_add] using
    error_poisson321 u h f g hu hh huc hhc hEq hDir hb

/-- Transferencia de una tasa uniforme del residuo para Dirichlet exacto. -/
theorem tasa_error_poisson321_dirichlet_exacto (u f g : Plano → ℝ)
    (h : ℕ → Plano → ℝ) (t : ℕ → ℝ)
    (hu : ContDiffOn ℝ 2 u cuadrado) (huc : ContinuousOn u (closure cuadrado))
    (hEq : EqOn (laplacianoClásico u) f cuadrado) (hDir : EqOn u g (frontier cuadrado))
    (hh : ∀ n, ContDiffOn ℝ 2 (h n) cuadrado)
    (hhc : ∀ n, ContinuousOn (h n) (closure cuadrado))
    (hhDir : ∀ n, EqOn (h n) g (frontier cuadrado))
    (hb : ∀ n, ∃ M : ℝ, ∀ x ∈ cuadrado, |laplacianoClásico (h n) x - f x| ≤ M)
    (hRate : (fun n => supResiduo cuadrado (fun x => laplacianoClásico (h n) x - f x)) =O[atTop] t) :
    (fun n => supResiduo (closure cuadrado) (fun x => h n x - u x)) =O[atTop] t := by
  refine (IsBigO.of_bound' (Eventually.of_forall fun n => ?_)).trans
    (hRate.const_mul_left (1 / 2))
  have hcont := (hhc n).sub huc
  obtain ⟨M, hM⟩ := cuadrado_acotado.isCompact_closure.exists_bound_of_continuousOn hcont
  have hnon := supResiduo_nonneg_de_acotada (v := fun x => h n x - u x)
    (U := closure cuadrado) ⟨M, fun x hx => by simpa [Real.norm_eq_abs] using hM x hx⟩
  rw [Real.norm_eq_abs, abs_of_nonneg hnon, Real.norm_eq_abs]
  exact (error_poisson321_dirichlet_exacto u (h n) f g hu (hh n) huc (hhc n) hEq
    hDir (hhDir n) (hb n)).trans (le_abs_self _)

/-- Aplicación al exponente interior de (3.28) cuando la clase impone
Dirichlet exacto. La única tasa supuesta es la del residuo. -/
theorem tasa_poisson321_de_residuo_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (mr : ℕ → ℕ) (α : ℝ) (u f g : Plano → ℝ) (h : ℕ → Ω → Plano → ℝ)
    (hu : ContDiffOn ℝ 2 u cuadrado) (huc : ContinuousOn u (closure cuadrado))
    (hEq : EqOn (laplacianoClásico u) f cuadrado) (hDir : EqOn u g (frontier cuadrado))
    (hcand : ∀ᵐ ω ∂P, ∀ n,
      ContDiffOn ℝ 2 (h n ω) cuadrado ∧ ContinuousOn (h n ω) (closure cuadrado) ∧
      EqOn (h n ω) g (frontier cuadrado) ∧
      ∃ M : ℝ, ∀ x ∈ cuadrado, |laplacianoClásico (h n ω) x - f x| ≤ M)
    (hRate : ∀ᵐ ω ∂P,
      (fun n => supResiduo cuadrado (fun x => laplacianoClásico (h n ω) x - f x)) =O[atTop]
        fun n => (mr n : ℝ) ^ (-(α ^ 2 / (2 * (2 * α + 2))))) :
    ∀ᵐ ω ∂P,
      (fun n => supResiduo (closure cuadrado) (fun x => h n ω x - u x)) =O[atTop]
        fun n => (mr n : ℝ) ^ (-(α ^ 2 / (2 * (2 * α + 2)))) := by
  filter_upwards [hcand, hRate] with ω hc hr
  exact tasa_error_poisson321_dirichlet_exacto u f g (fun n => h n ω) _ hu huc hEq hDir
    (fun n => (hc n).1) (fun n => (hc n).2.1) (fun n => (hc n).2.2.1)
    (fun n => (hc n).2.2.2) hr

#check proposicion321_barrera_cuadratica
#check proposicion321_barrera_cuadratica_Linfty
#check proposicion321_Linfty_extendido
#print axioms proposicion321_barrera_cuadratica
#print axioms proposicion321_barrera_cuadratica_Linfty
#print axioms proposicion321_Linfty_extendido
#print axioms error_poisson321
#print axioms error_poisson321_dirichlet_exacto
#print axioms tasa_error_poisson321_dirichlet_exacto
#print axioms tasa_poisson321_de_residuo_ae

end TesisPINN
