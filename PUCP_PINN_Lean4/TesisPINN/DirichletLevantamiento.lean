import TesisPINN.PuentePoisson38_320

/-! Dirichlet exacto mediante un levantamiento globalmente suave. -/

noncomputable section

open MeasureTheory Filter TopologicalSpace EllipticPdes EllipticPdes.H1Graph Asymptotics
open scoped Distributions

namespace TesisPINN

private theorem continuo_memLp_cuadrado {F : Type*} [NormedAddCommGroup F]
    (v : Plano → F) (hv : Continuous v) : MemLp v 2 volumenPoisson := by
  letI : IsFiniteMeasure volumenPoisson :=
    isFiniteMeasure_restrict.mpr cuadrado_acotado.measure_lt_top.ne
  obtain ⟨M, hM⟩ := cuadrado_acotado.isCompact_closure.exists_bound_of_continuousOn hv.continuousOn
  apply MemLp.of_bound hv.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem cuadrado_abierto.measurableSet] with x hx
  exact hM x (subset_closure hx)

private theorem continuo_grad_suave (G : CandidatoPoisson) :
    Continuous (gradient G.val) :=
  (InnerProductSpace.toDual ℝ Plano).symm.continuous.comp
    (G.property.continuous_fderiv (by simp))

/-- Grafo de una función suave en el cuadrado, con valor y gradiente en L². -/
def grafoSuaveCuadrado (G : CandidatoPoisson) : H1Graph (volume : Measure Plano) cuadrado :=
  H1Graph.mk (continuo_memLp_cuadrado G.val G.property.continuous).toLp
    (continuo_memLp_cuadrado (gradient G.val) (continuo_grad_suave G)).toLp

theorem grafoSuaveCuadrado_fnL_ae (G : CandidatoPoisson) :
    ⇑(fnL (grafoSuaveCuadrado G)) =ᵐ[volumenPoisson] G.val :=
  (continuo_memLp_cuadrado G.val G.property.continuous).coeFn_toLp

theorem grafoSuaveCuadrado_gradL_ae (G : CandidatoPoisson) :
    ⇑(gradL (grafoSuaveCuadrado G)) =ᵐ[volumenPoisson] gradient G.val :=
  (continuo_memLp_cuadrado (gradient G.val) (continuo_grad_suave G)).coeFn_toLp

theorem grafoSuaveCuadrado_mem_W12 (G : CandidatoPoisson) :
    grafoSuaveCuadrado G ∈ W12 (volume : Measure Plano) cuadrado := by
  apply (mem_W12_iff_hasWeakFDerivOn cuadrado_abierto _).2
  have h := hasWeakFDerivOn_fderiv (Ω := cuadradoOpens) (μ := volume)
    (G.property.of_le (by simp)).contDiffOn
  apply h.congr_ae (grafoSuaveCuadrado_fnL_ae G).symm
  filter_upwards [grafoSuaveCuadrado_gradL_ae G] with x hx
  rw [hx]
  change fderiv ℝ G.val x = (InnerProductSpace.toDual ℝ Plano) (gradient G.val x)
  simp [gradient]

def aproximacionLevantada (G q : CandidatoPoisson) : Plano → ℝ :=
  G.val + aproximacionPoisson q

theorem aproximacionLevantada_suave (G q : CandidatoPoisson) :
    ContDiff ℝ (⊤ : ℕ∞) (aproximacionLevantada G q) :=
  G.property.add (psiCuadrado_suave.mul q.property)

def grafoLevantado (G q : CandidatoPoisson) : H1Graph (volume : Measure Plano) cuadrado :=
  grafoSuaveCuadrado G + grafoPoisson q

theorem grafoLevantado_mem_W12 (G q : CandidatoPoisson) :
    grafoLevantado G q ∈ W12 (volume : Measure Plano) cuadrado :=
  Submodule.add_mem _ (grafoSuaveCuadrado_mem_W12 G)
    (H01_le_W12 (psiGraph_mem_H01 q.val q.property))

theorem grafoLevantado_fnL_ae (G q : CandidatoPoisson) :
    ⇑(fnL (grafoLevantado G q)) =ᵐ[volumenPoisson] aproximacionLevantada G q := by
  rw [grafoLevantado, map_add]
  exact (Lp.coeFn_add _ _).trans
    ((grafoSuaveCuadrado_fnL_ae G).add (psiGraph_fnL_ae q.val q.property))

theorem aproximacionLevantada_frontera (G q : CandidatoPoisson) (x : Plano)
    (hx : x ∈ frontier cuadrado) : aproximacionLevantada G q x = G.val x := by
  change G.val x + psiCuadrado x * q.val x = G.val x
  rw [psiCuadrado_cero_frontera x hx, zero_mul, add_zero]

theorem errorLevantado_eq (G q : CandidatoPoisson)
    (u : H1Graph (volume : Measure Plano) cuadrado) :
    grafoLevantado G q - u = grafoPoisson q - (u - grafoSuaveCuadrado G) := by
  unfold grafoLevantado
  abel

theorem errorLevantado_mem_H01 (G q : CandidatoPoisson)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (hu : u - grafoSuaveCuadrado G ∈ H01 (volume : Measure Plano) cuadrado) :
    grafoLevantado G q - u ∈ H01 (volume : Measure Plano) cuadrado := by
  rw [errorLevantado_eq]
  exact Submodule.sub_mem _ (psiGraph_mem_H01 q.val q.property) hu

def residuoLevantado (G q : CandidatoPoisson) (f : Lp ℝ 2 volumenPoisson) :
    Lp ℝ 2 volumenPoisson :=
  laplacianoLp (aproximacionLevantada G q) (aproximacionLevantada_suave G q) - f

theorem residuoLevantado_ae (G q : CandidatoPoisson)
    (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson) :
    ⇑(residuoLevantado G q (datoPoissonLp f hf)) =ᵐ[volumenPoisson]
      (fun x => laplacianoClásico (aproximacionLevantada G q) x - f x) :=
  (Lp.coeFn_sub _ _).trans
    ((laplacianoLp_ae _ (aproximacionLevantada_suave G q)).sub (datoPoissonLp_ae f hf))

private theorem distribucion_sub_lp (a b : Lp ℝ 2 volumenPoisson) :
    Distribution.ofFun cuadradoOpens (a - b) volume ⊤ =
      Distribution.ofFun cuadradoOpens a volume ⊤ -
      Distribution.ofFun cuadradoOpens b volume ⊤ := by
  calc
    _ = Distribution.ofFun cuadradoOpens
        ((a : Plano → ℝ) - (b : Plano → ℝ)) volume ⊤ :=
      Distribution.ofFun_congr_ae (Lp.coeFn_sub a b)
    _ = _ := by
      rw [sub_eq_add_neg, Distribution.ofFun_add
        (locallyIntegrableOn_lp a) (locallyIntegrableOn_lp b).neg, Distribution.ofFun_neg]
      rfl

theorem laplaciano_errorLevantado (G q : CandidatoPoisson)
    (u : H1Graph (volume : Measure Plano) cuadrado) (f : Lp ℝ 2 volumenPoisson)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens f volume ⊤) :
    laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL (grafoLevantado G q - u)) volume ⊤) =
      Distribution.ofFun cuadradoOpens (residuoLevantado G q f) volume ⊤ := by
  rw [map_sub, distribucion_sub_lp, map_sub,
    Distribution.ofFun_congr_ae (grafoLevantado_fnL_ae G q),
    laplaciano_distribucional_eq_laplacianoLp _ (aproximacionLevantada_suave G q),
    hsol, residuoLevantado, distribucion_sub_lp]

private theorem laplacianoLevantado_eq (G q : CandidatoPoisson) (x : Plano) :
    laplacianoClásico (aproximacionLevantada G q) x =
      laplacianoClásico G.val x + laplacianoClásico (aproximacionPoisson q) x := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (aproximacionPoisson q) :=
    psiCuadrado_suave.mul q.property
  rw [laplacianoClásico_eq_mathlib _ (aproximacionLevantada_suave G q),
    laplacianoClásico_eq_mathlib _ G.property, laplacianoClásico_eq_mathlib _ hq]
  exact (G.property.of_le (by simp)).contDiffAt.laplacian_add
    (hq.of_le (by simp)).contDiffAt

/-- El cambio de medida del caso homogéneo se aplica al dato `f − ΔG`. -/
theorem perdidaResidualLevantada_eq (D : DensidadInferior) (G q : CandidatoPoisson)
    (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson) (lr : ℝ)
    (hInt : Integrable (fun x => (laplacianoClásico (aproximacionLevantada G q) x - f x) ^ 2)
      (medidaResidualPoisson D)) :
    ResiduoPonderadoIntegrable D (residuoLevantado G q (datoPoissonLp f hf)) ∧
    perdidaResidualMinima D lr (residuoLevantado G q (datoPoissonLp f hf)) =
      lr * ∫ x, (laplacianoClásico (aproximacionLevantada G q) x - f x) ^ 2
        ∂medidaResidualPoisson D := by
  let f0 : Plano → ℝ := fun x => f x - laplacianoClásico G.val x
  have hf0 : MemLp f0 2 volumenPoisson := hf.sub (laplacianoClásico_memLp G.val G.property)
  have heq : (fun x => laplacianoClásico (aproximacionPoisson q) x - f0 x) =
      (fun x => laplacianoClásico (aproximacionLevantada G q) x - f x) := by
    funext x
    rw [laplacianoLevantado_eq]
    dsimp [f0]
    ring
  have hLp : residuoAproximacion q.val q.property (datoPoissonLp f0 hf0) =
      residuoLevantado G q (datoPoissonLp f hf) := by
    apply Lp.ext
    exact (residuoPoisson_ae f0 hf0 q).trans
      ((EventuallyEq.of_eq heq).trans (residuoLevantado_ae G q f hf).symm)
  have hsq : (fun x => (laplacianoClásico (aproximacionPoisson q) x - f0 x) ^ 2) =
      (fun x => (laplacianoClásico (aproximacionLevantada G q) x - f x) ^ 2) :=
    congrArg (fun r : Plano → ℝ => fun x => r x ^ (2 : ℕ)) heq
  have h := perdidaResidualPoisson_eq D f0 hf0 q lr (by rw [hsq]; exact hInt)
  rw [hLp, hsq] at h
  exact h

theorem energia_de_perdidaLevantada (D : DensidadInferior) (G q : CandidatoPoisson)
    (lr : ℝ) (hlr : 0 < lr) (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (hu : u - grafoSuaveCuadrado G ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens (datoPoissonLp f hf) volume ⊤)
    (hInt : Integrable (fun x => (laplacianoClásico (aproximacionLevantada G q) x - f x) ^ 2)
      (medidaResidualPoisson D))
    (loss : ℝ) (hdom : lr * (∫ x, (laplacianoClásico (aproximacionLevantada G q) x - f x) ^ 2
      ∂medidaResidualPoisson D) ≤ loss) :
    ‖grafoLevantado G q - u‖ ≤ constanteEnergiaCuadrado /
      Real.sqrt (D.rho0 * lr) * Real.sqrt loss := by
  obtain ⟨hi, he⟩ := perdidaResidualLevantada_eq D G q f hf lr hInt
  let e : H01 (volume : Measure Plano) cuadrado :=
    ⟨grafoLevantado G q - u, errorLevantado_mem_H01 G q u hu⟩
  have hE := energia_cuadrado_uniforme e _ (laplaciano_errorLevantado G q u _ hsol)
  have hr := cota_norma_sin_superior D lr hlr _ hi loss (he.symm ▸ hdom)
  calc
    ‖grafoLevantado G q - u‖ ≤ constanteEnergiaCuadrado *
        ‖residuoLevantado G q (datoPoissonLp f hf)‖ := hE
    _ ≤ constanteEnergiaCuadrado * (Real.sqrt loss / Real.sqrt (D.rho0 * lr)) :=
      mul_le_mul_of_nonneg_left hr constanteEnergiaCuadrado_pos.le
    _ = _ := by ring

/-- Se usa la evaluación real del candidato y se suministra una cota de
seminorma de `G` en la frontera, que también controla a cada candidato. -/
def operadoresLevantados (G : CandidatoPoisson) (f : Plano → ℝ)
    (seminorma : CandidatoPoisson → ℝ) (SG : ℝ) :
    Operadores38 CandidatoPoisson Plano Plano where
  L q := laplacianoClásico (aproximacionLevantada G q)
  f := f
  B := aproximacionLevantada G
  g := G.val
  seminormaL := seminorma
  seminormaB := fun _ => SG

/-- (3.72) y (3.73) para Dirichlet no homogéneo exacto con levantamiento suave. -/
theorem teorema320_levantado_de_teorema38
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace CandidatoPoisson]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : DensidadInferior) [IsProbabilityMeasure (medidaResidualPoisson D)]
    (μb : Measure Plano) [IsProbabilityMeasure μb]
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (dr : DatosMasa38 (medidaResidualPoisson D) cuadrado 2 ε₀)
    (db : DatosMasa38 μb (frontier cuadrado) 1 ε₀)
    (sr : Muestreo38 P (medidaResidualPoisson D)) (sb : Muestreo38 P μb)
    (G : CandidatoPoisson) (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson)
    (seminorma : CandidatoPoisson → ℝ)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (hu : u - grafoSuaveCuadrado G ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens (datoPoissonLp f hf) volume ⊤)
    (mr mb : ℕ → ℕ) (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (hgr : ∀ᶠ n in atTop, n ≤ mr n) (hgb : ∀ᶠ n in atTop, n ≤ mb n)
    (lr lb α Sf SG K : ℝ) (hlr : 0 < lr) (hlb : 0 < lb)
    (hα : 0 < α) (hαone : α ≤ 1) (hK : 0 < K)
    (hrel : ∀ᶠ n in atTop, (mr n : ℝ) ≤ K * (mb n : ℝ) ^ 2)
    (Hm : ℕ → Set CandidatoPoisson) (hm g : ∀ n, Ω → Hm n)
    (hmeasHm : ∀ n, Measurable (fun ω => (hm n ω : CandidatoPoisson)))
    (hmeasG : ∀ n, Measurable (fun ω => (g n ω : CandidatoPoisson))) :
    let O := operadoresLevantados G f seminorma SG
    let base := fun n => O.base (medidaResidualPoisson D) μb (mr n) (mb n)
      (hmr n) (hmb n) dr.C db.C dr.c db.c lr lb α dr.C_pos dr.c_pos hlr hlb
    let Pn := problemaMuestral mr mb base sr.Z sb.Z
    (∀ n, CotasHolder (base n) (Hm n) cuadrado (frontier cuadrado) α Sf SG) →
    (∀ᵐ ω ∂P, ∃ R : ℝ, 0 ≤ R ∧ ∀ n,
      (Pn ω n).EsMinimizadorGlobal (Hm n) (hm n ω : CandidatoPoisson) ∧
      (Pn ω n).ComparadorExacto (Hm n) (g n ω : CandidatoPoisson) ∧
      (Pn ω n).regularidadTotal (g n ω : CandidatoPoisson) ≤ R) →
    ∀ᵐ ω ∂P,
      ((fun n => (Pn ω n).perdidaPoblacional (hm n ω : CandidatoPoisson)) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α / 2)))) ∧
      Tendsto (fun n => grafoLevantado G (hm n ω : CandidatoPoisson)) atTop (nhds u) ∧
      ((fun n => ‖grafoLevantado G (hm n ω : CandidatoPoisson) - u‖) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α / 4)))) := by
  intro O base Pn hHolder hvar
  have h38 := teorema38_dim2 P (medidaResidualPoisson D) μb cuadrado (frontier cuadrado)
    ε₀ hε₀ dr db sr sb O mr mb hmr hmb hgr hgb lr lb α Sf SG K
    hlr hlb hα hαone hK hrel Hm hm g hmeasHm hmeasG hHolder hvar
  let loss := fun n ω => (Pn ω n).perdidaPoblacional (hm n ω : CandidatoPoisson)
  have hRate : ∀ᵐ ω ∂P, (fun n => loss n ω) =O[atTop]
      (fun n => (mr n : ℝ) ^ (-(α / 2))) := h38.mono fun _ h => h.1
  have hsupportR := muestras_en_soporte_ae P (medidaResidualPoisson D) sr.Z
    cuadrado dr.concentrada sr.medible sr.ley
  have hsupportB := muestras_en_soporte_ae P μb sb.Z
    (frontier cuadrado) db.concentrada sb.medible sb.ley
  let KE := constanteEnergiaCuadrado / Real.sqrt (D.rho0 * lr)
  have hComp : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ‖grafoLevantado G (hm n ω : CandidatoPoisson) - u‖ ≤ KE * Real.sqrt (loss n ω) := by
    filter_upwards [hsupportR, hsupportB] with ω hr hb
    apply Eventually.of_forall
    intro n
    let q := (hm n ω : CandidatoPoisson)
    have hlap : Continuous (laplacianoClásico (aproximacionLevantada G q)) :=
      (laplacianoClásico_suave _ (aproximacionLevantada_suave G q)).continuous
    have hfmeas : AEStronglyMeasurable f (medidaResidualPoisson D) :=
      hf.aestronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
    have hres : AEStronglyMeasurable
        (fun x => (laplacianoClásico (aproximacionLevantada G q) x - f x) ^ 2)
        (medidaResidualPoisson D) :=
      (hlap.measurable.aestronglyMeasurable.sub hfmeas).pow 2
    have hbzero : (fun x => (O.B q x - O.g x) ^ 2) =ᵐ[μb] (fun _ => (0 : ℝ)) := by
      filter_upwards [mem_ae_iff.mpr db.concentrada] with x hx
      change (aproximacionLevantada G q x - G.val x) ^ 2 = 0
      simp [aproximacionLevantada_frontera G q x hx]
    have hInt := poblacionIntegrable_de_holder_acotado (Pn ω n) (Hm n)
      cuadrado (frontier cuadrado) dr.acotado db.acotado ⟨sr.Z 0 ω, hr 0⟩
      ⟨sb.Z 0 ω, hb 0⟩ dr.concentrada db.concentrada α Sf SG hα
      (hHolder n) q (hm n ω).2 hres
      (aestronglyMeasurable_const.congr hbzero.symm)
    have hdom : lr * (∫ x, (laplacianoClásico (aproximacionLevantada G q) x - f x) ^ 2
        ∂medidaResidualPoisson D) ≤ loss n ω := by
      change _ ≤ _ + lb * (∫ x, (O.B q x - O.g x) ^ 2 ∂μb)
      rw [integral_congr_ae hbzero, integral_zero, mul_zero, add_zero]
      exact le_rfl
    exact energia_de_perdidaLevantada D G q lr hlr f hf u hu hsol hInt.1 _ hdom
  simp only [errorLevantado_eq] at hComp
  have hEnergy := transferencia_energiaPoisson_ae P
    (fun n ω => (hm n ω : CandidatoPoisson)) loss (u - grafoSuaveCuadrado G) mr
    (tendsto_atTop_mono' atTop hgr tendsto_id) α KE hα
    (div_nonneg constanteEnergiaCuadrado_pos.le (Real.sqrt_nonneg _)) hComp hRate
  filter_upwards [hRate, hEnergy] with ω h1 h2
  refine ⟨h1, tendsto_iff_norm_sub_tendsto_zero.mpr ?_, ?_⟩
  · simpa only [errorLevantado_eq] using tendsto_iff_norm_sub_tendsto_zero.mp h2.1
  · simpa only [errorLevantado_eq] using h2.2

/-- En la estructura de Borel del grafo, la mensurabilidad del grafo
homogéneo se conserva al añadir el levantamiento fijo. -/
theorem measurable_grafoLevantado
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (H1Graph (volume : Measure Plano) cuadrado)]
    [BorelSpace (H1Graph (volume : Measure Plano) cuadrado)]
    (G : CandidatoPoisson) (q : Ω → CandidatoPoisson)
    (hq : Measurable (fun ω => grafoPoisson (q ω))) :
    Measurable (fun ω => grafoLevantado G (q ω)) := by
  have hc : Continuous (fun v : H1Graph (volume : Measure Plano) cuadrado =>
      grafoSuaveCuadrado G + v) := continuous_const.add continuous_id
  exact hc.measurable.comp hq

/-- El evento exacto se mide a través de la sucesión real de normas del error. -/
theorem prob_uno_convergenciaLevantada
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [MeasurableSpace (H1Graph (volume : Measure Plano) cuadrado)]
    [BorelSpace (H1Graph (volume : Measure Plano) cuadrado)]
    (G : CandidatoPoisson) (q : ℕ → Ω → CandidatoPoisson)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (hq : ∀ n, Measurable (fun ω => grafoPoisson (q n ω)))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => grafoLevantado G (q n ω)) atTop (nhds u)) :
    MeasurableSet {ω | Tendsto (fun n => grafoLevantado G (q n ω)) atTop (nhds u)} ∧
    P {ω | Tendsto (fun n => grafoLevantado G (q n ω)) atTop (nhds u)} = 1 := by
  have hc : Continuous (fun v : H1Graph (volume : Measure Plano) cuadrado => ‖v - u‖) :=
    (continuous_id.sub continuous_const).norm
  have hnorm (n : ℕ) : Measurable (fun ω => ‖grafoLevantado G (q n ω) - u‖) :=
    hc.measurable.comp (measurable_grafoLevantado G (q n) (hq n))
  have hm : MeasurableSet {ω | Tendsto (fun n => grafoLevantado G (q n ω)) atTop (nhds u)} := by
    have hevent : {ω | Tendsto (fun n => grafoLevantado G (q n ω)) atTop (nhds u)} =
        {ω | Tendsto (fun n => ‖grafoLevantado G (q n ω) - u‖) atTop (nhds (0 : ℝ))} :=
      Set.ext fun _ => tendsto_iff_norm_sub_tendsto_zero
    rw [hevent]
    exact measurableSet_tendsto_fun hnorm
      (show Measurable (fun _ : Ω => (0 : ℝ)) from measurable_const)
  exact ⟨hm, (prob_compl_eq_zero_iff hm).mp (mem_ae_iff.mp hae)⟩

#print axioms TesisPINN.teorema320_levantado_de_teorema38
#print axioms TesisPINN.grafoSuaveCuadrado_mem_W12
#print axioms TesisPINN.grafoLevantado_mem_W12
#print axioms TesisPINN.aproximacionLevantada_frontera
#print axioms TesisPINN.errorLevantado_mem_H01
#print axioms TesisPINN.laplaciano_errorLevantado
#print axioms TesisPINN.perdidaResidualLevantada_eq
#print axioms TesisPINN.energia_de_perdidaLevantada
#print axioms TesisPINN.measurable_grafoLevantado
#print axioms TesisPINN.prob_uno_convergenciaLevantada

end TesisPINN
