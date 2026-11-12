import TesisPINN.GeometriaMuestreoCuadrado
import TesisPINN.ConstantesLogCuadrado
import TesisPINN.ProblemaInterior
import TesisPINN.DirichletLevantamiento

/-! Proposición 3.15 y transferencia energética para candidatos con levantamiento. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Filter Asymptotics Topology EllipticPdes EllipticPdes.H1Graph
open scoped Distributions RealInnerProductSpace

def perdidaPoissonInterior (L f : Plano → ℝ) : ℝ := perdidaInterior medidaUniformeCuadrado L f

theorem perdidaPoissonInterior_eq (L f : Plano → ℝ) :
    perdidaPoissonInterior L f = (1 / 4) * ∫ x in cuadrado, (L x - f x) ^ 2 :=
  integral_medidaUniformeCuadrado _

def funcionalPoissonInterior {m : ℕ} (s : Fin m → Plano) (L f : Plano → ℝ) : ℝ :=
  funcionalInterior cuadrado (1 / 2) s L f (pesoLogInterior m)

theorem perdidaPoissonInterior_integrable (L f : Plano → ℝ)
    (α : ℝ) (hα : 0 < α)
    (hL : EsHolderInterior cuadrado α L)
    (hf : EsHolderInterior cuadrado α f) :
    Integrable (fun x => (L x - f x) ^ 2) medidaUniformeCuadrado :=
  residuoInterior_integrable medidaUniformeCuadrado cuadrado cuadrado_abierto.measurableSet
    cuadrado_acotado (soporte_no_vacio _ _ medidaUniformeCuadrado_concentrada)
    medidaUniformeCuadrado_concentrada L f α hα hL hf

private theorem cotaPoissonInterior {m : ℕ} (hm : 310 ≤ m)
    (s : Fin m → Plano) (hs : ∀ i, s i ∈ cuadrado)
    (hc : MuestrasCubren cuadrado s (radioLogCuadrado m))
    (L f : Plano → ℝ)
    (hL : EsHolderInterior cuadrado (1 / 2) L)
    (hf : EsHolderInterior cuadrado (1 / 2) f) :
    perdidaPoissonInterior L f ≤ factorLogInterior m * funcionalPoissonInterior s L f
      + 3 * radioLogCuadrado m * seminormaInterior cuadrado (1 / 2) f ^ 2 := by
  have hadm := radioLogCuadrado_admisible m hm
  have hr : 0 < radioLogCuadrado m := by
    simpa only [radioLogCuadrado_eq] using hadm.2.2.2.2.1
  have hr₀ : radioLogCuadrado m ≤ 1 := by
    simpa only [radioLogCuadrado_eq] using hadm.2.2.2.2.2
  have hfac := factorLogInterior_eq m (by omega)
  have ha : (3 * (Real.pi / 4) * (m : ℝ) * radioLogCuadrado m ^ (2 : ℝ)) *
      pesoLogInterior m = 3 * radioLogCuadrado m ^ (2 * (1 / 2 : ℝ)) := by
    rw [Real.rpow_two, hfac, producto_pesoLogInterior m (by omega)]
    norm_num
  have h := perdidaInterior_le_funcional medidaUniformeCuadrado cuadrado
    cuadrado_abierto.measurableSet medidaUniformeCuadrado_concentrada s (by omega) hs
    L f (1 / 2) (by norm_num) hL hf (radioLogCuadrado m) 1 (Real.pi / 4) 2
    (pesoLogInterior m) hr hr₀ (by positivity)
    hc masa_bola_uniforme_cuadrado (perdidaPoissonInterior_integrable L f _ (by norm_num) hL hf) ha
  rw [Real.rpow_two, hfac] at h
  norm_num at h
  exact h

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Se usan los mismos prefijos tanto en la ocupación como en el funcional. -/
def prefijoPoisson (P : Measure Ω) (Z : Muestreo38 P medidaUniformeCuadrado)
    (m : ℕ) (ω : Ω) : Fin m → Plano :=
  fun i => Z.Z i ω

/-- Las selecciones son funciones medibles del prefijo. Las desigualdades
variacionales y la admisibilidad se formulan en el mismo evento eventual. -/
structure Selecciones315 {H : Type*} [MeasurableSpace H]
    (P : Measure Ω) (Z : Muestreo38 P medidaUniformeCuadrado)
    (L : H → Plano → ℝ) (f : Plano → ℝ) (Hm : ℕ → Set H) where
  h : ∀ m, (Fin m → Plano) → H
  v : ∀ m, (Fin m → Plano) → H
  h_medible : ∀ m, Measurable (h m)
  v_medible : ∀ m, Measurable (v m)
  τ : ℕ → ℝ
  δ : ℕ → ℝ
  R : ℝ
  K : ℝ
  τ_nonneg : ∀ m, 0 ≤ τ m
  δ_nonneg : ∀ m, 0 ≤ δ m
  variacional : ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop,
    let s := prefijoPoisson P Z m ω
    h m s ∈ Hm m ∧ v m s ∈ Hm m ∧
    perdidaEmpiricaInterior s (L (v m s)) f ≤ τ m ∧
    seminormaInterior cuadrado (1 / 2) (L (v m s)) ^ 2 ≤ R ∧
    funcionalPoissonInterior s (L (h m s)) f ≤
      sInf ((fun w => funcionalPoissonInterior s (L w) f) '' Hm m) + δ m ∧
    τ m + δ m ≤ K * pesoLogInterior m

def escalaPerdida315 (m : ℕ) : ℝ := Real.sqrt (Real.log (m : ℝ) / m)

def escalaEnergia315 (m : ℕ) : ℝ := Real.sqrt (escalaPerdida315 m)

theorem radioLogCuadrado_eq_escala (m : ℕ) :
    radioLogCuadrado m = Real.sqrt 54 * escalaPerdida315 m := by
  rw [radioLogCuadrado, escalaPerdida315, mul_div_assoc, Real.sqrt_mul (by norm_num)]

/-- La geometría del cuadrado descarga las premisas de ocupación del Lema 3.13. -/
theorem ocupacion315 (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Muestreo38 P medidaUniformeCuadrado) :
    (∀ m : ℕ, 310 ≤ m → ∃ k : ℕ, ∃ cells : Fin k → Set Plano,
      MeasurableSet (todasCeldasOcupadas Z.Z m cells)ᶜ ∧
      P.real (todasCeldasOcupadas Z.Z m cells)ᶜ ≤ 1 / (3 * (m : ℝ) ^ 2 * Real.log m) ∧
      ∀ ω ∈ todasCeldasOcupadas Z.Z m cells,
        MuestrasCubren cuadrado (prefijoPoisson P Z m ω) (radioLogCuadrado m)) ∧
    (∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop,
      MuestrasCubren cuadrado (prefijoPoisson P Z m ω) (radioLogCuadrado m)) := by
  have hlog := lema313_cobertura_logaritmica P medidaUniformeCuadrado Z.Z Z.medible
    Z.indep Z.ley cuadrado (Real.sqrt 2) (1 / 9) 2 3 1 1
    (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    particiones_uniformes_cuadrado id (Eventually.of_forall fun _ => le_rfl)
  constructor
  · intro m hm
    obtain ⟨k, cells, hF, hbound, hcover⟩ :=
      hlog.1 m (radioLogCuadrado_admisible m hm)
    rw [falloLogCuadrado_eq m (by omega)] at hbound
    refine ⟨k, cells, hF, hbound, fun ω hω => ?_⟩
    change MuestrasCubren cuadrado (fun i : Fin m => Z.Z i ω) (radioLogCuadrado m)
    simpa only [radioLogCuadrado_eq] using hcover ω hω
  · filter_upwards [hlog.2] with ω hω
    filter_upwards [hω] with m hm
    change MuestrasCubren cuadrado (fun i : Fin m => Z.Z i ω) (radioLogCuadrado m)
    simpa only [id_eq, radioLogCuadrado_eq] using hm.2

/-- (3.65) y (3.66) para el laplaciano del candidato, representado por su
operador escalar. La prueba estadística solo usa su regularidad Hölder. -/
theorem proposicion315_perdida {H : Type*} [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Muestreo38 P medidaUniformeCuadrado)
    (L : H → Plano → ℝ) (f : Plano → ℝ) (Hm : ℕ → Set H)
    (hf : EsHolderInterior cuadrado (1 / 2) f)
    (hHolder : ∀ m w, w ∈ Hm m → EsHolderInterior cuadrado (1 / 2) (L w)) :
    (∀ m : ℕ, 310 ≤ m → ∃ E : Set Ω, MeasurableSet E ∧
      1 - 1 / (3 * (m : ℝ) ^ 2 * Real.log m) ≤ P.real E ∧
      ∀ ω ∈ E, ∀ w ∈ Hm m,
        perdidaPoissonInterior (L w) f ≤ factorLogInterior m *
          funcionalPoissonInterior (prefijoPoisson P Z m ω) (L w) f +
          3 * radioLogCuadrado m * seminormaInterior cuadrado (1 / 2) f ^ 2) ∧
    (∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop,
      MuestrasCubren cuadrado (prefijoPoisson P Z m ω) (radioLogCuadrado m)) ∧
    ∀ sel : Selecciones315 P Z L f Hm, ∀ᵐ ω ∂P,
      (fun m => perdidaPoissonInterior (L (sel.h m (prefijoPoisson P Z m ω))) f)
        =O[atTop] escalaPerdida315 := by
  obtain ⟨hOcc, hcov⟩ := ocupacion315 P Z
  let S := {ω | ∀ i, Z.Z i ω ∈ cuadrado}
  have hS : MeasurableSet S := by
    rw [show S = ⋂ i, Z.Z i ⁻¹' cuadrado by ext ω; simp [S]]
    exact MeasurableSet.iInter (fun i => cuadrado_abierto.measurableSet.preimage (Z.medible i))
  have hSae : ∀ᵐ ω ∂P, ω ∈ S :=
    muestras_en_soporte_ae P medidaUniformeCuadrado Z.Z cuadrado
      medidaUniformeCuadrado_concentrada Z.medible Z.ley
  have hSzero : P.real Sᶜ = 0 := by
    have hzero : P Sᶜ = 0 := mem_ae_iff.mp hSae
    rw [measureReal_def, hzero, ENNReal.toReal_zero]
  refine ⟨?_, hcov, ?_⟩
  · intro m hm
    obtain ⟨k, cells, hF, hbound, hcover⟩ := hOcc m hm
    let E := todasCeldasOcupadas Z.Z m cells ∩ S
    have hOcc : MeasurableSet (todasCeldasOcupadas Z.Z m cells) := by
      simpa only [compl_compl] using hF.compl
    have hE : MeasurableSet E := hOcc.inter hS
    have hprob : P.real Eᶜ ≤ 1 / (3 * (m : ℝ) ^ 2 * Real.log m) := by
      rw [show Eᶜ = (todasCeldasOcupadas Z.Z m cells)ᶜ ∪ Sᶜ from Set.compl_inter _ _]
      exact (measureReal_union_le _ _).trans (by rw [hSzero, add_zero]; exact hbound)
    rw [probReal_compl_eq_one_sub hE] at hprob
    refine ⟨E, hE, by linarith, ?_⟩
    intro ω hω w hw
    exact cotaPoissonInterior hm _ (fun i => hω.2 i) (hcover ω hω.1) _ _
      (hHolder m w hw) hf
  · intro sel
    filter_upwards [hcov, hSae, sel.variacional] with ω hcovω hSω hvar
    apply isBigO_de_cota_eventual _ _
      (3 * Real.sqrt 54 * (sel.R + sel.K + seminormaInterior cuadrado (1 / 2) f ^ 2))
    filter_upwards [hcovω, hvar, eventually_ge_atTop 310] with m hc hv hm
    dsimp at hv
    obtain ⟨hh, hvm, hτ, hR, hδ, htol⟩ := hv
    let s := prefijoPoisson P Z m ω
    have hadm := radioLogCuadrado_admisible m hm
    have hr : 0 < radioLogCuadrado m := by
      simpa only [radioLogCuadrado_eq] using hadm.2.2.2.2.1
    have hl : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hfac : 0 < factorLogInterior m := by unfold factorLogInterior; positivity
    have ha : 0 < pesoLogInterior m := by unfold pesoLogInterior; positivity
    have hj := (funcionalInterior_le_de_suboptimalidad cuadrado (1 / 2) s L f
      (pesoLogInterior m) ha (Hm m) (sel.h m s) (sel.v m s) hvm
      _ _ _ _ hδ hτ hR htol).1
    have hpop := cotaPoissonInterior hm s (fun i => hSω i) hc _ _
      (hHolder m _ hh) hf
    refine ⟨perdidaInterior_nonneg _ _ _, Real.sqrt_nonneg _, ?_⟩
    calc
      _ ≤ factorLogInterior m * (pesoLogInterior m * (sel.R + sel.K)) +
          3 * radioLogCuadrado m * seminormaInterior cuadrado (1 / 2) f ^ 2 :=
        hpop.trans (add_le_add_left (mul_le_mul_of_nonneg_left hj hfac.le) _)
      _ = _ := by
        rw [← mul_assoc (factorLogInterior m), producto_pesoLogInterior m (by omega),
          radioLogCuadrado_eq_escala]
        ring

theorem datoPoissonInterior_memLp (f : Plano → ℝ) (α : ℝ) (hα : 0 < α)
    (hf : EsHolderInterior cuadrado α f) :
    MemLp f 2 volumenPoisson := by
  have hcont := continuo_de_cota_holder cuadrado f _ α hα
    (seminormaInterior_cota cuadrado α f hf hα)
  have hmeas : AEStronglyMeasurable f volumenPoisson :=
    hcont.aestronglyMeasurable cuadrado_abierto.measurableSet
  apply (memLp_two_iff_integrable_sq hmeas).2
  have hzero : EsHolderInterior cuadrado α (0 : Plano → ℝ) := by
    refine ⟨0, le_rfl, fun x _ y _ => ?_⟩
    simp
  have hi := perdidaPoissonInterior_integrable 0 f α hα hzero hf
  have hs : Integrable (fun x => f x ^ 2) medidaUniformeCuadrado := by
    simpa only [Pi.zero_apply, zero_sub, neg_sq] using hi
  rw [medidaUniformeCuadrado, integrable_smul_measure
    (by positivity) ENNReal.ofReal_ne_top] at hs
  exact hs

theorem dato315_memLp (f : Plano → ℝ)
    (hf : EsHolderInterior cuadrado (1 / 2) f) :
    MemLp f 2 volumenPoisson :=
  datoPoissonInterior_memLp f (1 / 2) (by norm_num) hf

private def densidadUniforme315 : DensidadInferior where
  rho := fun _ => 1 / 4
  rho0 := 1 / 4
  rho0_pos := by norm_num
  measurable_rho := measurable_const
  lower := Eventually.of_forall fun _ => le_rfl

private theorem medida_densidadUniforme315 :
    medidaResidualPoisson densidadUniforme315 = medidaUniformeCuadrado :=
  medidaUniformeCuadrado_densidad.symm

theorem perdidaPoissonInterior_eq_norma_residuo
    (G q : CandidatoPoisson) (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson) :
    perdidaPoissonInterior (laplacianoClásico (aproximacionLevantada G q)) f =
      (1 / 4) * ‖residuoLevantado G q (datoPoissonLp f hf)‖ ^ 2 := by
  rw [perdidaPoissonInterior_eq]
  congr 1
  let r := residuoLevantado G q (datoPoissonLp f hf)
  have heq := (residuoLevantado_ae G q f hf).fun_comp (fun z : ℝ => z ^ 2)
  rw [← real_inner_self_eq_norm_sq r, MeasureTheory.L2.inner_def]
  refine (integral_congr_ae heq.symm).trans ?_
  congr 1
  funext x
  simp [r, Real.norm_eq_abs]

theorem energia315_por_perdida
    (G q : CandidatoPoisson) (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (hu : u - grafoSuaveCuadrado G ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens (datoPoissonLp f hf) volume ⊤) :
    ‖grafoLevantado G q - u‖ ≤ 2 * constanteEnergiaCuadrado *
      Real.sqrt (perdidaPoissonInterior (laplacianoClásico (aproximacionLevantada G q)) f) := by
  have hInt : Integrable (fun x =>
      (laplacianoClásico (aproximacionLevantada G q) x - f x) ^ 2)
      (medidaResidualPoisson densidadUniforme315) := by
    rw [medida_densidadUniforme315, medidaUniformeCuadrado]
    exact Integrable.smul_measure
      (((laplacianoClásico_memLp _ (aproximacionLevantada_suave G q)).sub hf).integrable_sq)
      ENNReal.ofReal_ne_top
  have h := energia_de_perdidaLevantada densidadUniforme315 G q 1 (by norm_num) f hf u hu
    hsol hInt (perdidaPoissonInterior (laplacianoClásico (aproximacionLevantada G q)) f)
    (by rw [medida_densidadUniforme315, one_mul]; rfl)
  change _ ≤ constanteEnergiaCuadrado / Real.sqrt ((1 / 4 : ℝ) * 1) * _ at h
  rw [mul_one, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)] at h
  convert h using 1
  ring

theorem escalaEnergia315_eq (m : ℕ) :
    escalaEnergia315 m = (Real.log (m : ℝ) / m) ^ (1 / 4 : ℝ) := by
  rw [escalaEnergia315, escalaPerdida315, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by positivity)]
  congr 1
  norm_num

theorem escalaEnergia315_tendsto : Tendsto escalaEnergia315 atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hn := h.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto escalaPerdida315 atTop (𝓝 0) := by
    change Tendsto (fun m : ℕ => Real.sqrt (Real.log (m : ℝ) / m)) atTop (𝓝 0)
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hn
  change Tendsto (fun m => Real.sqrt (escalaPerdida315 m)) atTop (𝓝 0)
  simpa only [Function.comp_def, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hr

theorem tasaEnergia_de_perdida {V : Type*} [NormedAddCommGroup V]
    (x : ℕ → V) (u : V) (E t : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hE : ∀ m, 0 ≤ E m) (hbound : ∀ m, ‖x m - u‖ ≤ A * Real.sqrt (E m))
    (ht : ∀ m, 0 ≤ t m) (htend : Tendsto (fun m => Real.sqrt (t m)) atTop (𝓝 0))
    (hRate : E =O[atTop] t) :
    Tendsto x atTop (𝓝 u) ∧ (fun m => ‖x m - u‖) =O[atTop] (fun m => Real.sqrt (t m)) := by
  obtain ⟨C, hC, hc⟩ := isBigO_iff'.mp hRate
  have hv : ∀ᶠ m in atTop, ‖x m - u‖ ≤ (A * Real.sqrt C) * Real.sqrt (t m) := by
    filter_upwards [hc] with m hm
    have he : E m ≤ C * t m := by
      rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hE m), abs_of_nonneg (ht m)] at hm
    calc
      _ ≤ A * Real.sqrt (E m) := hbound m
      _ ≤ A * Real.sqrt (C * t m) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) hA
      _ = _ := by rw [Real.sqrt_mul hC.le, mul_assoc]
  refine ⟨tendsto_iff_norm_sub_tendsto_zero.mpr ?_, isBigO_de_cota_eventual _ _ _
    (hv.mono fun _ hm => ⟨norm_nonneg _, Real.sqrt_nonneg _, hm⟩)⟩
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hv
  simpa using tendsto_const_nhds.mul htend

theorem laplacianoLevantado_holder (G q : CandidatoPoisson) (α : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1) :
    EsHolderInterior cuadrado α (laplacianoClásico (aproximacionLevantada G q)) := by
  let L := laplacianoClásico (aproximacionLevantada G q)
  have hs : ContDiff ℝ (⊤ : ℕ∞) L :=
    laplacianoClásico_suave _ (aproximacionLevantada_suave G q)
  obtain ⟨r, hr⟩ := cuadrado_acotado.subset_closedBall (0 : Plano)
  have hd := hs.continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Plano) r).exists_bound_of_continuousOn
    hd.continuousOn
  refine ⟨max M 0 * Metric.diam cuadrado ^ (1 - α), by positivity, ?_⟩
  intro x hx y hy
  have hLip := (convex_closedBall (0 : Plano) r).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hs.differentiable (by simp) x)
    (fun x hx => (hM x hx).trans (le_max_left _ 0)) (hr hy) (hr hx)
  rw [Real.norm_eq_abs, ← dist_eq_norm] at hLip
  have hdist := Metric.dist_le_diam_of_mem cuadrado_acotado hx hy
  have hroot : dist x y ≤ Metric.diam cuadrado ^ (1 - α) * dist x y ^ α := by
    calc
      dist x y = dist x y ^ (1 - α) * dist x y ^ α := by
        rcases eq_or_lt_of_le (dist_nonneg (x := x) (y := y)) with heq | hpos
        · rw [← heq, Real.zero_rpow hα.ne', mul_zero]
        · rw [← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow dist_nonneg hdist (sub_nonneg.mpr hα₁)) (Real.rpow_nonneg dist_nonneg _)
  rw [mul_assoc]
  exact hLip.trans (mul_le_mul_of_nonneg_left hroot (le_max_right _ _))

theorem laplacianoLevantado_holder315 (G q : CandidatoPoisson) :
    EsHolderInterior cuadrado (1 / 2) (laplacianoClásico (aproximacionLevantada G q)) :=
  laplacianoLevantado_holder G q (1 / 2) (by norm_num) (by norm_num)

/-- Poisson con dato de Dirichlet exacto impuesto por la clase `G + ψq`.
La tasa H¹ se añade a (3.66), que en el PDF es la tasa de pérdida. -/
theorem proposicion315_poisson
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Muestreo38 P medidaUniformeCuadrado)
    [MeasurableSpace CandidatoPoisson]
    (G : CandidatoPoisson) (f : Plano → ℝ) (Hm : ℕ → Set CandidatoPoisson)
    (hf : EsHolderInterior cuadrado (1 / 2) f)
    (sel : Selecciones315 P Z (fun q => laplacianoClásico (aproximacionLevantada G q)) f Hm)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (hu : u - grafoSuaveCuadrado G ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens (datoPoissonLp f (dato315_memLp f hf)) volume ⊤) :
    let L := fun q => laplacianoClásico (aproximacionLevantada G q)
    (∀ m : ℕ, 310 ≤ m → ∃ E : Set Ω, MeasurableSet E ∧
      1 - 1 / (3 * (m : ℝ) ^ 2 * Real.log m) ≤ P.real E ∧
      ∀ ω ∈ E, ∀ q ∈ Hm m,
        perdidaPoissonInterior (L q) f ≤ factorLogInterior m *
          funcionalPoissonInterior (prefijoPoisson P Z m ω) (L q) f +
          3 * radioLogCuadrado m * seminormaInterior cuadrado (1 / 2) f ^ 2) ∧
    (∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop,
      MuestrasCubren cuadrado (prefijoPoisson P Z m ω) (radioLogCuadrado m)) ∧
    ∀ᵐ ω ∂P,
      let q := fun m => sel.h m (prefijoPoisson P Z m ω)
      (fun m => perdidaPoissonInterior (L (q m)) f) =O[atTop] escalaPerdida315 ∧
      Tendsto (fun m => grafoLevantado G (q m)) atTop (𝓝 u) ∧
      (fun m => ‖grafoLevantado G (q m) - u‖) =O[atTop] escalaEnergia315 := by
  obtain ⟨hfinite, hcover, hrate⟩ := proposicion315_perdida P Z
    (fun q => laplacianoClásico (aproximacionLevantada G q)) f Hm hf
    (fun _ q _ => laplacianoLevantado_holder315 G q)
  refine ⟨hfinite, hcover, ?_⟩
  filter_upwards [hrate sel] with ω hω
  exact ⟨hω, tasaEnergia_de_perdida _ u _ escalaPerdida315 (2 * constanteEnergiaCuadrado)
    (mul_nonneg (by norm_num) constanteEnergiaCuadrado_pos.le)
    (fun _ => perdidaInterior_nonneg _ _ _)
    (fun _ => energia315_por_perdida G _ f (dato315_memLp f hf) u hu hsol)
    (fun _ => Real.sqrt_nonneg _) escalaEnergia315_tendsto hω⟩

#check proposicion315_perdida
#check proposicion315_poisson
#print axioms dato315_memLp
#print axioms perdidaPoissonInterior_eq_norma_residuo
#print axioms energia315_por_perdida
#print axioms laplacianoLevantado_holder315
#print axioms ocupacion315
#print axioms proposicion315_perdida
#print axioms proposicion315_poisson

end TesisPINN
