import TesisPINN.Teorema38
import TesisPINN.DensidadResidualMinima

/-! Puente entre la pérdida del Teorema 3.8 y la energía de Poisson
con Dirichlet homogéneo exacto en el cuadrado. -/

noncomputable section

open MeasureTheory Filter TopologicalSpace EllipticPdes EllipticPdes.H1Graph Asymptotics
open scoped Distributions

namespace TesisPINN

abbrev volumenPoisson : Measure Plano := (volume : Measure Plano).restrict cuadrado

def CandidatoPoisson := {q : Plano → ℝ // ContDiff ℝ (⊤ : ℕ∞) q}

def aproximacionPoisson (q : CandidatoPoisson) (x : Plano) : ℝ :=
  psiCuadrado x * q.val x

def grafoPoisson (q : CandidatoPoisson) : H1Graph (volume : Measure Plano) cuadrado :=
  psiGraph q.val q.property

theorem psiCuadrado_cero_frontera (x : Plano) (hx : x ∈ frontier cuadrado) :
    psiCuadrado x = 0 := by
  have hcoord (i : Fin 2) : x i ∈ Set.Icc (-1 : ℝ) 1 := by
    have hc : IsClosed ((fun y : Plano => y i) ⁻¹' Set.Icc (-1 : ℝ) 1) :=
      isClosed_Icc.preimage (by fun_prop)
    exact closure_minimal (fun y hy => ⟨(hy i).1.le, (hy i).2.le⟩) hc
      (frontier_subset_closure hx)
  have hn : x ∉ cuadrado := by
    simpa only [cuadrado_abierto.interior_eq] using hx.2
  change ¬ (∀ i : Fin 2, x i ∈ Set.Ioo (-1 : ℝ) 1) at hn
  obtain ⟨i, hi⟩ := not_forall.mp hn
  have he : (x i) ^ 2 = 1 := by
    by_cases hleft : -1 < x i
    · have hright : ¬ x i < 1 := fun h => hi ⟨hleft, h⟩
      rw [le_antisymm (hcoord i).2 (le_of_not_gt hright)]
      norm_num
    · rw [le_antisymm (le_of_not_gt hleft) (hcoord i).1]
      norm_num
  fin_cases i
  · exact psiCuadrado_cero_coord0 x he
  · exact psiCuadrado_cero_coord1 x he

/-- `B` evalúa la función ambiente, y su seminorma sobre la frontera es cero. -/
def operadoresPoisson (f : Plano → ℝ) (seminorma : CandidatoPoisson → ℝ) :
    Operadores38 CandidatoPoisson Plano Plano where
  L q := laplacianoClásico (aproximacionPoisson q)
  f := f
  B := aproximacionPoisson
  g := fun _ => 0
  seminormaL := seminorma
  seminormaB := fun _ => 0

theorem operadorPoisson_frontera (f : Plano → ℝ) (seminorma : CandidatoPoisson → ℝ)
    (q : CandidatoPoisson) (x : Plano) (hx : x ∈ frontier cuadrado) :
    (operadoresPoisson f seminorma).B q x = (operadoresPoisson f seminorma).g x := by
  change psiCuadrado x * q.val x = 0
  rw [psiCuadrado_cero_frontera x hx, zero_mul]

def datoPoissonLp (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson) :
    Lp ℝ 2 volumenPoisson := hf.toLp f

theorem datoPoissonLp_ae (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson) :
    ⇑(datoPoissonLp f hf) =ᵐ[volumenPoisson] f := hf.coeFn_toLp

def medidaResidualPoisson (D : DensidadInferior) : Measure Plano :=
  volumenPoisson.withDensity (fun x => ENNReal.ofReal (D.rho x))

theorem residuoPoisson_ae (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson)
    (q : CandidatoPoisson) :
    ⇑(residuoAproximacion q.val q.property (datoPoissonLp f hf)) =ᵐ[volumenPoisson]
      (fun x => laplacianoClásico (aproximacionPoisson q) x - f x) := by
  unfold residuoAproximacion
  exact (Lp.coeFn_sub _ _).trans
    ((laplacianoLp_ae _ (psiCuadrado_suave.mul q.property)).sub (datoPoissonLp_ae f hf))

/-- Cambio de medida e identificación del residuo puntual con el de la energía. -/
theorem perdidaResidualPoisson_eq (D : DensidadInferior)
    (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson) (q : CandidatoPoisson)
    (lr : ℝ) (hInt : Integrable
      (fun x => (laplacianoClásico (aproximacionPoisson q) x - f x) ^ 2)
      (medidaResidualPoisson D)) :
    ResiduoPonderadoIntegrable D (residuoAproximacion q.val q.property (datoPoissonLp f hf)) ∧
    perdidaResidualMinima D lr (residuoAproximacion q.val q.property (datoPoissonLp f hf)) =
      lr * ∫ x, (laplacianoClásico (aproximacionPoisson q) x - f x) ^ 2
        ∂medidaResidualPoisson D := by
  have hd : Measurable (fun x => ENNReal.ofReal (D.rho x)) :=
    D.measurable_rho.ennreal_ofReal
  have hfin : ∀ᵐ x ∂volumenPoisson, ENNReal.ofReal (D.rho x) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have heq :
      (fun x => (ENNReal.ofReal (D.rho x)).toReal •
        (laplacianoClásico (aproximacionPoisson q) x - f x) ^ 2) =ᵐ[volumenPoisson]
      (fun x => D.rho x * (residuoAproximacion q.val q.property (datoPoissonLp f hf) x) ^ 2) := by
    filter_upwards [D.lower, residuoPoisson_ae f hf q] with x hx hr
    simp [ENNReal.toReal_ofReal (D.rho0_pos.le.trans hx), hr, smul_eq_mul]
  refine ⟨((integrable_withDensity_iff_integrable_smul' hd hfin).mp hInt).congr heq, ?_⟩
  rw [perdidaResidualMinima, medidaResidualPoisson,
    integral_withDensity_eq_integral_toReal_smul hd hfin, integral_congr_ae heq]

theorem energia_de_perdidaPoisson (D : DensidadInferior) (lr : ℝ) (hlr : 0 < lr)
    (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens (datoPoissonLp f hf) volume ⊤)
    (q : CandidatoPoisson)
    (hInt : Integrable (fun x => (laplacianoClásico (aproximacionPoisson q) x - f x) ^ 2)
      (medidaResidualPoisson D))
    (loss : ℝ)
    (hdom : lr * (∫ x, (laplacianoClásico (aproximacionPoisson q) x - f x) ^ 2
      ∂medidaResidualPoisson D) ≤ loss) :
    ‖grafoPoisson q - u‖ ≤ constanteEnergiaCuadrado /
      Real.sqrt (D.rho0 * lr) * Real.sqrt loss := by
  obtain ⟨hi, he⟩ := perdidaResidualPoisson_eq D f hf q lr hInt
  exact estimacion_error_sin_superior D lr hlr u (datoPoissonLp f hf) hu hsol
    q.val q.property hi loss (he.symm ▸ hdom)

/-- La raíz de la pérdida divide por dos el exponente de la tasa. -/
theorem transferencia_energiaPoisson_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ℕ → Ω → CandidatoPoisson) (loss : ℕ → Ω → ℝ)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (mr : ℕ → ℕ) (hmr : Tendsto mr atTop atTop)
    (α K : ℝ) (hα : 0 < α) (hK : 0 ≤ K)
    (hComp : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ‖grafoPoisson (q n ω) - u‖ ≤ K * Real.sqrt (loss n ω))
    (hRate : ∀ᵐ ω ∂P, (fun n => loss n ω) =O[atTop]
      (fun n => (mr n : ℝ) ^ (-(α / 2)))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => grafoPoisson (q n ω)) atTop (nhds u) ∧
      (fun n => ‖grafoPoisson (q n ω) - u‖) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α / 4))) := by
  filter_upwards [hComp, hRate] with ω hcomp hrate
  obtain ⟨C, hC, hc⟩ := isBigO_iff'.mp hrate
  have hbound : ∀ᶠ n in atTop,
      ‖grafoPoisson (q n ω) - u‖ ≤ (K * Real.sqrt C) * (mr n : ℝ) ^ (-(α / 4)) := by
    filter_upwards [hcomp, hc] with n hn hcn
    have hnn : 0 ≤ (mr n : ℝ) ^ (-(α / 2)) := by positivity
    have hupper := (le_abs_self (loss n ω)).trans
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using hcn)
    have hroot : Real.sqrt ((mr n : ℝ) ^ (-(α / 2))) =
        (mr n : ℝ) ^ (-(α / 4)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ (mr n : ℝ))]
      congr 1
      ring
    calc
      _ ≤ K * Real.sqrt (loss n ω) := hn
      _ ≤ K * Real.sqrt (C * (mr n : ℝ) ^ (-(α / 2))) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hupper) hK
      _ = _ := by rw [Real.sqrt_mul hC.le, hroot]; ring
  have ht : Tendsto (fun n => (mr n : ℝ) ^ (-(α / 4))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < α / 4)).comp
      (tendsto_natCast_atTop_atTop.comp hmr)
  refine ⟨tendsto_iff_norm_sub_tendsto_zero.mpr ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [mul_zero] using ht.const_mul (K * Real.sqrt C))
      (Eventually.of_forall fun _ => norm_nonneg _) hbound
  · exact isBigO_de_cota_eventual _ _ (K * Real.sqrt C)
      (hbound.mono fun _ hn => ⟨norm_nonneg _, by positivity, hn⟩)

/-- Instancia homogénea exacta. El operador de frontera evalúa `ψq`.
La tasa poblacional se obtiene de `teorema38_dim2`. -/
theorem teorema320_poisson_de_teorema38
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace CandidatoPoisson]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : DensidadInferior) [IsProbabilityMeasure (medidaResidualPoisson D)]
    (μb : Measure Plano) [IsProbabilityMeasure μb]
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (dr : DatosMasa38 (medidaResidualPoisson D) cuadrado 2 ε₀)
    (db : DatosMasa38 μb (frontier cuadrado) 1 ε₀)
    (sr : Muestreo38 P (medidaResidualPoisson D)) (sb : Muestreo38 P μb)
    (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson)
    (seminorma : CandidatoPoisson → ℝ)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens (datoPoissonLp f hf) volume ⊤)
    (mr mb : ℕ → ℕ) (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (hgr : ∀ᶠ n in atTop, n ≤ mr n) (hgb : ∀ᶠ n in atTop, n ≤ mb n)
    (lr lb α Sf K : ℝ) (hlr : 0 < lr) (hlb : 0 < lb)
    (hα : 0 < α) (hαone : α ≤ 1) (hK : 0 < K)
    (hrel : ∀ᶠ n in atTop, (mr n : ℝ) ≤ K * (mb n : ℝ) ^ 2)
    (Hm : ℕ → Set CandidatoPoisson) (hm g : ∀ n, Ω → Hm n)
    (hmeasHm : ∀ n, Measurable (fun ω => (hm n ω : CandidatoPoisson)))
    (hmeasG : ∀ n, Measurable (fun ω => (g n ω : CandidatoPoisson))) :
    let O := operadoresPoisson f seminorma
    let base := fun n => O.base (medidaResidualPoisson D) μb (mr n) (mb n)
      (hmr n) (hmb n) dr.C db.C dr.c db.c lr lb α dr.C_pos dr.c_pos hlr hlb
    let Pn := problemaMuestral mr mb base sr.Z sb.Z
    (∀ n, CotasHolder (base n) (Hm n) cuadrado (frontier cuadrado) α Sf 0) →
    (∀ᵐ ω ∂P, ∃ R : ℝ, 0 ≤ R ∧ ∀ n,
      (Pn ω n).EsMinimizadorGlobal (Hm n) (hm n ω : CandidatoPoisson) ∧
      (Pn ω n).ComparadorExacto (Hm n) (g n ω : CandidatoPoisson) ∧
      (Pn ω n).regularidadTotal (g n ω : CandidatoPoisson) ≤ R) →
    ∀ᵐ ω ∂P,
      ((fun n => (Pn ω n).perdidaPoblacional (hm n ω : CandidatoPoisson)) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α / 2)))) ∧
      Tendsto (fun n => grafoPoisson (hm n ω : CandidatoPoisson)) atTop (nhds u) ∧
      ((fun n => ‖grafoPoisson (hm n ω : CandidatoPoisson) - u‖) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α / 4)))) := by
  intro O base Pn hHolder hvar
  have h38 := teorema38_dim2 P (medidaResidualPoisson D) μb cuadrado (frontier cuadrado)
    ε₀ hε₀ dr db sr sb O mr mb hmr hmb hgr hgb lr lb α Sf 0 K
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
      ‖grafoPoisson (hm n ω : CandidatoPoisson) - u‖ ≤ KE * Real.sqrt (loss n ω) := by
    filter_upwards [hsupportR, hsupportB] with ω hr hb
    apply Eventually.of_forall
    intro n
    let q := (hm n ω : CandidatoPoisson)
    have hlap : Continuous (laplacianoClásico (aproximacionPoisson q)) :=
      (laplacianoClásico_suave _ (psiCuadrado_suave.mul q.property)).continuous
    have hfmeas : AEStronglyMeasurable f (medidaResidualPoisson D) :=
      hf.aestronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
    have hres : AEStronglyMeasurable
        (fun x => (laplacianoClásico (aproximacionPoisson q) x - f x) ^ 2)
        (medidaResidualPoisson D) :=
      (hlap.measurable.aestronglyMeasurable.sub hfmeas).pow 2
    have hbzero : (fun x => (O.B q x - O.g x) ^ 2) =ᵐ[μb] (fun _ => (0 : ℝ)) := by
      filter_upwards [mem_ae_iff.mpr db.concentrada] with x hx
      change ((operadoresPoisson f seminorma).B q x -
        (operadoresPoisson f seminorma).g x) ^ 2 = 0
      simp [operadorPoisson_frontera f seminorma q x hx]
    have hInt := poblacionIntegrable_de_holder_acotado (Pn ω n) (Hm n)
      cuadrado (frontier cuadrado) dr.acotado db.acotado ⟨sr.Z 0 ω, hr 0⟩
      ⟨sb.Z 0 ω, hb 0⟩ dr.concentrada db.concentrada α Sf 0 hα
      (hHolder n) q (hm n ω).2 hres
      (aestronglyMeasurable_const.congr hbzero.symm)
    have hdom : lr * (∫ x, (laplacianoClásico (aproximacionPoisson q) x - f x) ^ 2
        ∂medidaResidualPoisson D) ≤ loss n ω := by
      change _ ≤ _ + lb * (∫ x, (O.B q x - O.g x) ^ 2 ∂μb)
      rw [integral_congr_ae hbzero, integral_zero, mul_zero, add_zero]
    exact energia_de_perdidaPoisson D lr hlr f hf u hu hsol q hInt.1 _ hdom
  have hEnergy := transferencia_energiaPoisson_ae P
    (fun n ω => (hm n ω : CandidatoPoisson)) loss u mr
    (tendsto_atTop_mono' atTop hgr tendsto_id) α KE hα
    (div_nonneg constanteEnergiaCuadrado_pos.le (Real.sqrt_nonneg _)) hComp hRate
  filter_upwards [hRate, hEnergy] with ω h1 h2
  exact ⟨h1, h2⟩

#print axioms TesisPINN.operadorPoisson_frontera
#print axioms TesisPINN.datoPoissonLp_ae
#print axioms TesisPINN.perdidaResidualPoisson_eq
#print axioms TesisPINN.energia_de_perdidaPoisson
#print axioms TesisPINN.transferencia_energiaPoisson_ae
#print axioms TesisPINN.teorema320_poisson_de_teorema38

end TesisPINN
