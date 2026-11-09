import TesisPINN.TransferenciaEnergetica
import EllipticPdes.Sobolev.GraphDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

/-!
# Pérdida poblacional y transferencia energética en el cuadrado

Este módulo formaliza únicamente la comparación determinista de la pérdida
poblacional con el residuo y su transferencia a la norma H¹. La pérdida puede
contener términos de frontera y otros términos no negativos, representados por
la hipótesis explícita de dominación. No se construye un minimizador aleatorio.
-/

noncomputable section

open MeasureTheory TopologicalSpace Topology Filter EllipticPdes EllipticPdes.H1Graph
open scoped RealInnerProductSpace Distributions

namespace TesisPINN

private abbrev medidaCuadrado : Measure Plano :=
  (volume : Measure Plano).restrict cuadrado

local instance : MeasurableSpace (H1Graph (volume : Measure Plano) cuadrado) :=
  borel _

local instance : BorelSpace (H1Graph (volume : Measure Plano) cuadrado) :=
  ⟨rfl⟩

/-- Densidad poblacional en el cuadrado. La cota superior, consecuencia de una
densidad continua en el cuadrado cerrado, se explicita para garantizar la
finitud de la integral ponderada cuando el residuo solo pertenece a L². -/
structure DensidadResidual where
  rho : Plano → ℝ
  rho0 : ℝ
  rhoMax : ℝ
  rho0_pos : 0 < rho0
  measurable_rho : Measurable rho
  lower : ∀ᵐ x ∂medidaCuadrado, rho0 ≤ rho x
  upper : ∀ᵐ x ∂medidaCuadrado, rho x ≤ rhoMax

private theorem residuo_sq_integrable (r : Lp ℝ 2 medidaCuadrado) :
    Integrable (fun x => (r x) ^ 2) medidaCuadrado :=
  (Lp.memLp r).integrable_sq

private theorem residuo_norm_sq_eq_integral (r : Lp ℝ 2 medidaCuadrado) :
    ‖r‖ ^ 2 = ∫ x, (r x) ^ 2 ∂medidaCuadrado := by
  rw [← real_inner_self_eq_norm_sq (r : Lp ℝ 2 medidaCuadrado),
    MeasureTheory.L2.inner_def]
  congr 1
  funext x
  simp [Real.norm_eq_abs]

/-- La cota superior esencial de la densidad hace integrable el término residual. -/
theorem integrable_residuo_ponderado (D : DensidadResidual)
    (r : Lp ℝ 2 medidaCuadrado) :
    Integrable (fun x => D.rho x * (r x) ^ 2) medidaCuadrado := by
  apply (residuo_sq_integrable r).bdd_mul D.measurable_rho.aestronglyMeasurable
  filter_upwards [D.lower, D.upper] with x hlo hhi
  rw [Real.norm_eq_abs, abs_of_nonneg (D.rho0_pos.le.trans hlo)]
  exact hhi

/-- El término residual de la pérdida poblacional, con medida de volumen
restringida a `U=(-1,1)²`. -/
def perdidaResidualPoblacional (D : DensidadResidual) (lambdaR : ℝ)
    (r : Lp ℝ 2 medidaCuadrado) : ℝ :=
  lambdaR * ∫ x, D.rho x * (r x) ^ 2 ∂medidaCuadrado

theorem perdidaResidualPoblacional_nonneg (D : DensidadResidual)
    (lambdaR : ℝ) (hlambda : 0 < lambdaR)
    (r : Lp ℝ 2 medidaCuadrado) :
    0 ≤ perdidaResidualPoblacional D lambdaR r := by
  unfold perdidaResidualPoblacional
  apply mul_nonneg hlambda.le
  apply integral_nonneg_of_ae
  filter_upwards [D.lower] with x hx
  exact mul_nonneg (D.rho0_pos.le.trans hx) (sq_nonneg _)

/-- La norma L² del residuo se controla por la densidad ponderada. -/
theorem cota_residuo_por_densidad (D : DensidadResidual)
    (r : Lp ℝ 2 medidaCuadrado) :
    D.rho0 * ‖r‖ ^ 2 ≤
      ∫ x, D.rho x * (r x) ^ 2 ∂medidaCuadrado := by
  rw [residuo_norm_sq_eq_integral, ← integral_const_mul]
  apply integral_mono_ae ((residuo_sq_integrable r).const_mul D.rho0)
    (integrable_residuo_ponderado D r)
  filter_upwards [D.lower] with x hx
  exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)

/-- Si la pérdida total domina el término residual, entonces controla la
norma cuadrática del residuo. Todos los términos integrales son finitos por
`integrable_residuo_ponderado`. -/
theorem cota_residuo_por_perdida (D : DensidadResidual)
    (lambdaR : ℝ) (hlambda : 0 < lambdaR)
    (r : Lp ℝ 2 medidaCuadrado) (loss : ℝ)
    (hdom : perdidaResidualPoblacional D lambdaR r ≤ loss) :
    ‖r‖ ^ 2 ≤ loss / (D.rho0 * lambdaR) := by
  have hc : 0 < D.rho0 * lambdaR := mul_pos D.rho0_pos hlambda
  apply (le_div_iff₀ hc).2
  have hbase := cota_residuo_por_densidad D r
  dsimp [perdidaResidualPoblacional] at hdom
  nlinarith [mul_le_mul_of_nonneg_left hbase hlambda.le]

/-- Forma lineal de la comparación, obtenida tomando raíces cuadradas de
cantidades no negativas. -/
theorem cota_norma_residuo_por_perdida (D : DensidadResidual)
    (lambdaR : ℝ) (hlambda : 0 < lambdaR)
    (r : Lp ℝ 2 medidaCuadrado) (loss : ℝ)
    (hdom : perdidaResidualPoblacional D lambdaR r ≤ loss) :
    ‖r‖ ≤ Real.sqrt loss / Real.sqrt (D.rho0 * lambdaR) := by
  have hc : 0 < D.rho0 * lambdaR := mul_pos D.rho0_pos hlambda
  have hsq := cota_residuo_por_perdida D lambdaR hlambda r loss hdom
  have hsq' := (le_div_iff₀ hc).1 hsq
  have hloss : 0 ≤ loss := by
    have hnorm : 0 ≤ ‖r‖ ^ 2 := sq_nonneg _
    nlinarith
  have hrootc : 0 < Real.sqrt (D.rho0 * lambdaR) := Real.sqrt_pos.2 hc
  apply (le_div_iff₀ hrootc).2
  have hs1 := Real.sq_sqrt hc.le
  have hs2 := Real.sq_sqrt hloss
  have hs3 : 0 ≤ Real.sqrt (D.rho0 * lambdaR) * ‖r‖ :=
    mul_nonneg hrootc.le (norm_nonneg _)
  have hs4 : 0 ≤ Real.sqrt loss := Real.sqrt_nonneg _
  have hs5 : (Real.sqrt (D.rho0 * lambdaR) * ‖r‖) ^ 2 ≤
      (Real.sqrt loss) ^ 2 := by
    nlinarith
  nlinarith

/-- Transferencia de la pérdida poblacional al error en H¹. La pérdida total
es una variable real cuya dominación del término residual se declara. -/
theorem estimacion_error_por_perdida
    (D : DensidadResidual) (lambdaR : ℝ) (hlambda : 0 < lambdaR)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 medidaCuadrado)
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤)
    (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (loss : ℝ)
    (hdom : perdidaResidualPoblacional D lambdaR
      (residuoAproximacion q hq f) ≤ loss) :
    ‖psiGraph q hq - u‖ ≤
      constanteEnergiaCuadrado / Real.sqrt (D.rho0 * lambdaR) * Real.sqrt loss := by
  have hr := cota_norma_residuo_por_perdida D lambdaR hlambda
    (residuoAproximacion q hq f) loss hdom
  calc
    ‖psiGraph q hq - u‖ ≤
        constanteEnergiaCuadrado * ‖residuoAproximacion q hq f‖ :=
      estimacion_uniforme_psi_solucion_exacta u f hu hsol q hq
    _ ≤ constanteEnergiaCuadrado *
        (Real.sqrt loss / Real.sqrt (D.rho0 * lambdaR)) :=
      mul_le_mul_of_nonneg_left hr constanteEnergiaCuadrado_pos.le
    _ = constanteEnergiaCuadrado / Real.sqrt (D.rho0 * lambdaR) *
        Real.sqrt loss := by ring

/-- Convergencia determinista de la pérdida asumida implica convergencia H¹. -/
theorem tendsto_psiGraph_de_perdida
    (D : DensidadResidual) (lambdaR : ℝ) (hlambda : 0 < lambdaR)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 medidaCuadrado)
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤)
    (q : ℕ → Plano → ℝ) (hq : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (q n))
    (loss : ℕ → ℝ)
    (hdom : ∀ n, perdidaResidualPoblacional D lambdaR
      (residuoAproximacion (q n) (hq n) f) ≤ loss n)
    (hloss : Tendsto loss atTop (𝓝 0)) :
    Tendsto (fun n => psiGraph (q n) (hq n)) atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => estimacion_error_por_perdida D lambdaR hlambda u f hu hsol
      (q n) (hq n) (loss n) (hdom n))
  have hsqrt : Tendsto (fun n => Real.sqrt (loss n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hloss
  simpa using (tendsto_const_nhds.mul hsqrt :
    Tendsto (fun n =>
      (constanteEnergiaCuadrado / Real.sqrt (D.rho0 * lambdaR)) *
        Real.sqrt (loss n)) atTop (𝓝
      ((constanteEnergiaCuadrado / Real.sqrt (D.rho0 * lambdaR)) * 0)))

/-- Tasa de pérdida en dimensión dos. `n` enumera aproximantes, mientras
`mr n` es el tamaño de la muestra residual y no se identifica con `n`. -/
theorem tasa_error_de_perdida_mr
    (D : DensidadResidual) (lambdaR : ℝ) (hlambda : 0 < lambdaR)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 medidaCuadrado)
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤)
    (q : ℕ → Plano → ℝ) (hq : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (q n))
    (loss : ℕ → ℝ) (mr : ℕ → ℕ) (alpha A : ℝ)
    (hA : 0 ≤ A) (hmr : ∀ n, 0 < mr n)
    (hdom : ∀ n, perdidaResidualPoblacional D lambdaR
      (residuoAproximacion (q n) (hq n) f) ≤ loss n)
    (hrate : ∀ n, loss n ≤ A * (mr n : ℝ) ^ (-alpha / 2)) :
    ∀ n, ‖psiGraph (q n) (hq n) - u‖ ≤
      (constanteEnergiaCuadrado / Real.sqrt (D.rho0 * lambdaR) *
        Real.sqrt A) * (mr n : ℝ) ^ (-alpha / 4) := by
  intro n
  have hmrpos : 0 ≤ (mr n : ℝ) := (Nat.cast_pos.mpr (hmr n)).le
  have hpownonneg : 0 ≤ (mr n : ℝ) ^ (-alpha / 2) :=
    Real.rpow_nonneg hmrpos _
  have hrootpow : Real.sqrt ((mr n : ℝ) ^ (-alpha / 2)) =
      (mr n : ℝ) ^ (-alpha / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hmrpos]
    congr 1
    ring
  calc
    ‖psiGraph (q n) (hq n) - u‖ ≤
        constanteEnergiaCuadrado / Real.sqrt (D.rho0 * lambdaR) *
          Real.sqrt (loss n) :=
      estimacion_error_por_perdida D lambdaR hlambda u f hu hsol
        (q n) (hq n) (loss n) (hdom n)
    _ ≤ constanteEnergiaCuadrado / Real.sqrt (D.rho0 * lambdaR) *
          Real.sqrt (A * (mr n : ℝ) ^ (-alpha / 2)) := by
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hrate n))
      exact div_nonneg constanteEnergiaCuadrado_pos.le (Real.sqrt_nonneg _)
    _ = (constanteEnergiaCuadrado / Real.sqrt (D.rho0 * lambdaR) *
          Real.sqrt A) * (mr n : ℝ) ^ (-alpha / 4) := by
      rw [Real.sqrt_mul hA, hrootpow]
      ring

/-- La implicación casi segura es una aplicación trayectoria por trayectoria
de la transferencia determinista. La convergencia de la pérdida y la
dominación residual son premisas sobre el espacio probabilístico. -/
theorem tendsto_psiGraph_de_perdida_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (D : DensidadResidual) (lambdaR : ℝ) (hlambda : 0 < lambdaR)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 medidaCuadrado)
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤)
    (q : Omega → ℕ → Plano → ℝ)
    (hq : ∀ omega n, ContDiff ℝ (⊤ : ℕ∞) (q omega n))
    (loss : Omega → ℕ → ℝ)
    (hdom : ∀ᵐ omega ∂P, ∀ n, perdidaResidualPoblacional D lambdaR
      (residuoAproximacion (q omega n) (hq omega n) f) ≤ loss omega n)
    (hloss : ∀ᵐ omega ∂P, Tendsto (loss omega) atTop (𝓝 0)) :
    ∀ᵐ omega ∂P,
      Tendsto (fun n => psiGraph (q omega n) (hq omega n)) atTop (𝓝 u) := by
  filter_upwards [hdom, hloss] with omega hdomOmega hlossOmega
  exact tendsto_psiGraph_de_perdida D lambdaR hlambda u f hu hsol
    (q omega) (hq omega) (loss omega) hdomOmega hlossOmega

/-- Si la pérdida converge con probabilidad uno, el error converge con
probabilidad uno. Se exigen explícitamente las dos mensurabilidades de las
trayectorias; no se deducen de la mera existencia de minimizadores. -/
theorem prob_uno_tendsto_psiGraph_de_perdida
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (D : DensidadResidual) (lambdaR : ℝ) (hlambda : 0 < lambdaR)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 medidaCuadrado)
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤)
    (q : Omega → ℕ → Plano → ℝ)
    (hq : ∀ omega n, ContDiff ℝ (⊤ : ℕ∞) (q omega n))
    (loss : Omega → ℕ → ℝ)
    (hLossMeas : ∀ n, Measurable (fun omega => loss omega n))
    (hApproxMeas : ∀ n, Measurable
      (fun omega => psiGraph (q omega n) (hq omega n)))
    (hdom : ∀ᵐ omega ∂P, ∀ n, perdidaResidualPoblacional D lambdaR
      (residuoAproximacion (q omega n) (hq omega n) f) ≤ loss omega n)
    (hlossProb : P {omega | Tendsto (loss omega) atTop (𝓝 0)} = 1) :
    P {omega | Tendsto (fun n => psiGraph (q omega n) (hq omega n))
      atTop (𝓝 u)} = 1 := by
  have hLossSet : MeasurableSet
      {omega | Tendsto (loss omega) atTop (𝓝 0)} := by
    exact measurableSet_tendsto_fun hLossMeas measurable_const
  have hLossAe : ∀ᵐ omega ∂P, Tendsto (loss omega) atTop (𝓝 0) :=
    (mem_ae_iff_prob_eq_one hLossSet).2 hlossProb
  have hErrorSet : MeasurableSet
      {omega | Tendsto (fun n => psiGraph (q omega n) (hq omega n))
        atTop (𝓝 u)} := by
    exact measurableSet_tendsto_fun hApproxMeas measurable_const
  apply (mem_ae_iff_prob_eq_one hErrorSet).1
  exact tendsto_psiGraph_de_perdida_ae P D lambdaR hlambda u f hu hsol
    q hq loss hdom hLossAe

#print axioms TesisPINN.integrable_residuo_ponderado
#print axioms TesisPINN.perdidaResidualPoblacional_nonneg
#print axioms TesisPINN.cota_residuo_por_densidad
#print axioms TesisPINN.cota_residuo_por_perdida
#print axioms TesisPINN.cota_norma_residuo_por_perdida
#print axioms TesisPINN.estimacion_error_por_perdida
#print axioms TesisPINN.tendsto_psiGraph_de_perdida
#print axioms TesisPINN.tasa_error_de_perdida_mr
#print axioms TesisPINN.tendsto_psiGraph_de_perdida_ae
#print axioms TesisPINN.prob_uno_tendsto_psiGraph_de_perdida

end TesisPINN

