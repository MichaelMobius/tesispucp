import TesisPINN.PerdidaPoblacional

/-!
# Comparación ponderada sin cota superior de densidad

La Hipótesis 3.2 proporciona una cota inferior esencial. Para una pérdida real
finita, se hace visible la integrabilidad del residuo ponderado particular.
No se impone `rhoMax`; el caso de integral infinita puede tratarse con
`ENNReal` en una etapa posterior.
-/

noncomputable section

open MeasureTheory TopologicalSpace Topology Filter EllipticPdes EllipticPdes.H1Graph
open scoped RealInnerProductSpace Distributions

namespace TesisPINN

private abbrev μU : Measure Plano := (volume : Measure Plano).restrict cuadrado

structure DensidadInferior where
  rho : Plano → ℝ
  rho0 : ℝ
  rho0_pos : 0 < rho0
  measurable_rho : Measurable rho
  lower : ∀ᵐ x ∂μU, rho0 ≤ rho x

/-- La finitud de la pérdida residual de un candidato es una condición sobre
ese candidato, sin restringir globalmente la densidad por arriba. -/
def ResiduoPonderadoIntegrable (D : DensidadInferior) (r : Lp ℝ 2 μU) : Prop :=
  Integrable (fun x => D.rho x * (r x) ^ 2) μU

def perdidaResidualMinima (D : DensidadInferior) (lambdaR : ℝ)
    (r : Lp ℝ 2 μU) : ℝ :=
  lambdaR * ∫ x, D.rho x * (r x) ^ 2 ∂μU

private theorem norma_sq_integral (r : Lp ℝ 2 μU) :
    ‖r‖ ^ 2 = ∫ x, (r x) ^ 2 ∂μU := by
  rw [← real_inner_self_eq_norm_sq (r : Lp ℝ 2 μU), MeasureTheory.L2.inner_def]
  congr 1
  funext x
  simp [Real.norm_eq_abs]

/-- Comparación de normas que usa solo la cota inferior y la finitud del
término que realmente aparece en la pérdida. -/
theorem cota_densidad_sin_superior (D : DensidadInferior)
    (r : Lp ℝ 2 μU) (hInt : ResiduoPonderadoIntegrable D r) :
    D.rho0 * ‖r‖ ^ 2 ≤ ∫ x, D.rho x * (r x) ^ 2 ∂μU := by
  rw [norma_sq_integral, ← integral_const_mul]
  apply integral_mono_ae ((Lp.memLp r).integrable_sq.const_mul D.rho0) hInt
  filter_upwards [D.lower] with x hx
  exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)

theorem cota_perdida_sin_superior (D : DensidadInferior)
    (lambdaR : ℝ) (hlambda : 0 < lambdaR)
    (r : Lp ℝ 2 μU) (hInt : ResiduoPonderadoIntegrable D r)
    (loss : ℝ) (hdom : perdidaResidualMinima D lambdaR r ≤ loss) :
    ‖r‖ ^ 2 ≤ loss / (D.rho0 * lambdaR) := by
  have hc : 0 < D.rho0 * lambdaR := mul_pos D.rho0_pos hlambda
  apply (le_div_iff₀ hc).2
  have hbase := cota_densidad_sin_superior D r hInt
  dsimp [perdidaResidualMinima] at hdom
  nlinarith [mul_le_mul_of_nonneg_left hbase hlambda.le]

theorem cota_norma_sin_superior (D : DensidadInferior)
    (lambdaR : ℝ) (hlambda : 0 < lambdaR)
    (r : Lp ℝ 2 μU) (hInt : ResiduoPonderadoIntegrable D r)
    (loss : ℝ) (hdom : perdidaResidualMinima D lambdaR r ≤ loss) :
    ‖r‖ ≤ Real.sqrt loss / Real.sqrt (D.rho0 * lambdaR) := by
  have hc : 0 < D.rho0 * lambdaR := mul_pos D.rho0_pos hlambda
  have hsq := cota_perdida_sin_superior D lambdaR hlambda r hInt loss hdom
  have hsq' := (le_div_iff₀ hc).1 hsq
  have hloss : 0 ≤ loss := by
    nlinarith [sq_nonneg ‖r‖]
  have hrootc : 0 < Real.sqrt (D.rho0 * lambdaR) := Real.sqrt_pos.2 hc
  apply (le_div_iff₀ hrootc).2
  have hs1 := Real.sq_sqrt hc.le
  have hs2 := Real.sq_sqrt hloss
  have hs3 : 0 ≤ Real.sqrt (D.rho0 * lambdaR) * ‖r‖ :=
    mul_nonneg hrootc.le (norm_nonneg _)
  have hs4 : 0 ≤ Real.sqrt loss := Real.sqrt_nonneg _
  have hs5 : (Real.sqrt (D.rho0 * lambdaR) * ‖r‖) ^ 2 ≤
      (Real.sqrt loss) ^ 2 := by nlinarith
  nlinarith

/-- Versión de la estimación energética que no usa `rhoMax`. -/
theorem estimacion_error_sin_superior
    (D : DensidadInferior) (lambdaR : ℝ) (hlambda : 0 < lambdaR)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 μU)
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤)
    (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hInt : ResiduoPonderadoIntegrable D (residuoAproximacion q hq f))
    (loss : ℝ)
    (hdom : perdidaResidualMinima D lambdaR
      (residuoAproximacion q hq f) ≤ loss) :
    ‖psiGraph q hq - u‖ ≤
      constanteEnergiaCuadrado / Real.sqrt (D.rho0 * lambdaR) * Real.sqrt loss := by
  have hr := cota_norma_sin_superior D lambdaR hlambda
    (residuoAproximacion q hq f) hInt loss hdom
  calc
    ‖psiGraph q hq - u‖ ≤
        constanteEnergiaCuadrado * ‖residuoAproximacion q hq f‖ :=
      estimacion_uniforme_psi_solucion_exacta u f hu hsol q hq
    _ ≤ constanteEnergiaCuadrado *
        (Real.sqrt loss / Real.sqrt (D.rho0 * lambdaR)) :=
      mul_le_mul_of_nonneg_left hr constanteEnergiaCuadrado_pos.le
    _ = constanteEnergiaCuadrado / Real.sqrt (D.rho0 * lambdaR) *
        Real.sqrt loss := by ring

/-- La estructura acotada de la etapa anterior es un caso particular; sus
resultados anteriores permanecen intactos. -/
def DensidadResidual.toInferior (D : DensidadResidual) : DensidadInferior where
  rho := D.rho
  rho0 := D.rho0
  rho0_pos := D.rho0_pos
  measurable_rho := D.measurable_rho
  lower := D.lower

theorem acotada_integrable (D : DensidadResidual) (r : Lp ℝ 2 μU) :
    ResiduoPonderadoIntegrable D.toInferior r :=
  integrable_residuo_ponderado D r

#print axioms TesisPINN.cota_densidad_sin_superior
#print axioms TesisPINN.cota_perdida_sin_superior
#print axioms TesisPINN.cota_norma_sin_superior
#print axioms TesisPINN.estimacion_error_sin_superior
#print axioms TesisPINN.acotada_integrable

end TesisPINN

