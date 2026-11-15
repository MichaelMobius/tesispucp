import TesisPINN.EnergiaSobolev
import Mathlib.Analysis.Distribution.DerivNotation

/-!
# Laplaciano distribucional de un grafo Sobolev

El operador de Mathlib suma segundas derivadas en una base ortonormal.
La fórmula de evaluación usa el gradiente débil de `W12`.
-/

noncomputable section

open MeasureTheory TopologicalSpace EllipticPdes EllipticPdes.H1Graph
open scoped RealInnerProductSpace Distributions LineDeriv

namespace TesisPINN

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private noncomputable def baseDimensional : OrthonormalBasis
    (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E

/-- Laplaciano de una distribución sobre un abierto de dimensión finita. -/
def laplacianoDistribucionalDimensional (Ω : Opens E) :
    𝓓'(Ω, ℝ) →L[ℝ] 𝓓'(Ω, ℝ) :=
  LineDeriv.laplacianCLM ℝ E (𝓓'(Ω, ℝ))

/-- El laplaciano distribucional es la suma de las segundas derivadas. -/
theorem laplacianoDistribucionalDimensional_eq_suma (Ω : Opens E) (T : 𝓓'(Ω, ℝ)) :
    laplacianoDistribucionalDimensional Ω T =
      ∑ i : Fin (Module.finrank ℝ E), ∂_{baseDimensional i} (∂_{baseDimensional i} T) := by
  exact LineDeriv.laplacianCLM_eq_sum baseDimensional T

/-- La derivada direccional clásica de una función de prueba sigue siendo
una función de prueba, y su soporte topológico permanece en `Ω`. -/
def derivadaPruebaDimensional {Ω : Set E} (φ : testFunctions Ω) (v : E) :
    testFunctions Ω :=
  ⟨fun x => fderiv ℝ (φ : E → ℝ) x v,
    (φ.2.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const,
    φ.2.2.1.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans φ.2.2.2⟩


/-- La igualdad `ΔU = r` en `𝓓′(Ω)`; `r` es una clase `L²(Ω)`.
`Ω` es abierto porque su tipo es `Opens E`. -/
def HasDistributionalLaplacianDimensional (Ω : Opens E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (U : H1Graph μ (Ω : Set E)) (r : Lp ℝ 2 (μ.restrict (Ω : Set E))) : Prop :=
  laplacianoDistribucionalDimensional Ω
    (Distribution.ofFun Ω (fnL U) μ ⊤) =
      Distribution.ofFun Ω r μ ⊤

/-- El laplaciano de `U` es la divergencia distribucional de su gradiente débil.
La igualdad de las primeras derivadas viene de la caracterización de `W12`. -/
theorem laplaciano_dimensional_ofFun_eq_div_grad (Ω : Opens E) (μ : Measure E)
    [μ.IsAddHaarMeasure] (U : H1Graph μ (Ω : Set E)) (hU : U ∈ W12 μ (Ω : Set E)) :
    laplacianoDistribucionalDimensional Ω
      (Distribution.ofFun Ω (fnL U) μ ⊤) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∂_{baseDimensional i}
          (Distribution.ofFun Ω
            (fun x => innerSL ℝ ((gradL U) x)
              (baseDimensional i)) μ ⊤) := by
  rw [laplacianoDistribucionalDimensional_eq_suma]
  have hg := (mem_W12_iff_hasWeakFDerivOn Ω.isOpen U).mp hU
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun T : 𝓓'(Ω, ℝ) => ∂_{baseDimensional i} T) ((hg (baseDimensional i)).2.2)

/-- Evaluación del laplaciano: cada derivada exterior aporta un signo menos.
Esta identidad fija el signo antes de pasar al producto escalar `L²`. -/
theorem laplaciano_dimensional_eval_suma (Ω : Opens E) (μ : Measure E)
    [μ.IsAddHaarMeasure] (U : H1Graph μ (Ω : Set E)) (hU : U ∈ W12 μ (Ω : Set E))
    (ψ : 𝓓(Ω, ℝ)) :
    laplacianoDistribucionalDimensional Ω
        (Distribution.ofFun Ω (fnL U) μ ⊤) ψ =
      ∑ i : Fin (Module.finrank ℝ E),
        -(∫ x, fderiv ℝ (ψ : E → ℝ) x (baseDimensional i) •
          innerSL ℝ ((gradL U) x) (baseDimensional i) ∂μ) := by
  rw [laplaciano_dimensional_ofFun_eq_div_grad Ω μ U hU]
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact lineDerivOp_ofFun_apply
    (locallyIntegrableOn_innerSL_gradL (baseDimensional i) U) ψ

/-- La suma de las componentes direccionales recupera el producto escalar
con el gradiente clásico. -/
theorem suma_derivadas_dimensional_eq_producto (φ : E → ℝ) (x w : E) :
    (∑ i : Fin (Module.finrank ℝ E), fderiv ℝ φ x (baseDimensional i) * inner ℝ w (baseDimensional i)) =
      inner ℝ w (gradient φ x) := by
  calc
    (∑ i : Fin (Module.finrank ℝ E), fderiv ℝ φ x (baseDimensional i) * inner ℝ w (baseDimensional i)) =
        ∑ i : Fin (Module.finrank ℝ E), inner ℝ w (baseDimensional i) *
          inner ℝ (baseDimensional i) (gradient φ x) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [EllipticPdes.inner_gradient_right φ x (baseDimensional i)]
      ring
    _ = inner ℝ w (gradient φ x) := baseDimensional.sum_inner_mul_inner w (gradient φ x)


/-- Producto integrable de una función localmente integrable con una prueba
continua de soporte compacto. Se usa para la suma finita de integrales. -/
private theorem integrable_producto_prueba {Ω : Set E} {μ : Measure E}
    {f ψ : E → ℝ} (hf : LocallyIntegrableOn f Ω μ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω) :
    Integrable (fun x => f x * ψ x) μ := by
  have hK : IntegrableOn (fun x => f x * ψ x) (tsupport ψ) μ :=
    (hf.integrableOn_compact_subset hs hc).mul_continuousOn hψ.continuousOn hc
  exact hK.integrable_of_forall_notMem_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
/-- Evaluar ΔU sobre una prueba produce el negativo del producto integral
entre el gradiente débil y el gradiente de la prueba. -/
theorem laplaciano_dimensional_eval_producto (Ω : Opens E) (μ : Measure E)
    [μ.IsAddHaarMeasure] (U : H1Graph μ (Ω : Set E)) (hU : U ∈ W12 μ (Ω : Set E))
    (φ : testFunctions (Ω : Set E)) :
    laplacianoDistribucionalDimensional Ω
        (Distribution.ofFun Ω (fnL U) μ ⊤)
        (⟨(φ : E → ℝ), φ.2.1, φ.2.2.1, φ.2.2.2⟩ : 𝓓(Ω, ℝ)) =
      -(∫ x, inner ℝ ((gradL U) x)
        (gradient (φ : E → ℝ) x) ∂μ) := by
  let ψ : 𝓓(Ω, ℝ) := ⟨(φ : E → ℝ), φ.2.1, φ.2.2.1, φ.2.2.2⟩
  change laplacianoDistribucionalDimensional Ω
      (Distribution.ofFun Ω (fnL U) μ ⊤) ψ = _
  rw [laplaciano_dimensional_eval_suma Ω μ U hU]
  have hint : ∀ i : Fin (Module.finrank ℝ E), Integrable
      (fun x => fderiv ℝ (φ : E → ℝ) x (baseDimensional i) *
        innerSL ℝ ((gradL U) x) (baseDimensional i)) μ := by
    intro i
    let hφd := derivadaPruebaDimensional φ (baseDimensional i)
    have hg := locallyIntegrableOn_innerSL_gradL (baseDimensional i)
      (U : H1Graph μ (Ω : Set E))
    have hprod := integrable_producto_prueba hg
      hφd.2.1.continuous hφd.2.2.1 hφd.2.2.2
    have hco : (hφd : E → ℝ) =
        fun x => fderiv ℝ (φ : E → ℝ) x (baseDimensional i) := by
      funext x
      rfl
    rw [hco] at hprod
    simpa only [mul_comm] using hprod
  change (∑ i : Fin (Module.finrank ℝ E), -(∫ x, fderiv ℝ (φ : E → ℝ) x (baseDimensional i) *
    innerSL ℝ ((gradL U) x) (baseDimensional i) ∂μ)) = _
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← integral_finsetSum Finset.univ (by intro i hi; simpa only [mul_comm] using hint i)]
  congr 1
  funext x
  exact suma_derivadas_dimensional_eq_producto (φ : E → ℝ) x
    ((gradL U) x)

/-- Producto `L²` del gradiente con una prueba, escrito como integral global.
La integral fuera de `Ω` se anula por el soporte de la prueba. -/
theorem inner_gradiente_prueba_dimensional_eq_integral (Ω : Opens E) (μ : Measure E)
    [μ.IsAddHaarMeasure] (U : H1Graph μ (Ω : Set E))
    (φ : testFunctions (Ω : Set E)) :
    inner ℝ (gradL U)
        (gradCls μ (Ω : Set E) φ) =
      ∫ x, inner ℝ ((gradL U) x)
        (gradient (φ : E → ℝ) x) ∂μ := by
  calc
    inner ℝ (gradL U)
        (gradCls μ (Ω : Set E) φ) =
        inner ℝ (gradCls μ (Ω : Set E) φ)
          (gradL U) := real_inner_comm _ _
    _ = ∫ x in (Ω : Set E),
        inner ℝ (gradient (φ : E → ℝ) x)
          ((gradL U) x) ∂μ := by
        exact inner_toLp_left (memLp_gradient_of_mem φ.2) _
    _ = ∫ x in (Ω : Set E),
        inner ℝ ((gradL U) x)
          (gradient (φ : E → ℝ) x) ∂μ := by
        apply integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact real_inner_comm _ _
    _ = ∫ x, inner ℝ ((gradL U) x)
          (gradient (φ : E → ℝ) x) ∂μ := by
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          have hnot : x ∉ tsupport (φ : E → ℝ) :=
            fun h => hx (φ.2.2.2 h)
          have hd : fderiv ℝ (φ : E → ℝ) x = 0 :=
            fderiv_of_notMem_tsupport ℝ hnot
          simp [gradient, hd])

/-- Producto escalar de un residuo `L²` con la prueba, como integral global. -/
theorem inner_residuo_prueba_dimensional_eq_integral (Ω : Opens E) (μ : Measure E)
    [μ.IsAddHaarMeasure] (r : Lp ℝ 2 (μ.restrict (Ω : Set E)))
    (φ : testFunctions (Ω : Set E)) :
    inner ℝ r (fnCls μ (Ω : Set E) φ) =
      ∫ x, (φ : E → ℝ) x * r x ∂μ := by
  calc
    inner ℝ r (fnCls μ (Ω : Set E) φ) =
        inner ℝ (fnCls μ (Ω : Set E) φ) r := real_inner_comm _ _
    _ = ∫ x in (Ω : Set E), inner ℝ ((φ : E → ℝ) x) (r x) ∂μ := by
        exact inner_toLp_left (memLp_of_mem φ.2) _
    _ = ∫ x in (Ω : Set E), (φ : E → ℝ) x * r x ∂μ := by
        simp only [Real.inner_apply]
    _ = ∫ x, (φ : E → ℝ) x * r x ∂μ := by
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          have hnot : x ∉ tsupport (φ : E → ℝ) := fun h => hx (φ.2.2.2 h)
          rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul])

/-- La igualdad del laplaciano en `𝓓′(Ω)` implica
la identidad débil sobre toda función de prueba. -/
theorem laplaciano_dimensional_implica_prueba (Ω : Opens E) (μ : Measure E)
    [μ.IsAddHaarMeasure] (U : H01 μ (Ω : Set E))
    (r : Lp ℝ 2 (μ.restrict (Ω : Set E)))
    (hΔ : HasDistributionalLaplacianDimensional Ω μ U r) : HasTestLaplacian U r := by
  intro φ
  let ψ : 𝓓(Ω, ℝ) := ⟨(φ : E → ℝ), φ.2.1, φ.2.2.1, φ.2.2.2⟩
  have heq := congrArg (fun T : 𝓓'(Ω, ℝ) => T ψ) hΔ
  have hl := laplaciano_dimensional_eval_producto Ω μ U (H01_le_W12 U.property) φ
  have hr : Distribution.ofFun Ω r μ ⊤ ψ =
      ∫ x, (φ : E → ℝ) x * r x ∂μ := by
    simpa [ψ, smul_eq_mul] using
      (Distribution.ofFun_apply (locallyIntegrableOn_lp r) (φ := ψ))
  rw [hl, hr] at heq
  rw [← inner_gradiente_prueba_dimensional_eq_integral Ω μ U φ,
    ← inner_residuo_prueba_dimensional_eq_integral Ω μ r φ] at heq
  exact (neg_eq_iff_eq_neg).mp heq


/-- El representante `L²` del laplaciano distribucional es único. Por ello
`‖r‖` en la cota energética está determinado por `ΔU`. -/
theorem laplaciano_dimensional_l2_unico (Ω : Opens E) (μ : Measure E)
    [μ.IsAddHaarMeasure] (U : H1Graph μ (Ω : Set E))
    (r r' : Lp ℝ 2 (μ.restrict (Ω : Set E)))
    (hr : HasDistributionalLaplacianDimensional Ω μ U r)
    (hr' : HasDistributionalLaplacianDimensional Ω μ U r') : r = r' := by
  have heq : Distribution.ofFun Ω r μ ⊤ = Distribution.ofFun Ω r' μ ⊤ :=
    hr.symm.trans hr'
  exact Lp.ext (Distribution.ofFun_injective
    (locallyIntegrableOn_lp r) (locallyIntegrableOn_lp r') heq)
#check laplaciano_dimensional_eval_producto
#check laplaciano_dimensional_implica_prueba
#print axioms laplaciano_dimensional_eval_producto
#print axioms laplaciano_dimensional_implica_prueba
#print axioms laplaciano_dimensional_l2_unico

end TesisPINN
