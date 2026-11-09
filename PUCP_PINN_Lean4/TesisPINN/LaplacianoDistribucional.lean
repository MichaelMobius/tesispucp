import TesisPINN.EnergiaSobolev
import Mathlib.Analysis.Distribution.DerivNotation

/-!
# Laplaciano distribucional en el plano

La definición usa segundas derivadas direccionales de distribuciones abiertas.
El signo es el convencional `Δ = ∂₁² + ∂₂²`.
-/

noncomputable section

open MeasureTheory TopologicalSpace EllipticPdes EllipticPdes.H1Graph
open scoped RealInnerProductSpace Distributions LineDeriv

namespace TesisPINN

abbrev Plano := EuclideanSpace ℝ (Fin 2)

def basePlano : OrthonormalBasis (Fin 2) ℝ Plano :=
  EuclideanSpace.basisFun (Fin 2) ℝ

/-- Laplaciano de una distribución sobre un abierto del plano. -/
def laplacianoDistribucional (Ω : Opens Plano) :
    𝓓'(Ω, ℝ) →L[ℝ] 𝓓'(Ω, ℝ) :=
  LineDeriv.laplacianCLM ℝ Plano (𝓓'(Ω, ℝ))

/-- El laplaciano distribucional es la suma de las dos segundas derivadas. -/
theorem laplacianoDistribucional_eq_suma (Ω : Opens Plano) (T : 𝓓'(Ω, ℝ)) :
    laplacianoDistribucional Ω T =
      ∑ i : Fin 2, ∂_{basePlano i} (∂_{basePlano i} T) := by
  exact LineDeriv.laplacianCLM_eq_sum basePlano T

/-- La derivada direccional clásica de una función de prueba sigue siendo
una función de prueba, y su soporte topológico permanece en `Ω`. -/
def derivadaPrueba {Ω : Set Plano} (φ : testFunctions Ω) (v : Plano) :
    testFunctions Ω :=
  ⟨fun x => fderiv ℝ (φ : Plano → ℝ) x v,
    (φ.2.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const,
    φ.2.2.1.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans φ.2.2.2⟩


/-- La igualdad `ΔU = r` en `𝓓′(Ω)`; `r` es una clase `L²(Ω)`.
`Ω` es abierto porque su tipo es `Opens Plano`. -/
def HasDistributionalLaplacian (Ω : Opens Plano) (μ : Measure Plano) [μ.IsAddHaarMeasure]
    (U : H01 μ (Ω : Set Plano)) (r : Lp ℝ 2 (μ.restrict (Ω : Set Plano))) : Prop :=
  laplacianoDistribucional Ω
    (Distribution.ofFun Ω (fnL (U : H1Graph μ (Ω : Set Plano))) μ ⊤) =
      Distribution.ofFun Ω r μ ⊤

/-- El laplaciano de `U` es la divergencia distribucional de su gradiente débil.
La igualdad de las primeras derivadas viene de `H01 ⊆ W12`. -/
theorem laplaciano_ofFun_eq_div_grad (Ω : Opens Plano) (μ : Measure Plano)
    [μ.IsAddHaarMeasure] (U : H01 μ (Ω : Set Plano)) :
    laplacianoDistribucional Ω
      (Distribution.ofFun Ω (fnL (U : H1Graph μ (Ω : Set Plano))) μ ⊤) =
      ∑ i : Fin 2,
        ∂_{basePlano i}
          (Distribution.ofFun Ω
            (fun x => innerSL ℝ ((gradL (U : H1Graph μ (Ω : Set Plano))) x)
              (basePlano i)) μ ⊤) := by
  rw [laplacianoDistribucional_eq_suma]
  have hg := h01_gradiente_distribucional (μ := μ) Ω.isOpen U
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun T : 𝓓'(Ω, ℝ) => ∂_{basePlano i} T) ((hg (basePlano i)).2.2)

/-- Evaluación del laplaciano: cada derivada exterior aporta un signo menos.
Esta identidad fija el signo antes de pasar al producto escalar `L²`. -/
theorem laplaciano_eval_suma (Ω : Opens Plano) (μ : Measure Plano)
    [μ.IsAddHaarMeasure] (U : H01 μ (Ω : Set Plano)) (ψ : 𝓓(Ω, ℝ)) :
    laplacianoDistribucional Ω
        (Distribution.ofFun Ω (fnL (U : H1Graph μ (Ω : Set Plano))) μ ⊤) ψ =
      ∑ i : Fin 2,
        -(∫ x, fderiv ℝ (ψ : Plano → ℝ) x (basePlano i) •
          innerSL ℝ ((gradL (U : H1Graph μ (Ω : Set Plano))) x) (basePlano i) ∂μ) := by
  rw [laplaciano_ofFun_eq_div_grad]
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact lineDerivOp_ofFun_apply
    (locallyIntegrableOn_innerSL_gradL (basePlano i) (U : H1Graph μ (Ω : Set Plano))) ψ

/-- La suma de las dos componentes direccionales recupera el producto escalar
con el gradiente clásico. -/
theorem suma_derivadas_eq_producto (φ : Plano → ℝ) (x w : Plano) :
    (∑ i : Fin 2, fderiv ℝ φ x (basePlano i) * inner ℝ w (basePlano i)) =
      inner ℝ w (gradient φ x) := by
  calc
    (∑ i : Fin 2, fderiv ℝ φ x (basePlano i) * inner ℝ w (basePlano i)) =
        ∑ i : Fin 2, inner ℝ w (basePlano i) *
          inner ℝ (basePlano i) (gradient φ x) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [EllipticPdes.inner_gradient_right φ x (basePlano i)]
      ring
    _ = inner ℝ w (gradient φ x) := basePlano.sum_inner_mul_inner w (gradient φ x)


/-- Producto integrable de una función localmente integrable con una prueba
continua de soporte compacto. Se usa para la suma de dos integrales. -/
private theorem integrable_producto_prueba {Ω : Set Plano} {μ : Measure Plano}
    {f ψ : Plano → ℝ} (hf : LocallyIntegrableOn f Ω μ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω) :
    Integrable (fun x => f x * ψ x) μ := by
  have hK : IntegrableOn (fun x => f x * ψ x) (tsupport ψ) μ :=
    (hf.integrableOn_compact_subset hs hc).mul_continuousOn hψ.continuousOn hc
  exact hK.integrable_of_forall_notMem_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
/-- Evaluar ΔU sobre una prueba produce el negativo del producto integral
entre el gradiente débil y el gradiente de la prueba. -/
theorem laplaciano_eval_producto (Ω : Opens Plano) (μ : Measure Plano)
    [μ.IsAddHaarMeasure] (U : H01 μ (Ω : Set Plano))
    (φ : testFunctions (Ω : Set Plano)) :
    laplacianoDistribucional Ω
        (Distribution.ofFun Ω (fnL (U : H1Graph μ (Ω : Set Plano))) μ ⊤)
        (⟨(φ : Plano → ℝ), φ.2.1, φ.2.2.1, φ.2.2.2⟩ : 𝓓(Ω, ℝ)) =
      -(∫ x, inner ℝ ((gradL (U : H1Graph μ (Ω : Set Plano))) x)
        (gradient (φ : Plano → ℝ) x) ∂μ) := by
  let ψ : 𝓓(Ω, ℝ) := ⟨(φ : Plano → ℝ), φ.2.1, φ.2.2.1, φ.2.2.2⟩
  change laplacianoDistribucional Ω
      (Distribution.ofFun Ω (fnL (U : H1Graph μ (Ω : Set Plano))) μ ⊤) ψ = _
  rw [laplaciano_eval_suma]
  have hint : ∀ i : Fin 2, Integrable
      (fun x => fderiv ℝ (φ : Plano → ℝ) x (basePlano i) *
        innerSL ℝ ((gradL (U : H1Graph μ (Ω : Set Plano))) x) (basePlano i)) μ := by
    intro i
    let hφd := derivadaPrueba φ (basePlano i)
    have hg := locallyIntegrableOn_innerSL_gradL (basePlano i)
      (U : H1Graph μ (Ω : Set Plano))
    have hprod := integrable_producto_prueba hg
      hφd.2.1.continuous hφd.2.2.1 hφd.2.2.2
    have hco : (hφd : Plano → ℝ) =
        fun x => fderiv ℝ (φ : Plano → ℝ) x (basePlano i) := by
      funext x
      rfl
    rw [hco] at hprod
    simpa only [mul_comm] using hprod
  change (∑ i : Fin 2, -(∫ x, fderiv ℝ (φ : Plano → ℝ) x (basePlano i) *
    innerSL ℝ ((gradL (U : H1Graph μ (Ω : Set Plano))) x) (basePlano i) ∂μ)) = _
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← integral_finsetSum Finset.univ (by intro i hi; simpa only [mul_comm] using hint i)]
  congr 1
  funext x
  exact suma_derivadas_eq_producto (φ : Plano → ℝ) x
    ((gradL (U : H1Graph μ (Ω : Set Plano))) x)

/-- Producto `L²` del gradiente con una prueba, escrito como integral global.
La integral fuera de `Ω` se anula por el soporte de la prueba. -/
theorem inner_gradiente_prueba_eq_integral (Ω : Opens Plano) (μ : Measure Plano)
    [μ.IsAddHaarMeasure] (U : H01 μ (Ω : Set Plano))
    (φ : testFunctions (Ω : Set Plano)) :
    inner ℝ (gradL (U : H1Graph μ (Ω : Set Plano)))
        (gradCls μ (Ω : Set Plano) φ) =
      ∫ x, inner ℝ ((gradL (U : H1Graph μ (Ω : Set Plano))) x)
        (gradient (φ : Plano → ℝ) x) ∂μ := by
  calc
    inner ℝ (gradL (U : H1Graph μ (Ω : Set Plano)))
        (gradCls μ (Ω : Set Plano) φ) =
        inner ℝ (gradCls μ (Ω : Set Plano) φ)
          (gradL (U : H1Graph μ (Ω : Set Plano))) := real_inner_comm _ _
    _ = ∫ x in (Ω : Set Plano),
        inner ℝ (gradient (φ : Plano → ℝ) x)
          ((gradL (U : H1Graph μ (Ω : Set Plano))) x) ∂μ := by
        exact inner_toLp_left (memLp_gradient_of_mem φ.2) _
    _ = ∫ x in (Ω : Set Plano),
        inner ℝ ((gradL (U : H1Graph μ (Ω : Set Plano))) x)
          (gradient (φ : Plano → ℝ) x) ∂μ := by
        apply integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact real_inner_comm _ _
    _ = ∫ x, inner ℝ ((gradL (U : H1Graph μ (Ω : Set Plano))) x)
          (gradient (φ : Plano → ℝ) x) ∂μ := by
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          have hnot : x ∉ tsupport (φ : Plano → ℝ) :=
            fun h => hx (φ.2.2.2 h)
          have hd : fderiv ℝ (φ : Plano → ℝ) x = 0 :=
            fderiv_of_notMem_tsupport ℝ hnot
          simp [gradient, hd])

/-- Producto escalar de un residuo `L²` con la prueba, como integral global. -/
theorem inner_residuo_prueba_eq_integral (Ω : Opens Plano) (μ : Measure Plano)
    [μ.IsAddHaarMeasure] (r : Lp ℝ 2 (μ.restrict (Ω : Set Plano)))
    (φ : testFunctions (Ω : Set Plano)) :
    inner ℝ r (fnCls μ (Ω : Set Plano) φ) =
      ∫ x, (φ : Plano → ℝ) x * r x ∂μ := by
  calc
    inner ℝ r (fnCls μ (Ω : Set Plano) φ) =
        inner ℝ (fnCls μ (Ω : Set Plano) φ) r := real_inner_comm _ _
    _ = ∫ x in (Ω : Set Plano), inner ℝ ((φ : Plano → ℝ) x) (r x) ∂μ := by
        exact inner_toLp_left (memLp_of_mem φ.2) _
    _ = ∫ x in (Ω : Set Plano), (φ : Plano → ℝ) x * r x ∂μ := by
        simp only [Real.inner_apply]
    _ = ∫ x, (φ : Plano → ℝ) x * r x ∂μ := by
        exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          have hnot : x ∉ tsupport (φ : Plano → ℝ) := fun h => hx (φ.2.2.2 h)
          rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul])

/-- El puente faltante: la igualdad del laplaciano en `𝓓′(Ω)` implica
la identidad débil sobre toda función de prueba. -/
theorem laplaciano_distribucional_implica_prueba (Ω : Opens Plano) (μ : Measure Plano)
    [μ.IsAddHaarMeasure] (U : H01 μ (Ω : Set Plano))
    (r : Lp ℝ 2 (μ.restrict (Ω : Set Plano)))
    (hΔ : HasDistributionalLaplacian Ω μ U r) : HasTestLaplacian U r := by
  intro φ
  let ψ : 𝓓(Ω, ℝ) := ⟨(φ : Plano → ℝ), φ.2.1, φ.2.2.1, φ.2.2.2⟩
  have heq := congrArg (fun T : 𝓓'(Ω, ℝ) => T ψ) hΔ
  have hl := laplaciano_eval_producto Ω μ U φ
  have hr : Distribution.ofFun Ω r μ ⊤ ψ =
      ∫ x, (φ : Plano → ℝ) x * r x ∂μ := by
    simpa [ψ, smul_eq_mul] using
      (Distribution.ofFun_apply (locallyIntegrableOn_lp r) (φ := ψ))
  rw [hl, hr] at heq
  rw [← inner_gradiente_prueba_eq_integral Ω μ U φ,
    ← inner_residuo_prueba_eq_integral Ω μ r φ] at heq
  exact (neg_eq_iff_eq_neg).mp heq


/-- El representante `L²` del laplaciano distribucional es único. Por ello
`‖r‖` en la cota energética está determinado por `ΔU`. -/
theorem laplaciano_distribucional_l2_unico (Ω : Opens Plano) (μ : Measure Plano)
    [μ.IsAddHaarMeasure] (U : H01 μ (Ω : Set Plano))
    (r r' : Lp ℝ 2 (μ.restrict (Ω : Set Plano)))
    (hr : HasDistributionalLaplacian Ω μ U r)
    (hr' : HasDistributionalLaplacian Ω μ U r') : r = r' := by
  have heq : Distribution.ofFun Ω r μ ⊤ = Distribution.ofFun Ω r' μ ⊤ :=
    hr.symm.trans hr'
  exact Lp.ext (Distribution.ofFun_injective
    (locallyIntegrableOn_lp r) (locallyIntegrableOn_lp r') heq)
/-- Estimación analítica del Lema 3.19 en el plano. La premisa `ΔU = r`
se expresa como igualdad en `𝓓′(Ω)`; Green y Poincaré se deducen. -/
theorem energia_sobolev_de_laplaciano_distribucional (Ω : Opens Plano) (μ : Measure Plano)
    [μ.IsAddHaarMeasure] (hΩb : Bornology.IsBounded (Ω : Set Plano))
    (U : H01 μ (Ω : Set Plano)) (r : Lp ℝ 2 (μ.restrict (Ω : Set Plano)))
    (hΔ : HasDistributionalLaplacian Ω μ U r) :
    ∃ Cₚ : ℝ, 0 < Cₚ ∧
      ‖(U : H1Graph μ (Ω : Set Plano))‖ ≤
        Cₚ * Real.sqrt (1 + Cₚ ^ 2) * ‖r‖ :=
  energia_sobolev_de_laplaciano_de_prueba hΩb U r
    (laplaciano_distribucional_implica_prueba Ω μ U r hΔ)

/-- Versión para la medida de Lebesgue en `ℝ²`, con `Ω` abierto y acotado.
La pertenencia a `H₀¹` se expresa por el cierre de grafos de prueba. -/
theorem energia_sobolev_plano_volumen (Ω : Opens Plano)
    (hΩb : Bornology.IsBounded (Ω : Set Plano))
    (U : H01 (volume : Measure Plano) (Ω : Set Plano))
    (r : Lp ℝ 2 ((volume : Measure Plano).restrict (Ω : Set Plano)))
    (hΔ : HasDistributionalLaplacian Ω volume U r) :
    ∃ Cₚ : ℝ, 0 < Cₚ ∧
      ‖(U : H1Graph (volume : Measure Plano) (Ω : Set Plano))‖ ≤
        Cₚ * Real.sqrt (1 + Cₚ ^ 2) * ‖r‖ :=
  energia_sobolev_de_laplaciano_distribucional Ω volume hΩb U r hΔ
#print axioms TesisPINN.laplacianoDistribucional_eq_suma
#print axioms TesisPINN.energia_sobolev_plano_volumen
#print axioms TesisPINN.laplaciano_distribucional_implica_prueba
#print axioms TesisPINN.laplaciano_distribucional_l2_unico
#print axioms TesisPINN.energia_sobolev_de_laplaciano_distribucional
#print axioms TesisPINN.inner_gradiente_prueba_eq_integral
#print axioms TesisPINN.inner_residuo_prueba_eq_integral
#print axioms TesisPINN.laplaciano_eval_producto
#print axioms TesisPINN.suma_derivadas_eq_producto
#print axioms TesisPINN.laplaciano_eval_suma
#print axioms TesisPINN.laplaciano_ofFun_eq_div_grad

end TesisPINN

