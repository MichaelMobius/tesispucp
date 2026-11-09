import EllipticPdes.Poincare.GraphBounded
import TesisPINN.Energia
import Mathlib.Tactic.Linarith

/-!
# Lema 3.19: estructura Sobolev y constante de Poincaré

El error se representa por `H1Graph.H01 μ Ω`. La norma del grafo es la norma
H¹ de sus componentes `fnL` y `gradL`. La desigualdad de Poincaré se obtiene
de EllipticPDE, sin postularla.
-/

noncomputable section

open MeasureTheory
open EllipticPdes
open EllipticPdes.H1Graph
open scoped RealInnerProductSpace

namespace TesisPINN

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Nontrivial E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Set E}

/-- Una constante de Poincaré estrictamente positiva a partir de la cota
cuadrática `C ≥ 0` de EllipticPDE. Elegimos `Cₚ = √(C + 1)`, de modo que
`C ≤ Cₚ²` incluso cuando la constante original es cero. -/
theorem exists_poincare_constant (hΩb : Bornology.IsBounded Ω) :
    ∃ Cₚ : ℝ, 0 < Cₚ ∧
      ∀ U : H01 μ Ω,
        ‖fnL (U : H1Graph μ Ω)‖ ≤ Cₚ * ‖gradL (U : H1Graph μ Ω)‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    poincare_H01_of_bounded (μ := μ) (Ω := Ω) hΩb
  let Cₚ : ℝ := Real.sqrt (C + 1)
  have hCₚ : 0 < Cₚ := by
    dsimp [Cₚ]
    exact Real.sqrt_pos.2 (by linarith)
  refine ⟨Cₚ, hCₚ, ?_⟩
  intro U
  have hsq : ‖fnL (U : H1Graph μ Ω)‖ ^ 2 ≤
      C * ‖gradL (U : H1Graph μ Ω)‖ ^ 2 :=
    hbound (U : H1Graph μ Ω) U.property
  have hCₚsq : Cₚ ^ 2 = C + 1 := Real.sq_sqrt (by linarith)
  have hsq' : ‖fnL (U : H1Graph μ Ω)‖ ^ 2 ≤
      Cₚ ^ 2 * ‖gradL (U : H1Graph μ Ω)‖ ^ 2 := by
    calc
      ‖fnL (U : H1Graph μ Ω)‖ ^ 2 ≤
          C * ‖gradL (U : H1Graph μ Ω)‖ ^ 2 := hsq
      _ ≤ Cₚ ^ 2 * ‖gradL (U : H1Graph μ Ω)‖ ^ 2 := by
        rw [hCₚsq]
        exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hCₚ.le (norm_nonneg _))).mp (by simpa only [mul_pow] using hsq')

/-- La identidad definicional de la norma H¹ del grafo. -/
theorem norma_sobolev_cuadratica (U : H01 μ Ω) :
    ‖(U : H1Graph μ Ω)‖ ^ 2 =
      ‖fnL (U : H1Graph μ Ω)‖ ^ 2 +
        ‖gradL (U : H1Graph μ Ω)‖ ^ 2 :=
  norm_sq_eq (U : H1Graph μ Ω)


/-- Formulación débil distribucional de `ΔU = r` sobre funciones de prueba:
`-∫ ∇U · ∇φ = ∫ r φ`. La derivada primera del grafo es la derivada
distribucional por `H01_le_W12` y `mem_W12_iff_hasWeakFDerivOn`. -/
def HasTestLaplacian (U : H01 μ Ω) (r : Lp ℝ 2 (μ.restrict Ω)) : Prop :=
  ∀ φ : testFunctions Ω,
    inner ℝ (gradL (U : H1Graph μ Ω)) (gradCls μ Ω φ) =
      -(inner ℝ r (fnCls μ Ω φ))


/-- El campo `gradL U` es realmente el gradiente distribucional de `fnL U`
cuando `Ω` es abierto, por la caracterización de `W¹,²` de EllipticPDE. -/
theorem h01_gradiente_distribucional (hΩ : IsOpen Ω) (U : H01 μ Ω) :
    HasWeakFDerivOn ⟨Ω, hΩ⟩ (fnL (U : H1Graph μ Ω))
      (fun x => innerSL ℝ ((gradL (U : H1Graph μ Ω)) x)) μ := by
  apply (mem_W12_iff_hasWeakFDerivOn hΩ (U : H1Graph μ Ω)).mp
  exact H01_le_W12 U.property
/-- La identidad de Green se extiende desde las funciones de prueba a todo
`H₀¹` por densidad; en particular se puede tomar como prueba el propio error. -/
theorem green_por_densidad (U : H01 μ Ω) (r : Lp ℝ 2 (μ.restrict Ω))
    (hΔ : HasTestLaplacian U r) :
    inner ℝ (gradL (U : H1Graph μ Ω)) (gradL (U : H1Graph μ Ω)) =
      -(inner ℝ r (fnL (U : H1Graph μ Ω))) := by
  let F : H1Graph μ Ω →L[ℝ] ℝ :=
    (innerSL ℝ (gradL (U : H1Graph μ Ω))).comp gradL +
      (innerSL ℝ r).comp fnL
  have hclosed : IsClosed {V : H1Graph μ Ω | F V = 0} :=
    isClosed_singleton.preimage F.continuous
  have htest : ∀ φ : testFunctions Ω,
      testGraphₗ μ Ω φ ∈ {V : H1Graph μ Ω | F V = 0} := by
    intro φ
    change inner ℝ (gradL (U : H1Graph μ Ω)) (gradCls μ Ω φ) +
      inner ℝ r (fnCls μ Ω φ) = 0
    rw [hΔ φ]
    abel
  have hU : F (U : H1Graph μ Ω) = 0 :=
    (H01_subset_of_isClosed hclosed htest) U.property
  change inner ℝ (gradL (U : H1Graph μ Ω)) (gradL (U : H1Graph μ Ω)) +
    inner ℝ r (fnL (U : H1Graph μ Ω)) = 0 at hU
  exact eq_neg_of_add_eq_zero_left hU

/-- Estimación energética de la parte analítica del Lema 3.19, a partir de
la identidad distribucional sobre pruebas y la cota de Poincaré de la biblioteca. -/
theorem energia_sobolev_de_laplaciano_de_prueba (hΩb : Bornology.IsBounded Ω)
    (U : H01 μ Ω) (r : Lp ℝ 2 (μ.restrict Ω))
    (hΔ : HasTestLaplacian U r) :
    ∃ Cₚ : ℝ, 0 < Cₚ ∧
      ‖(U : H1Graph μ Ω)‖ ≤ Cₚ * Real.sqrt (1 + Cₚ ^ 2) * ‖r‖ := by
  obtain ⟨Cₚ, hCₚ, hPoincare⟩ := exists_poincare_constant (μ := μ) hΩb
  refine ⟨Cₚ, hCₚ, ?_⟩
  have hGreen := green_por_densidad U r hΔ
  have hEnergy := energia_norma_par_debil Cₚ
    (fnL (U : H1Graph μ Ω)) r (gradL (U : H1Graph μ Ω))
    hCₚ hGreen (hPoincare U)
  change ‖mk (fnL (U : H1Graph μ Ω)) (gradL (U : H1Graph μ Ω))‖ ≤ _ at hEnergy
  rw [mk_fnL_gradL] at hEnergy
  exact hEnergy
#print axioms TesisPINN.exists_poincare_constant
#print axioms TesisPINN.norma_sobolev_cuadratica
#print axioms TesisPINN.h01_gradiente_distribucional
#print axioms TesisPINN.green_por_densidad
#print axioms TesisPINN.energia_sobolev_de_laplaciano_de_prueba

end TesisPINN





