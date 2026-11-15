import TesisPINN.LaplacianoDistribucionalDimensional

/-!
# Estabilidad de Poisson con condición homogénea Sobolev
-/

noncomputable section

open MeasureTheory TopologicalSpace EllipticPdes EllipticPdes.H1Graph
open scoped RealInnerProductSpace Distributions

namespace TesisPINN

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- Green evaluada en el propio error. Los dos productos se calculan en
`L²(μ.restrict Ω)`, con el mismo representante del laplaciano. -/
theorem green_dimensional (Ω : Opens E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : H01 μ (Ω : Set E)) (r : Lp ℝ 2 (μ.restrict (Ω : Set E)))
    (hΔ : HasDistributionalLaplacianDimensional Ω μ e r) :
    ‖gradL (e : H1Graph μ (Ω : Set E))‖ ^ 2 =
      -(inner ℝ r (fnL (e : H1Graph μ (Ω : Set E)))) := by
  rw [← real_inner_self_eq_norm_sq]
  exact green_por_densidad e r (laplaciano_dimensional_implica_prueba Ω μ e r hΔ)

/-- (3.71) con cualquier constante de Poincaré positiva dada. -/
theorem lema319_constante_dada (Ω : Opens E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (C : ℝ) (hC : 0 < C)
    (hP : ∀ e : H01 μ (Ω : Set E),
      ‖fnL (e : H1Graph μ (Ω : Set E))‖ ≤ C * ‖gradL (e : H1Graph μ (Ω : Set E))‖)
    (e : H01 μ (Ω : Set E)) (r : Lp ℝ 2 (μ.restrict (Ω : Set E)))
    (hΔ : HasDistributionalLaplacianDimensional Ω μ e r) :
    ‖(e : H1Graph μ (Ω : Set E))‖ ≤ C * Real.sqrt (1 + C ^ 2) * ‖r‖ := by
  have hGreen := green_por_densidad e r (laplaciano_dimensional_implica_prueba Ω μ e r hΔ)
  have hEnergy := energia_norma_par_debil C (fnL (e : H1Graph μ (Ω : Set E))) r
    (gradL (e : H1Graph μ (Ω : Set E))) hC hGreen (hP e)
  change ‖mk (fnL (e : H1Graph μ (Ω : Set E))) (gradL (e : H1Graph μ (Ω : Set E)))‖ ≤
    _ at hEnergy
  rwa [mk_fnL_gradL] at hEnergy

/-- Para un abierto acotado se elige una constante antes de cuantificar
sobre el error y el residuo. -/
theorem lema319_dimensional (Ω : Opens E) (μ : Measure E)
    [μ.IsAddHaarMeasure] (hΩb : Bornology.IsBounded (Ω : Set E)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ e : H01 μ (Ω : Set E),
        ‖fnL (e : H1Graph μ (Ω : Set E))‖ ≤ C * ‖gradL (e : H1Graph μ (Ω : Set E))‖) ∧
      ∀ (e : H01 μ (Ω : Set E)) (r : Lp ℝ 2 (μ.restrict (Ω : Set E))),
        HasDistributionalLaplacianDimensional Ω μ e r →
          ‖(e : H1Graph μ (Ω : Set E))‖ ≤ C * Real.sqrt (1 + C ^ 2) * ‖r‖ := by
  obtain ⟨C, hC, hP⟩ := exists_poincare_constant (μ := μ) hΩb
  exact ⟨C, hC, hP, lema319_constante_dada Ω μ C hC hP⟩

/-- Linealidad de la inclusión de los representantes `L²` en distribuciones. -/
private theorem ofFun_sub_lp (Ω : Opens E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (a b : Lp ℝ 2 (μ.restrict (Ω : Set E))) :
    Distribution.ofFun Ω (a - b) μ ⊤ =
      Distribution.ofFun Ω a μ ⊤ - Distribution.ofFun Ω b μ ⊤ := by
  calc
    Distribution.ofFun Ω (a - b) μ ⊤ =
        Distribution.ofFun Ω ((a : E → ℝ) - (b : E → ℝ)) μ ⊤ :=
      Distribution.ofFun_congr_ae (Lp.coeFn_sub a b)
    _ = _ := by
      rw [sub_eq_add_neg, Distribution.ofFun_add
        (locallyIntegrableOn_lp a) (locallyIntegrableOn_lp b).neg,
        Distribution.ofFun_neg]
      rfl

/-- Con el error Lean `h-u`, el residuo es `Δh-f`. -/
theorem laplaciano_dimensional_resta (Ω : Opens E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (h u : H1Graph μ (Ω : Set E)) (Lh f : Lp ℝ 2 (μ.restrict (Ω : Set E)))
    (hh : HasDistributionalLaplacianDimensional Ω μ h Lh)
    (hu : HasDistributionalLaplacianDimensional Ω μ u f) :
    HasDistributionalLaplacianDimensional Ω μ (h - u) (Lh - f) := by
  unfold HasDistributionalLaplacianDimensional at *
  rw [map_sub, ofFun_sub_lp, map_sub, hh, hu, ofFun_sub_lp]

/-- (3.74) para candidatos Sobolev con error en `H₀¹`. -/
theorem estimacion320_dimensional (Ω : Opens E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (C : ℝ) (hC : 0 < C)
    (hP : ∀ e : H01 μ (Ω : Set E),
      ‖fnL (e : H1Graph μ (Ω : Set E))‖ ≤ C * ‖gradL (e : H1Graph μ (Ω : Set E))‖)
    (h u : H1Graph μ (Ω : Set E)) (Lh f : Lp ℝ 2 (μ.restrict (Ω : Set E)))
    (he : h - u ∈ H01 μ (Ω : Set E))
    (hh : HasDistributionalLaplacianDimensional Ω μ h Lh)
    (hu : HasDistributionalLaplacianDimensional Ω μ u f) :
    ‖h - u‖ ≤ C * Real.sqrt (1 + C ^ 2) * ‖Lh - f‖ :=
  lema319_constante_dada Ω μ C hC hP ⟨h - u, he⟩ (Lh - f)
    (laplaciano_dimensional_resta Ω μ h u Lh f hh hu)

/-- Consecuencia exacta de la igualdad de trazas para un operador cuyo
núcleo, como subespacio de `W12`, se haya identificado con `H01`. -/
theorem diferencia_mem_H01_de_traza {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (Ω : Opens E) (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (Tr : W12 μ (Ω : Set E) →L[ℝ] F)
    (hker : ∀ v : W12 μ (Ω : Set E), Tr v = 0 ↔
      (v : H1Graph μ (Ω : Set E)) ∈ H01 μ (Ω : Set E))
    (h u : W12 μ (Ω : Set E)) (ht : Tr h = Tr u) :
    (h : H1Graph μ (Ω : Set E)) - (u : H1Graph μ (Ω : Set E)) ∈ H01 μ (Ω : Set E) :=
  (hker (h - u)).mp (by rw [map_sub, ht, sub_self])

/-- Cota (3.74) condicionada a la identificación del núcleo de la traza. -/
theorem estimacion320_de_trazas_iguales {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : Opens E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (Tr : W12 μ (Ω : Set E) →L[ℝ] F)
    (hker : ∀ v : W12 μ (Ω : Set E), Tr v = 0 ↔ v.val ∈ H01 μ (Ω : Set E))
    (C : ℝ) (hC : 0 < C)
    (hP : ∀ e : H01 μ (Ω : Set E), ‖fnL e.val‖ ≤ C * ‖gradL e.val‖)
    (h u : W12 μ (Ω : Set E)) (ht : Tr h = Tr u)
    (Lh f : Lp ℝ 2 (μ.restrict (Ω : Set E)))
    (hh : HasDistributionalLaplacianDimensional Ω μ h.val Lh)
    (hu : HasDistributionalLaplacianDimensional Ω μ u.val f) :
    ‖h.val - u.val‖ ≤ C * Real.sqrt (1 + C ^ 2) * ‖Lh - f‖ :=
  estimacion320_dimensional Ω μ C hC hP h.val u.val Lh f
    (diferencia_mem_H01_de_traza Ω μ Tr hker h u ht) hh hu

#check lema319_constante_dada
#check lema319_dimensional
#check estimacion320_dimensional
#print axioms green_dimensional
#print axioms lema319_constante_dada
#print axioms lema319_dimensional
#print axioms laplaciano_dimensional_resta
#print axioms estimacion320_dimensional
#print axioms diferencia_mem_H01_de_traza
#check estimacion320_de_trazas_iguales
#print axioms estimacion320_de_trazas_iguales

end TesisPINN
