import TesisPINN.RecorteCuadradoH01
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Laplaciano clásico y residuo concreto en el cuadrado

La convención es `Δ = ∂₁² + ∂₂²`, como en el Lema 3.19 y el
Teorema 3.20 de la tesis. La identidad distribucional se deduce de
`hasWeakFDerivOn_fderiv` dos veces, sin axiomas nuevos.
-/

noncomputable section

open MeasureTheory TopologicalSpace EllipticPdes EllipticPdes.H1Graph
open scoped RealInnerProductSpace Distributions LineDeriv

namespace TesisPINN

/-- Derivada direccional clásica en un vector de la base ortonormal. -/
def derivadaClásica (f : Plano → ℝ) (i : Fin 2) (x : Plano) : ℝ :=
  fderiv ℝ f x (basePlano i)

/-- Laplaciano clásico como suma de segundas derivadas direccionales. -/
def laplacianoClásico (f : Plano → ℝ) (x : Plano) : ℝ :=
  ∑ i : Fin 2, fderiv ℝ (derivadaClásica f i) x (basePlano i)

private theorem derivadaClásica_suave (f : Plano → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (derivadaClásica f i) := by
  unfold derivadaClásica
  exact (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem laplacianoClásico_suave (f : Plano → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (laplacianoClásico f) := by
  unfold laplacianoClásico
  apply ContDiff.sum
  intro i hi
  exact ((derivadaClásica_suave f hf i).fderiv_right
    (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- La suma direccional coincide con el laplaciano clásico de Mathlib. -/
theorem laplacianoClásico_eq_mathlib (f : Plano → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    laplacianoClásico f = Laplacian.laplacian f := by
  have hD : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  funext x
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    f basePlano) x]
  unfold laplacianoClásico
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedFDeriv_two_apply]
  unfold derivadaClásica
  rw [fderiv_clm_apply (hD x) (differentiableAt_const (basePlano i))]
  simp

/-- Cada primera derivada distribucional coincide con la derivada clásica. -/
private theorem derivada_distribucional_clásica (f : Plano → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ∂_{basePlano i} (Distribution.ofFun cuadradoOpens f volume ⊤) =
      Distribution.ofFun cuadradoOpens (derivadaClásica f i) volume ⊤ := by
  exact (hasWeakFDerivOn_fderiv (μ := volume) (Ω := cuadradoOpens)
    (u := f) (hf.contDiffOn.of_le (by simp)) (basePlano i)).2.2

/-- La segunda derivada distribucional tiene el representante clásico. -/
private theorem segunda_distribucional_clásica (f : Plano → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ∂_{basePlano i} (∂_{basePlano i}
      (Distribution.ofFun cuadradoOpens f volume ⊤)) =
      Distribution.ofFun cuadradoOpens
        (fun x => fderiv ℝ (derivadaClásica f i) x (basePlano i)) volume ⊤ := by
  rw [derivada_distribucional_clásica f hf i]
  exact (hasWeakFDerivOn_fderiv (μ := volume) (Ω := cuadradoOpens)
    (u := derivadaClásica f i)
    ((derivadaClásica_suave f hf i).contDiffOn.of_le (by simp))
    (basePlano i)).2.2

theorem laplaciano_distribucional_eq_clásico (f : Plano → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens f volume ⊤) =
      Distribution.ofFun cuadradoOpens (laplacianoClásico f) volume ⊤ := by
  rw [laplacianoDistribucional_eq_suma]
  simp_rw [segunda_distribucional_clásica f hf]
  simp only [Fin.sum_univ_two]
  rw [← Distribution.ofFun_add]
  · congr 1
    funext x
    simp [laplacianoClásico, Fin.sum_univ_two, Pi.add_apply]
  · exact ((derivadaClásica_suave f hf 0).fderiv_right
      (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const |>.continuous.continuousOn.locallyIntegrableOn
      cuadrado_abierto.measurableSet
  · exact ((derivadaClásica_suave f hf 1).fderiv_right
      (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const |>.continuous.continuousOn.locallyIntegrableOn
      cuadrado_abierto.measurableSet

private theorem cuadrado_medida_finita :
    IsFiniteMeasure ((volume : Measure Plano).restrict cuadrado) := by
  rw [isFiniteMeasure_restrict]
  have hbox : cuadrado = EllipticPdes.Analysis.FrechetKolmogorov.dbox (n := 2) 1 := by
    ext x
    simp [cuadrado, EllipticPdes.Poincare.euclBox,
      EllipticPdes.Analysis.FrechetKolmogorov.mem_dbox]
  rw [hbox]
  exact EllipticPdes.Analysis.FrechetKolmogorov.volume_dbox_ne_top 1

/-- La continuidad del laplaciano clásico en el cuadrado cerrado da `L²(U)`. -/
theorem laplacianoClásico_memLp (f : Plano → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    MemLp (laplacianoClásico f) 2 ((volume : Measure Plano).restrict cuadrado) := by
  letI : IsFiniteMeasure ((volume : Measure Plano).restrict cuadrado) :=
    cuadrado_medida_finita
  have hc : Continuous (laplacianoClásico f) := (laplacianoClásico_suave f hf).continuous
  obtain ⟨M, hM⟩ := cuadrado_acotado.isCompact_closure.exists_bound_of_continuousOn
    hc.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem cuadrado_abierto.measurableSet] with x hx
  exact hM x (subset_closure hx)

/-- Clase `L²` canónica del laplaciano clásico. -/
def laplacianoLp (f : Plano → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado) :=
  (laplacianoClásico_memLp f hf).toLp (laplacianoClásico f)

theorem laplacianoLp_ae (f : Plano → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ⇑(laplacianoLp f hf) =ᵐ[((volume : Measure Plano).restrict cuadrado)]
      laplacianoClásico f :=
  (laplacianoClásico_memLp f hf).coeFn_toLp

theorem laplaciano_distribucional_eq_laplacianoLp (f : Plano → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens f volume ⊤) =
      Distribution.ofFun cuadradoOpens (laplacianoLp f hf) volume ⊤ := by
  rw [laplaciano_distribucional_eq_clásico f hf]
  exact Distribution.ofFun_congr_ae (laplacianoLp_ae f hf).symm

/-- Diferencia clásica de dos candidatos de Dirichlet exacto. -/
def errorPsi (qh qu : Plano → ℝ) (x : Plano) : ℝ :=
  psiCuadrado x * qh x - psiCuadrado x * qu x

theorem errorPsi_suave (qh qu : Plano → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) qh) (hu : ContDiff ℝ (⊤ : ℕ∞) qu) :
    ContDiff ℝ (⊤ : ℕ∞) (errorPsi qh qu) :=
  (psiCuadrado_suave.mul hh).sub (psiCuadrado_suave.mul hu)

/-- Residuo concreto `r = Δ(ψqh - ψqu)` en `L²(U)`. -/
def residuoPsi (qh qu : Plano → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) qh) (hu : ContDiff ℝ (⊤ : ℕ∞) qu) :
    Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado) :=
  laplacianoLp (errorPsi qh qu) (errorPsi_suave qh qu hh hu)

theorem residuoPsi_ae (qh qu : Plano → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) qh) (hu : ContDiff ℝ (⊤ : ℕ∞) qu) :
    ⇑(residuoPsi qh qu hh hu) =ᵐ[((volume : Measure Plano).restrict cuadrado)]
      laplacianoClásico (errorPsi qh qu) :=
  laplacianoLp_ae _ _

private theorem fnL_errorPsi_ae (qh qu : Plano → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) qh) (hu : ContDiff ℝ (⊤ : ℕ∞) qu) :
    ⇑(fnL (psiGraph qh hh - psiGraph qu hu))
      =ᵐ[((volume : Measure Plano).restrict cuadrado)] errorPsi qh qu := by
  have h := (Lp.coeFn_sub (fnL (psiGraph qh hh)) (fnL (psiGraph qu hu))).trans
    ((psiGraph_fnL_ae qh hh).sub (psiGraph_fnL_ae qu hu))
  have heq : ((fun x => psiCuadrado x * qh x) -
      (fun x => psiCuadrado x * qu x)) = errorPsi qh qu := by
    ext x
    simp [errorPsi]
  simpa only [map_sub, heq] using h

theorem laplaciano_distribucional_errorPsi (qh qu : Plano → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) qh) (hu : ContDiff ℝ (⊤ : ℕ∞) qu) :
    laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens
        (fnL (psiGraph qh hh - psiGraph qu hu)) volume ⊤) =
      Distribution.ofFun cuadradoOpens (residuoPsi qh qu hh hu) volume ⊤ := by
  rw [Distribution.ofFun_congr_ae (fnL_errorPsi_ae qh qu hh hu)]
  exact laplaciano_distribucional_eq_laplacianoLp
    (errorPsi qh qu) (errorPsi_suave qh qu hh hu)

/-- Estimación energética sin premisas `hΔ` ni `he` para dos candidatos `ψq` suaves. -/
theorem estimacion_psi_suave_residuo_concreto (qh qu : Plano → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) qh) (hu : ContDiff ℝ (⊤ : ℕ∞) qu) :
    ∃ Cₚ : ℝ, 0 < Cₚ ∧
      ‖psiGraph qh hh - psiGraph qu hu‖ ≤
        Cₚ * Real.sqrt (1 + Cₚ ^ 2) * ‖residuoPsi qh qu hh hu‖ := by
  exact estimacion_psi_suave_dirichlet_exacto qh qu hh hu
    (residuoPsi qh qu hh hu) (laplaciano_distribucional_errorPsi qh qu hh hu)

/-- `Distribution.ofFun` respeta la resta de clases `L²`. -/
private theorem ofFun_lp_sub
    (a b : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado)) :
    Distribution.ofFun cuadradoOpens (a - b) volume ⊤ =
      Distribution.ofFun cuadradoOpens a volume ⊤ -
        Distribution.ofFun cuadradoOpens b volume ⊤ := by
  calc
    Distribution.ofFun cuadradoOpens (a - b) volume ⊤ =
        Distribution.ofFun cuadradoOpens ((a : Plano → ℝ) - (b : Plano → ℝ)) volume ⊤ :=
      Distribution.ofFun_congr_ae (Lp.coeFn_sub a b)
    _ = Distribution.ofFun cuadradoOpens a volume ⊤ -
        Distribution.ofFun cuadradoOpens b volume ⊤ := by
      rw [sub_eq_add_neg, Distribution.ofFun_add
        (locallyIntegrableOn_lp a) (locallyIntegrableOn_lp b).neg,
        Distribution.ofFun_neg]
      rfl

/-- Para `u*` general, la ecuación `Δu*=f` da el residuo `Δ(ψq)-f`.
La pertenencia de `u*` a `H₀¹` sigue siendo una hipótesis explícita. -/
theorem estimacion_psi_frente_solucion_exacta
    (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens f volume ⊤) :
    ∃ Cₚ : ℝ, 0 < Cₚ ∧
      ‖psiGraph q hq - u‖ ≤ Cₚ * Real.sqrt (1 + Cₚ ^ 2) *
        ‖laplacianoLp (fun x => psiCuadrado x * q x)
          (psiCuadrado_suave.mul hq) - f‖ := by
  let rh := laplacianoLp (fun x => psiCuadrado x * q x) (psiCuadrado_suave.mul hq) - f
  apply estimacion_error_dirichlet_exacto (psiGraph q hq) u rh
    (Submodule.sub_mem _ (psiGraph_mem_H01 q hq) hu)
  rw [map_sub, ofFun_lp_sub, map_sub]
  rw [Distribution.ofFun_congr_ae (psiGraph_fnL_ae q hq)]
  rw [laplaciano_distribucional_eq_laplacianoLp
    (fun x => psiCuadrado x * q x) (psiCuadrado_suave.mul hq), hsol]
  exact (ofFun_lp_sub _ _).symm

#print axioms TesisPINN.laplacianoClásico_eq_mathlib
#print axioms TesisPINN.laplaciano_distribucional_eq_clásico
#print axioms TesisPINN.laplacianoClásico_memLp
#print axioms TesisPINN.laplaciano_distribucional_errorPsi
#print axioms TesisPINN.estimacion_psi_suave_residuo_concreto
#print axioms TesisPINN.estimacion_psi_frente_solucion_exacta

end TesisPINN
