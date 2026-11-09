import TesisPINN.RecorteCuadrado
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Aproximación Sobolev de `ψ q` en el cuadrado

El recorte interior converge en las clases `L²` de valor y gradiente por
integrabilidad uniforme en el cuadrado de medida finita. La cota uniforme del
gradiente usa la anulación lineal de `ψ` en la franja de transición.
-/

noncomputable section
open MeasureTheory Filter Topology


namespace TesisPINN

private theorem norm_gradient_eq (f : Plano → ℝ) (x : Plano) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  simp [gradient]

private theorem cuadrado_finite : IsFiniteMeasure ((volume : Measure Plano).restrict cuadrado) := by
  rw [isFiniteMeasure_restrict]
  have hbox : cuadrado = EllipticPdes.Analysis.FrechetKolmogorov.dbox (n := 2) 1 := by
    ext x
    simp [cuadrado, EllipticPdes.Poincare.euclBox,
      EllipticPdes.Analysis.FrechetKolmogorov.mem_dbox]
  rw [hbox]
  exact EllipticPdes.Analysis.FrechetKolmogorov.volume_dbox_ne_top 1

private theorem convergencia_l2_de_cota_uniforme {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → Plano → E) (g : Plano → E) (M : ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) ((volume : Measure Plano).restrict cuadrado))
    (hg : AEStronglyMeasurable g ((volume : Measure Plano).restrict cuadrado))
    (hM : 0 ≤ M)
    (hbound : ∀ n, ∀ x ∈ cuadrado, ‖f n x‖ ≤ M)
    (hgbound : ∀ x ∈ cuadrado, ‖g x‖ ≤ M)
    (heq : ∀ x ∈ cuadrado, ∀ᶠ n in atTop, f n x = g x) :
    Tendsto (fun n => eLpNorm (f n - g) 2 ((volume : Measure Plano).restrict cuadrado))
      atTop (𝓝 0) := by
  letI : IsFiniteMeasure ((volume : Measure Plano).restrict cuadrado) := cuadrado_finite
  have hmem : MemLp g 2 ((volume : Measure Plano).restrict cuadrado) :=
    MemLp.of_bound hg M ((ae_restrict_mem cuadrado_abierto.measurableSet).mono fun x hx => hgbound x hx)
  have hui : UnifIntegrable f 2 ((volume : Measure Plano).restrict cuadrado) := by
    apply unifIntegrable_of (by norm_num) (by norm_num) hf
    intro ε hε
    let C : NNReal := ⟨M + 1, by positivity⟩
    refine ⟨C, ?_⟩
    intro n
    have hz : ({x | C ≤ ‖f n x‖₊}.indicator (f n))
        =ᵐ[((volume : Measure Plano).restrict cuadrado)] (fun _ => 0) := by
      filter_upwards [ae_restrict_mem cuadrado_abierto.measurableSet] with x hx
      have hb := hbound n x hx
      simp only [Set.indicator, Set.mem_ofPred_eq]
      split_ifs with hh
      · have hh' : M + 1 ≤ ‖f n x‖ := by exact_mod_cast hh
        linarith
      · rfl
    rw [eLpNorm_congr_ae hz]
    simpa using hε.le
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hf hmem hui
  filter_upwards [ae_restrict_mem cuadrado_abierto.measurableSet] with x hx
  exact (show (fun n => f n x) =ᶠ[atTop] (fun _ => g x) from heq x hx).tendsto

end TesisPINN

namespace TesisPINN

open EllipticPdes EllipticPdes.H1Graph

private theorem psi_memLp (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    MemLp (fun x => psiCuadrado x * q x) 2 ((volume : Measure Plano).restrict cuadrado) := by
  letI : IsFiniteMeasure ((volume : Measure Plano).restrict cuadrado) := cuadrado_finite
  obtain ⟨M, hM0, hM⟩ := existe_cota_q_y_deriv_psi_q q hq
  apply MemLp.of_bound ((psiCuadrado_suave.mul hq).continuous.aestronglyMeasurable) M
  filter_upwards [ae_restrict_mem cuadrado_abierto.measurableSet] with x hx
  obtain ⟨hψ0, hψ1⟩ := psiCuadrado_no_neg_le_uno hx
  have hqM := (hM x hx).1
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hψ0]
  nlinarith [mul_nonneg (sub_nonneg.mpr hψ1) (norm_nonneg (q x)),
    mul_nonneg hψ0 (sub_nonneg.mpr hqM)]

private theorem psi_grad_memLp (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    MemLp (gradient (fun x => psiCuadrado x * q x)) 2
      ((volume : Measure Plano).restrict cuadrado) := by
  letI : IsFiniteMeasure ((volume : Measure Plano).restrict cuadrado) := cuadrado_finite
  obtain ⟨M, hM0, hM⟩ := existe_cota_q_y_deriv_psi_q q hq
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun x => psiCuadrado x * q x) :=
    psiCuadrado_suave.mul hq
  have hcont : Continuous (gradient (fun x => psiCuadrado x * q x)) := by
    change Continuous (fun x => (InnerProductSpace.toDual ℝ Plano).symm
      (fderiv ℝ (fun y => psiCuadrado y * q y) x))
    exact (InnerProductSpace.toDual ℝ Plano).symm.continuous.comp
      (he.continuous_fderiv (by simp))
  apply MemLp.of_bound hcont.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem cuadrado_abierto.measurableSet] with x hx
  rw [norm_gradient_eq]
  exact (hM x hx).2
def psiGraph (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    H1Graph (volume : Measure Plano) cuadrado :=
  H1Graph.mk (psi_memLp q hq).toLp (psi_grad_memLp q hq).toLp

theorem psiGraph_fnL_ae (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ⇑(fnL (psiGraph q hq)) =ᵐ[((volume : Measure Plano).restrict cuadrado)]
      (fun x => psiCuadrado x * q x) :=
  (psi_memLp q hq).coeFn_toLp

theorem psiGraph_gradL_ae (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ⇑(gradL (psiGraph q hq)) =ᵐ[((volume : Measure Plano).restrict cuadrado)]
      gradient (fun x => psiCuadrado x * q x) :=
  (psi_grad_memLp q hq).coeFn_toLp

theorem recortePsi_tendsto_fnL (q : Plano → ℝ)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    Tendsto (fun n => fnL (testGraphₗ volume cuadrado
      (recortePsiPrueba (ancho_pos n) q hq))) atTop (𝓝 (fnL (psiGraph q hq))) := by
  obtain ⟨M, hM0, hM⟩ := existe_cota_q_y_deriv_psi_q q hq
  let f : ℕ → Plano → ℝ := fun n x =>
    (recortePsiPrueba (ancho_pos n) q hq : Plano → ℝ) x
  let g : Plano → ℝ := fun x => psiCuadrado x * q x
  have hf : ∀ n, AEStronglyMeasurable (f n) ((volume : Measure Plano).restrict cuadrado) := by
    intro n
    exact (recortePsiPrueba (ancho_pos n) q hq).2.1.continuous.aestronglyMeasurable
  have hg : AEStronglyMeasurable g ((volume : Measure Plano).restrict cuadrado) :=
    (psiCuadrado_suave.mul hq).continuous.aestronglyMeasurable
  have hb : ∀ n, ∀ x ∈ cuadrado, ‖f n x‖ ≤ M := by
    intro n x hx
    obtain ⟨hψ0, hψ1⟩ := psiCuadrado_no_neg_le_uno hx
    have hχ0 := recorte_no_neg (ancho n) x
    have hχ1 := recorte_le_uno (ancho n) x
    have hqM := (hM x hx).1
    change ‖recorte (ancho n) x * (psiCuadrado x * q x)‖ ≤ M
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hχ0, abs_of_nonneg hψ0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hχ1) (mul_nonneg hψ0 (norm_nonneg (q x))),
      mul_nonneg hχ0 (mul_nonneg (sub_nonneg.mpr hψ1) (norm_nonneg (q x))),
      mul_nonneg (mul_nonneg hχ0 hψ0) (sub_nonneg.mpr hqM)]
  have hgb : ∀ x ∈ cuadrado, ‖g x‖ ≤ M := by
    intro x hx
    obtain ⟨hψ0, hψ1⟩ := psiCuadrado_no_neg_le_uno hx
    have hqM := (hM x hx).1
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hψ0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hψ1) (norm_nonneg (q x)),
      mul_nonneg hψ0 (sub_nonneg.mpr hqM)]
  have heq : ∀ x ∈ cuadrado, ∀ᶠ n in atTop, f n x = g x := by
    intro x hx
    filter_upwards [eventualmente_recortePsi_valor_y_gradiente q hq hx] with n hn
    exact hn.1
  have hconv := convergencia_l2_de_cota_uniforme f g M hf hg hM0 hb hgb heq
  have hfm : ∀ n, MemLp (f n) 2 ((volume : Measure Plano).restrict cuadrado) := by
    intro n
    exact EllipticPdes.memLp_of_mem
      (recortePsiPrueba (ancho_pos n) q hq).2
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hfm g (psi_memLp q hq)).2 hconv
  convert hLp using 1
  · ext n
    rfl
  · rfl

theorem recortePsi_tendsto_gradL (q : Plano → ℝ)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    Tendsto (fun n => gradL (testGraphₗ volume cuadrado
      (recortePsiPrueba (ancho_pos n) q hq))) atTop (𝓝 (gradL (psiGraph q hq))) := by
  obtain ⟨M, hM0, hM⟩ := existe_cota_q_y_deriv_psi_q q hq
  obtain ⟨C, hC0, hC⟩ := EllipticPdes.Extension.exists_bound_deriv_smoothTransition
  let f : ℕ → Plano → Plano := fun n x =>
    gradient (recortePsiPrueba (ancho_pos n) q hq : Plano → ℝ) x
  let g : Plano → Plano := gradient (fun x => psiCuadrado x * q x)
  have hf : ∀ n, AEStronglyMeasurable (f n) ((volume : Measure Plano).restrict cuadrado) := by
    intro n
    exact (EllipticPdes.continuous_gradient_of_mem
      (recortePsiPrueba (ancho_pos n) q hq).2).aestronglyMeasurable
  have hg : AEStronglyMeasurable g ((volume : Measure Plano).restrict cuadrado) :=
    (psi_grad_memLp q hq).aestronglyMeasurable
  have hb : ∀ n, ∀ x ∈ cuadrado, ‖f n x‖ ≤ M + 16 * C * M := by
    intro n x hx
    rw [norm_gradient_eq]
    exact norm_fderiv_recortePsi_le (ancho_pos n) hC hM0 q hq hx
      (hM x hx).1 (hM x hx).2
  have hgb : ∀ x ∈ cuadrado, ‖g x‖ ≤ M + 16 * C * M := by
    intro x hx
    rw [norm_gradient_eq]
    have hbase := (hM x hx).2
    nlinarith [mul_nonneg hC0 hM0]
  have heq : ∀ x ∈ cuadrado, ∀ᶠ n in atTop, f n x = g x := by
    intro x hx
    filter_upwards [eventualmente_recortePsi_valor_y_gradiente q hq hx] with n hn
    exact hn.2
  have hM' : 0 ≤ M + 16 * C * M := by positivity
  have hconv := convergencia_l2_de_cota_uniforme f g (M + 16 * C * M)
    hf hg hM' hb hgb heq
  have hfm : ∀ n, MemLp (f n) 2 ((volume : Measure Plano).restrict cuadrado) := by
    intro n
    exact EllipticPdes.memLp_gradient_of_mem
      (recortePsiPrueba (ancho_pos n) q hq).2
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hfm g (psi_grad_memLp q hq)).2 hconv
  convert hLp using 1
  · ext n
    rfl
  · rfl

theorem psiGraph_mem_H01 (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    psiGraph q hq ∈ H01 (volume : Measure Plano) cuadrado := by
  exact mem_H01_de_aproximacion_l2 (psiGraph q hq)
    (fun n => recortePsiPrueba (ancho_pos n) q hq)
    (recortePsi_tendsto_fnL q hq) (recortePsi_tendsto_gradL q hq)

/-- Estimación determinista para dos candidatos suaves de Dirichlet exacto.
La identidad del residuo distribucional permanece como hipótesis explícita. -/
theorem estimacion_psi_suave_dirichlet_exacto
    (qh qu : Plano → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) qh) (hu : ContDiff ℝ (⊤ : ℕ∞) qu)
    (r : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (hΔ : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens
        (fnL (psiGraph qh hh - psiGraph qu hu)) volume ⊤) =
      Distribution.ofFun cuadradoOpens r volume ⊤) :
    ∃ Cₚ : ℝ, 0 < Cₚ ∧
      ‖psiGraph qh hh - psiGraph qu hu‖ ≤
        Cₚ * Real.sqrt (1 + Cₚ ^ 2) * ‖r‖ := by
  exact estimacion_error_dirichlet_exacto _ _ r
    (Submodule.sub_mem _ (psiGraph_mem_H01 qh hh) (psiGraph_mem_H01 qu hu)) hΔ

#print axioms TesisPINN.convergencia_l2_de_cota_uniforme
#print axioms TesisPINN.recortePsi_tendsto_fnL
#print axioms TesisPINN.recortePsi_tendsto_gradL
#print axioms TesisPINN.psiGraph_fnL_ae
#print axioms TesisPINN.psiGraph_gradL_ae
#print axioms TesisPINN.psiGraph_mem_H01
#print axioms TesisPINN.estimacion_psi_suave_dirichlet_exacto

end TesisPINN

