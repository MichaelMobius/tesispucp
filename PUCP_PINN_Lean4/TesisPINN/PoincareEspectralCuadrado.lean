import TesisPINN.Proposicion322

/-! Constante óptima de Poincaré para el grafo con Dirichlet en el cuadrado. -/

noncomputable section

namespace TesisPINN

open MeasureTheory EllipticPdes EllipticPdes.H1Graph

private def gradienteModoNormalizado (p : ℕ × ℕ) : Lp Plano 2 volumenPoisson :=
  (Real.sqrt (autovalorSeno p))⁻¹ • gradL (grafoModoSeno p : H1Graph volume cuadrado)

private theorem inner_gradienteModoNormalizado (p : ℕ × ℕ)
    (e : H01 (volume : Measure Plano) cuadrado) :
    inner ℝ (gradienteModoNormalizado p) (gradL (e : H1Graph volume cuadrado)) =
      Real.sqrt (autovalorSeno p) * coefSeno (fnL (e : H1Graph volume cuadrado)) p := by
  have hg := green_H01_bilineal (grafoModoSeno p) e ((-autovalorSeno p) • modoSenoLp p)
    (laplaciano_distribucional_implica_prueba cuadradoOpens volume _ _
      (modoSeno_laplaciano_distribucional p))
  rw [gradienteModoNormalizado, real_inner_smul_left, hg, real_inner_smul_left, neg_mul, neg_neg]
  change (Real.sqrt (autovalorSeno p))⁻¹ * (autovalorSeno p * _) = _
  rw [← mul_assoc]
  congr 1
  have hp := Real.sqrt_pos.2 (autovalorSeno_pos p)
  apply (inv_mul_eq_iff_eq_mul₀ hp.ne').2
  exact (Real.sq_sqrt (autovalorSeno_pos p).le).symm.trans (pow_two _)

private theorem gradienteModoNormalizado_ortonormal :
    Orthonormal ℝ gradienteModoNormalizado := by
  classical
  rw [orthonormal_iff_ite]
  intro p q
  rw [show gradienteModoNormalizado q =
    (Real.sqrt (autovalorSeno q))⁻¹ • gradL (grafoModoSeno q : H1Graph volume cuadrado) from rfl,
    real_inner_smul_right, inner_gradienteModoNormalizado]
  change (Real.sqrt (autovalorSeno q))⁻¹ *
    (Real.sqrt (autovalorSeno p) * inner ℝ (modoSenoLp p) (modoSenoLp q)) = _
  rw [orthonormal_iff_ite.mp modoSenoLp_ortonormal]
  by_cases h : p = q
  · subst q
    simp [(Real.sqrt_pos.2 (autovalorSeno_pos p)).ne']
  · simp [h]

theorem poincare_cuadrado_espectral (e : H01 (volume : Measure Plano) cuadrado) :
    ‖fnL (e : H1Graph volume cuadrado)‖ ≤
      (Real.sqrt 2 / Real.pi) * ‖gradL (e : H1Graph volume cuadrado)‖ := by
  let z := fnL (e : H1Graph volume cuadrado)
  let g := gradL (e : H1Graph volume cuadrado)
  have h (s : Finset (ℕ × ℕ)) : ∑ p ∈ s, (Real.pi ^ 2 / 2) * |coefSeno z p| ^ 2 ≤ ‖g‖ ^ 2 := by
    calc
      _ ≤ ∑ p ∈ s, autovalorSeno p * |coefSeno z p| ^ 2 :=
        Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right
          ((autovalorSeno_minimo p).1 ▸ (autovalorSeno_minimo p).2) (sq_nonneg _)
      _ = ∑ p ∈ s, ‖inner ℝ (gradienteModoNormalizado p) g‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [inner_gradienteModoNormalizado, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (autovalorSeno_pos p).le]
      _ ≤ _ := gradienteModoNormalizado_ortonormal.sum_inner_products_le g
  have hb := Real.tsum_le_of_sum_le (fun p : ℕ × ℕ => by
    exact mul_nonneg (by positivity : 0 ≤ Real.pi ^ 2 / 2) (sq_nonneg |coefSeno z p|)) h
  rw [tsum_mul_left, modoSenoLp_parseval] at hb
  have hp := Real.pi_pos
  have hC : (Real.sqrt 2 / Real.pi) ^ 2 = 2 / Real.pi ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, hC]
  change ‖z‖ ^ 2 ≤ 2 / Real.pi ^ 2 * ‖g‖ ^ 2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hp)).2
  linarith

/-- Igualdad en el primer modo para la constante de (3.80). -/
theorem poincare_cuadrado_primer_modo :
    ‖modoSenoLp (0, 0)‖ = (Real.sqrt 2 / Real.pi) *
      ‖gradL (grafoModoSeno (0, 0) : H1Graph volume cuadrado)‖ := by
  have hp := Real.pi_pos
  rw [modoSenoLp_norma]
  apply (sq_eq_sq₀ zero_le_one (by positivity)).1
  rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num), energia_primer_modoSeno]
  field_simp [hp.ne']

/-- Toda constante válida en el cuadrado es al menos la de (3.80). -/
theorem poincare_cuadrado_constante_minima (C : ℝ)
    (hC : ∀ e : H01 (volume : Measure Plano) cuadrado,
      ‖fnL (e : H1Graph volume cuadrado)‖ ≤ C * ‖gradL (e : H1Graph volume cuadrado)‖) :
    Real.sqrt 2 / Real.pi ≤ C := by
  have hb := hC (grafoModoSeno (0, 0))
  change ‖modoSenoLp (0, 0)‖ ≤ _ at hb
  rw [poincare_cuadrado_primer_modo] at hb
  have hp : 0 < ‖gradL (grafoModoSeno (0, 0) : H1Graph volume cuadrado)‖ := by
    by_contra! h
    have hz := le_antisymm h (norm_nonneg _)
    have he := energia_primer_modoSeno
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at he
    exact (ne_of_gt (by positivity : 0 < Real.pi ^ 2 / 2)) he.symm
  exact le_of_mul_le_mul_right hb hp

/-- Estimación (3.81) para un error en el grafo de Dirichlet. -/
theorem energia_cuadrado_poincare_optima
    (e : H01 (volume : Measure Plano) cuadrado) (r : Lp ℝ 2 volumenPoisson)
    (hr : HasDistributionalLaplacian cuadradoOpens volume e r) :
    ‖(e : H1Graph volume cuadrado)‖ ≤
      (Real.sqrt 2 / Real.pi) * Real.sqrt (1 + 2 / Real.pi ^ 2) * ‖r‖ := by
  have htest := laplaciano_distribucional_implica_prueba cuadradoOpens volume e r hr
  have hEnergy := energia_norma_par_debil (Real.sqrt 2 / Real.pi)
    (fnL (e : H1Graph volume cuadrado)) r (gradL (e : H1Graph volume cuadrado))
    (div_pos (Real.sqrt_pos.2 (by norm_num)) Real.pi_pos)
    (green_por_densidad e r htest) (poincare_cuadrado_espectral e)
  change ‖mk (fnL (e : H1Graph volume cuadrado)) (gradL (e : H1Graph volume cuadrado))‖ ≤ _ at hEnergy
  rw [mk_fnL_gradL, div_pow, Real.sq_sqrt (by norm_num)] at hEnergy
  exact hEnergy

#check poincare_cuadrado_espectral
#check energia_cuadrado_poincare_optima
#print axioms poincare_cuadrado_espectral
#print axioms poincare_cuadrado_constante_minima
#print axioms energia_cuadrado_poincare_optima

end TesisPINN
