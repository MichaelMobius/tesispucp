import TesisPINN.BaseSenoCuadrado
import TesisPINN.ConstanteEspectralCuadrado

/-! Identidad de coeficientes para el laplaciano distribucional de Dirichlet. -/

noncomputable section

namespace TesisPINN

open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped RealInnerProductSpace

/-- Green contra un elemento arbitrario del cierre de las funciones de prueba. -/
theorem green_H01_bilineal (u v : H01 (volume : Measure Plano) cuadrado)
    (r : Lp ℝ 2 volumenPoisson) (hr : HasTestLaplacian u r) :
    inner ℝ (gradL (u : H1Graph volume cuadrado)) (gradL (v : H1Graph volume cuadrado)) =
      -(inner ℝ r (fnL (v : H1Graph volume cuadrado))) := by
  let F : H1Graph (volume : Measure Plano) cuadrado →L[ℝ] ℝ :=
    (innerSL ℝ (gradL (u : H1Graph volume cuadrado))).comp gradL +
      (innerSL ℝ r).comp fnL
  have hc : IsClosed {w : H1Graph volume cuadrado | F w = 0} :=
    isClosed_singleton.preimage F.continuous
  have ht : ∀ φ : testFunctions cuadrado,
      testGraphₗ volume cuadrado φ ∈ {w : H1Graph volume cuadrado | F w = 0} := by
    intro φ
    change inner ℝ (gradL (u : H1Graph volume cuadrado)) (gradCls volume cuadrado φ) +
      inner ℝ r (fnCls volume cuadrado φ) = 0
    rw [hr φ, neg_add_cancel]
  have h : F (v : H1Graph volume cuadrado) = 0 :=
    (H01_subset_of_isClosed hc ht) v.property
  change inner ℝ (gradL (u : H1Graph volume cuadrado)) (gradL (v : H1Graph volume cuadrado)) +
    inner ℝ r (fnL (v : H1Graph volume cuadrado)) = 0 at h
  exact eq_neg_of_add_eq_zero_left h

theorem laplacianoLp_modoSeno (p : ℕ × ℕ) :
    laplacianoLp (modoSeno p) (modoSeno_suave p) = (-autovalorSeno p) • modoSenoLp p := by
  apply Lp.ext
  filter_upwards [laplacianoLp_ae (modoSeno p) (modoSeno_suave p),
    Lp.coeFn_smul (-autovalorSeno p) (modoSenoLp p), grafoModoSeno_fnL_ae p] with x hx hy hz
  rw [hx, hy]
  change laplacianoClásico (modoSeno p) x =
    (-autovalorSeno p) * (fnL (grafoModoSeno p : H1Graph volume cuadrado)) x
  rw [hz]
  linarith only [modoSeno_ecuacion p x]

theorem modoSeno_laplaciano_distribucional (p : ℕ × ℕ) :
    HasDistributionalLaplacian cuadradoOpens volume (grafoModoSeno p)
      ((-autovalorSeno p) • modoSenoLp p) := by
  unfold HasDistributionalLaplacian
  rw [Distribution.ofFun_congr_ae (grafoModoSeno_fnL_ae p),
    laplaciano_distribucional_eq_laplacianoLp _ (modoSeno_suave p), laplacianoLp_modoSeno]
  rfl

/-- (3.79) y la identidad posterior para cada modo. El dato `r` representa
`Δe` y los coeficientes de la tesis se toman de `F = -r`. -/
theorem coeficiente_laplaciano_modoSeno
    (e : H01 (volume : Measure Plano) cuadrado) (r : Lp ℝ 2 volumenPoisson)
    (hr : HasDistributionalLaplacian cuadradoOpens volume e r) (p : ℕ × ℕ) :
    inner ℝ (-r) (modoSenoLp p) =
      autovalorSeno p * inner ℝ (fnL (e : H1Graph volume cuadrado)) (modoSenoLp p) := by
  have he := green_H01_bilineal e (grafoModoSeno p) r
    (laplaciano_distribucional_implica_prueba cuadradoOpens volume e r hr)
  have hm := green_H01_bilineal (grafoModoSeno p) e ((-autovalorSeno p) • modoSenoLp p)
    (laplaciano_distribucional_implica_prueba cuadradoOpens volume _ _
      (modoSeno_laplaciano_distribucional p))
  rw [real_inner_comm (gradL (e : H1Graph volume cuadrado))
    (gradL (grafoModoSeno p : H1Graph volume cuadrado))] at hm
  change _ = -(inner ℝ r (modoSenoLp p)) at he
  rw [he, real_inner_smul_left] at hm
  simpa only [inner_neg_left, neg_mul, neg_neg,
    real_inner_comm (fnL (e : H1Graph volume cuadrado)) (modoSenoLp p)] using hm

theorem autovalorSeno_inv_sq (p : ℕ × ℕ) :
    (autovalorSeno p)⁻¹ ^ 2 = (16 / Real.pi ^ 4) * terminoEspectral p := by
  unfold autovalorSeno terminoEspectral denominadorEspectral
  push_cast
  have hp := Real.pi_pos
  have hsum : (0 : ℝ) < ((p.1 : ℝ) + 1) ^ 2 + ((p.2 : ℝ) + 1) ^ 2 := by positivity
  field_simp [hp.ne', hsum.ne']
  ring

/-- El modo de índices físicos `(1,1)` tiene la menor frecuencia. -/
theorem autovalorSeno_minimo (p : ℕ × ℕ) :
    autovalorSeno (0, 0) = Real.pi ^ 2 / 2 ∧
      autovalorSeno (0, 0) ≤ autovalorSeno p := by
  have h1 : (0 : ℝ) ≤ (p.1 : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (p.2 : ℝ) := by positivity
  unfold autovalorSeno
  push_cast
  constructor
  · ring
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [sq_nonneg (p.1 : ℝ), sq_nonneg (p.2 : ℝ)]

/-- Caso de igualdad propuesto por la tesis para la cota óptima de Poincaré. -/
theorem energia_primer_modoSeno :
    ‖gradL (grafoModoSeno (0, 0) : H1Graph volume cuadrado)‖ ^ 2 = Real.pi ^ 2 / 2 := by
  have hm := green_H01_bilineal (grafoModoSeno (0, 0)) (grafoModoSeno (0, 0))
    ((-autovalorSeno (0, 0)) • modoSenoLp (0, 0))
    (laplaciano_distribucional_implica_prueba cuadradoOpens volume _ _
      (modoSeno_laplaciano_distribucional (0, 0)))
  change inner ℝ _ _ = -(inner ℝ ((-autovalorSeno (0, 0)) • modoSenoLp (0, 0))
    (modoSenoLp (0, 0))) at hm
  simpa only [real_inner_self_eq_norm_sq, real_inner_smul_left, modoSenoLp_norma,
    one_pow, mul_one, neg_neg, (autovalorSeno_minimo (0, 0)).1] using hm

#check coeficiente_laplaciano_modoSeno
#check energia_primer_modoSeno
#print axioms green_H01_bilineal
#print axioms modoSeno_laplaciano_distribucional
#print axioms coeficiente_laplaciano_modoSeno
#print axioms energia_primer_modoSeno

end TesisPINN
