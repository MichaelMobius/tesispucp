import TesisPINN.DirichletCuadrado
import EllipticPdes.Extension.Cutoff
import EllipticPdes.Analysis.FrechetKolmogorov
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Recortes interiores del cuadrado

`lado δ t` vale cero a distancia menor o igual que `δ` de la cara izquierda
del intervalo `(-1,1)` y uno a distancia al menos `2δ`. El producto de las
cuatro caras da un recorte suave del cuadrado.
-/

noncomputable section

open MeasureTheory TopologicalSpace Topology Filter Set EllipticPdes EllipticPdes.H1Graph
open scoped RealInnerProductSpace

namespace TesisPINN

private theorem cuadrado_eq_dbox :
    cuadrado = EllipticPdes.Analysis.FrechetKolmogorov.dbox (n := 2) 1 := by
  ext x
  simp [cuadrado, EllipticPdes.Poincare.euclBox,
    EllipticPdes.Analysis.FrechetKolmogorov.mem_dbox]

/-- Perfil suave de la cara `t=-1`. -/
def lado (δ t : ℝ) : ℝ := Real.smoothTransition ((t + 1) / δ - 1)

theorem lado_suave (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (lado δ) := by
  unfold lado
  exact EllipticPdes.Extension.contDiff_smoothTransition.comp
    ((contDiff_id.add contDiff_const).div_const δ |>.sub contDiff_const)

theorem lado_no_neg (δ t : ℝ) : 0 ≤ lado δ t := by
  exact Real.smoothTransition.nonneg _

theorem lado_le_uno (δ t : ℝ) : lado δ t ≤ 1 := by
  exact Real.smoothTransition.le_one _

theorem lado_cero {δ t : ℝ} (hδ : 0 < δ) (ht : t + 1 ≤ δ) : lado δ t = 0 := by
  unfold lado
  exact Real.smoothTransition.zero_of_nonpos (by rw [sub_nonpos, div_le_one hδ]; exact ht)

theorem lado_uno {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ ≤ t + 1) :
    lado δ t = 1 := by
  unfold lado
  exact Real.smoothTransition.one_of_one_le (by rw [le_sub_iff_add_le, le_div_iff₀ hδ]; linarith)

theorem deriv_lado (δ t : ℝ) :
    deriv (lado δ) t = deriv Real.smoothTransition ((t + 1) / δ - 1) / δ := by
  have hinner : HasDerivAt (fun s : ℝ => (s + 1) / δ - 1) (1 / δ) t := by
    convert (((hasDerivAt_id t).add_const 1).div_const δ).sub_const 1 using 1
    · funext s; simp only [id_eq]
  have houter : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((t + 1) / δ - 1)) ((t + 1) / δ - 1) :=
    (EllipticPdes.Extension.contDiff_smoothTransition.differentiable (by simp) _).hasDerivAt
  convert (houter.comp t hinner).deriv using 1
  · rfl
  · ring

/-- La derivada de una pared es de orden `1/δ`. -/
theorem abs_deriv_lado_le {δ C : ℝ} (hδ : 0 < δ)
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) (t : ℝ) :
    |deriv (lado δ) t| ≤ C / δ := by
  rw [deriv_lado, abs_div, abs_of_pos hδ]
  exact div_le_div_of_nonneg_right (hC _) hδ.le

/-- Perfil de las dos caras de un intervalo. -/
def perfil (δ t : ℝ) : ℝ := lado δ t * lado δ (-t)

theorem perfil_suave (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (perfil δ) := by
  unfold perfil
  exact (lado_suave δ).mul ((lado_suave δ).comp contDiff_neg)

theorem abs_deriv_perfil_le {δ C : ℝ} (hδ : 0 < δ)
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) (t : ℝ) :
    |deriv (perfil δ) t| ≤ 2 * C / δ := by
  have hA : DifferentiableAt ℝ (lado δ) t :=
    (lado_suave δ).differentiable (by simp) t
  have hneg : DifferentiableAt ℝ (fun s : ℝ => -s) t := by fun_prop
  have hB : DifferentiableAt ℝ (fun s => lado δ (-s)) t :=
    ((lado_suave δ).differentiable (by simp) (-t)).comp t hneg
  have hdB : deriv (fun s => lado δ (-s)) t = -deriv (lado δ) (-t) := by
    change deriv ((lado δ) ∘ fun s : ℝ => -s) t = _
    rw [deriv_comp t ((lado_suave δ).differentiable (by simp) (-t)) hneg]
    simp
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  change |deriv (fun s => lado δ s * lado δ (-s)) t| ≤ 2 * C / δ
  rw [deriv_fun_mul hA hB, hdB]
  calc
    |deriv (lado δ) t * lado δ (-t) + lado δ t * -deriv (lado δ) (-t)|
        ≤ |deriv (lado δ) t| * |lado δ (-t)| +
          |lado δ t| * |deriv (lado δ) (-t)| := by
            grw [abs_add_le, abs_mul, abs_mul, abs_neg]
    _ ≤ (C / δ) * 1 + 1 * (C / δ) := by
      gcongr
      · exact abs_deriv_lado_le hδ hC t
      · rw [abs_of_nonneg (lado_no_neg δ (-t))]; exact lado_le_uno δ (-t)
      · rw [abs_of_nonneg (lado_no_neg δ t)]; exact lado_le_uno δ t
      · exact abs_deriv_lado_le hδ hC (-t)
    _ = 2 * C / δ := by ring

/-- Producto de los cuatro perfiles de pared. -/
def recorte (δ : ℝ) (x : Plano) : ℝ :=
  lado δ (x 0) * lado δ (-(x 0)) * lado δ (x 1) * lado δ (-(x 1))

theorem recorte_eq_perfil (δ : ℝ) (x : Plano) :
    recorte δ x = perfil δ (x 0) * perfil δ (x 1) := by
  simp only [recorte, perfil]
  ring

theorem perfil_no_neg (δ t : ℝ) : 0 ≤ perfil δ t :=
  mul_nonneg (lado_no_neg δ t) (lado_no_neg δ (-t))

theorem perfil_le_uno (δ t : ℝ) : perfil δ t ≤ 1 := by
  unfold perfil
  have h₀ := lado_no_neg δ t
  have h₁ := lado_no_neg δ (-t)
  have H₀ := lado_le_uno δ t
  have H₁ := lado_le_uno δ (-t)
  nlinarith [mul_nonneg h₀ (sub_nonneg.mpr H₁)]

theorem fderiv_recorte_formula (δ : ℝ) (x w : Plano) :
    fderiv ℝ (recorte δ) x w =
      deriv (perfil δ) (x 0) * w 0 * perfil δ (x 1) +
        perfil δ (x 0) * (deriv (perfil δ) (x 1) * w 1) := by
  let p₀ : Plano →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p₁ : Plano →L[ℝ] ℝ := EuclideanSpace.proj 1
  have h₀ : HasFDerivAt (fun y : Plano => perfil δ (y 0))
      ((deriv (perfil δ) (x 0)) • p₀) x := by
    convert ((perfil_suave δ).differentiable (by simp) (x 0)).hasDerivAt.comp_hasFDerivAt
      x p₀.hasFDerivAt using 1
    funext y
    rfl
  have h₁ : HasFDerivAt (fun y : Plano => perfil δ (y 1))
      ((deriv (perfil δ) (x 1)) • p₁) x := by
    convert ((perfil_suave δ).differentiable (by simp) (x 1)).hasDerivAt.comp_hasFDerivAt
      x p₁.hasFDerivAt using 1
    funext y
    rfl
  have h := (h₀.mul h₁).fderiv
  have hp := congrArg (fun L : Plano →L[ℝ] ℝ => L w) h
  have hr : recorte δ = fun y : Plano => perfil δ (y 0) * perfil δ (y 1) := by
    funext y
    exact recorte_eq_perfil δ y
  rw [hr]
  change (fderiv ℝ (fun y : Plano => perfil δ (y 0) * perfil δ (y 1)) x) w = _ at hp
  rw [hp]
  simp [p₀, p₁, smul_eq_mul]
  ring

/-- Cota direccional para el recorte de las cuatro caras. -/
theorem abs_fderiv_recorte_le {δ C : ℝ} (hδ : 0 < δ)
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) (x w : Plano) :
    |fderiv ℝ (recorte δ) x w| ≤
      (2 * C / δ) * (|w 0| + |w 1|) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hD : 0 ≤ 2 * C / δ := div_nonneg (by positivity) hδ.le
  rw [fderiv_recorte_formula]
  calc
    |deriv (perfil δ) (x 0) * w 0 * perfil δ (x 1) +
        perfil δ (x 0) * (deriv (perfil δ) (x 1) * w 1)|
      ≤ |deriv (perfil δ) (x 0)| * |w 0| * |perfil δ (x 1)| +
        |perfil δ (x 0)| * (|deriv (perfil δ) (x 1)| * |w 1|) := by
          grw [abs_add_le, abs_mul, abs_mul, abs_mul, abs_mul]
    _ ≤ (2 * C / δ) * |w 0| * 1 +
        1 * ((2 * C / δ) * |w 1|) := by
          gcongr
          · exact abs_deriv_perfil_le hδ hC (x 0)
          · rw [abs_of_nonneg (perfil_no_neg δ (x 1))]; exact perfil_le_uno δ (x 1)
          · rw [abs_of_nonneg (perfil_no_neg δ (x 0))]; exact perfil_le_uno δ (x 0)
          · exact abs_deriv_perfil_le hδ hC (x 1)
    _ = (2 * C / δ) * (|w 0| + |w 1|) := by ring

theorem abs_fderiv_recorte_le_norm {δ C : ℝ} (hδ : 0 < δ)
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) (x w : Plano) :
    |fderiv ℝ (recorte δ) x w| ≤ (4 * C / δ) * ‖w‖ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hD : 0 ≤ 2 * C / δ := div_nonneg (by positivity) hδ.le
  have hw0 : |w 0| ≤ ‖w‖ := by simpa using PiLp.norm_apply_le w 0
  have hw1 : |w 1| ≤ ‖w‖ := by simpa using PiLp.norm_apply_le w 1
  calc
    |fderiv ℝ (recorte δ) x w| ≤ (2 * C / δ) * (|w 0| + |w 1|) :=
      abs_fderiv_recorte_le hδ hC x w
    _ ≤ (2 * C / δ) * (2 * ‖w‖) := by gcongr; linarith
    _ = (4 * C / δ) * ‖w‖ := by ring

theorem recorte_suave (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (recorte δ) := by
  unfold recorte
  have h₀ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plano => x 0) := by fun_prop
  have h₁ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plano => x 1) := by fun_prop
  exact ((((lado_suave δ).comp h₀).mul ((lado_suave δ).comp h₀.neg)).mul
    ((lado_suave δ).comp h₁)).mul ((lado_suave δ).comp h₁.neg)

theorem recorte_no_neg (δ : ℝ) (x : Plano) : 0 ≤ recorte δ x := by
  unfold recorte
  exact mul_nonneg (mul_nonneg (mul_nonneg (lado_no_neg _ _) (lado_no_neg _ _))
    (lado_no_neg _ _)) (lado_no_neg _ _)

theorem recorte_le_uno (δ : ℝ) (x : Plano) : recorte δ x ≤ 1 := by
  unfold recorte
  have h₀ := lado_no_neg δ (x 0)
  have h₁ := lado_no_neg δ (-(x 0))
  have h₂ := lado_no_neg δ (x 1)
  have h₃ := lado_no_neg δ (-(x 1))
  have H₀ := lado_le_uno δ (x 0)
  have H₁ := lado_le_uno δ (-(x 0))
  have H₂ := lado_le_uno δ (x 1)
  have H₃ := lado_le_uno δ (-(x 1))
  calc
    lado δ (x 0) * lado δ (-(x 0)) * lado δ (x 1) * lado δ (-(x 1))
        ≤ 1 * 1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

/-- El cuadrado cerrado que contiene el soporte del recorte. -/
def cuadradoInteriorCerrado (δ : ℝ) : Set Plano :=
  {x | ∀ i : Fin 2, x i ∈ Icc (-1 + δ) (1 - δ)}

theorem cuadradoInteriorCerrado_cerrado (δ : ℝ) :
    IsClosed (cuadradoInteriorCerrado δ) := by
  have h : cuadradoInteriorCerrado δ =
      ⋂ i : Fin 2, (fun x : Plano => x i) ⁻¹' Icc (-1 + δ) (1 - δ) := by
    ext x
    simp [cuadradoInteriorCerrado, Set.mem_iInter]
  rw [h]
  exact isClosed_iInter fun i =>
    isClosed_Icc.preimage ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous)

theorem cuadradoInteriorCerrado_sub_cuadrado {δ : ℝ} (hδ : 0 < δ) :
    cuadradoInteriorCerrado δ ⊆ cuadrado := by
  intro x hx i
  have hi := hx i
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

theorem cuadradoInteriorCerrado_compacto {δ : ℝ} (hδ : 0 < δ) :
    IsCompact (cuadradoInteriorCerrado δ) :=
  Metric.isCompact_of_isClosed_isBounded (cuadradoInteriorCerrado_cerrado δ)
    (cuadrado_acotado.subset (cuadradoInteriorCerrado_sub_cuadrado hδ))

theorem recorte_cero_izq0 {δ : ℝ} (hδ : 0 < δ) {x : Plano}
    (hx : x 0 ≤ -1 + δ) : recorte δ x = 0 := by
  have h : lado δ (x 0) = 0 := lado_cero hδ (by linarith)
  simp [recorte, h]

theorem recorte_cero_der0 {δ : ℝ} (hδ : 0 < δ) {x : Plano}
    (hx : 1 - δ ≤ x 0) : recorte δ x = 0 := by
  have h : lado δ (-(x 0)) = 0 := lado_cero hδ (by linarith)
  simp [recorte, h]

theorem recorte_cero_izq1 {δ : ℝ} (hδ : 0 < δ) {x : Plano}
    (hx : x 1 ≤ -1 + δ) : recorte δ x = 0 := by
  have h : lado δ (x 1) = 0 := lado_cero hδ (by linarith)
  simp [recorte, h]

theorem recorte_cero_der1 {δ : ℝ} (hδ : 0 < δ) {x : Plano}
    (hx : 1 - δ ≤ x 1) : recorte δ x = 0 := by
  have h : lado δ (-(x 1)) = 0 := lado_cero hδ (by linarith)
  simp [recorte, h]

theorem recorte_soporte_interior {δ : ℝ} (hδ : 0 < δ) :
    tsupport (recorte δ) ⊆ cuadradoInteriorCerrado δ := by
  apply closure_minimal _ (cuadradoInteriorCerrado_cerrado δ)
  intro x hx
  have hx0l : -1 + δ ≤ x 0 := by
    by_contra h
    exact hx (recorte_cero_izq0 hδ (le_of_lt (lt_of_not_ge h)))
  have hx0r : x 0 ≤ 1 - δ := by
    by_contra h
    exact hx (recorte_cero_der0 hδ (le_of_lt (lt_of_not_ge h)))
  have hx1l : -1 + δ ≤ x 1 := by
    by_contra h
    exact hx (recorte_cero_izq1 hδ (le_of_lt (lt_of_not_ge h)))
  have hx1r : x 1 ≤ 1 - δ := by
    by_contra h
    exact hx (recorte_cero_der1 hδ (le_of_lt (lt_of_not_ge h)))
  intro i
  fin_cases i <;> exact ⟨by assumption, by assumption⟩

theorem recorte_soporte_compacto {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (recorte δ) := by
  exact (cuadradoInteriorCerrado_compacto hδ).of_isClosed_subset
    isClosed_closure (recorte_soporte_interior hδ)

/-- El recorte vale uno en el cuadrado separado `2δ` de las cuatro caras. -/
theorem recorte_uno {δ : ℝ} (hδ : 0 < δ) {x : Plano}
    (hx : ∀ i : Fin 2, x i ∈ Icc (-1 + 2 * δ) (1 - 2 * δ)) :
    recorte δ x = 1 := by
  have h0l : lado δ (x 0) = 1 := lado_uno hδ (by linarith [(hx 0).1])
  have h0r : lado δ (-(x 0)) = 1 := lado_uno hδ (by linarith [(hx 0).2])
  have h1l : lado δ (x 1) = 1 := lado_uno hδ (by linarith [(hx 1).1])
  have h1r : lado δ (-(x 1)) = 1 := lado_uno hδ (by linarith [(hx 1).2])
  simp [recorte, h0l, h0r, h1l, h1r]

/-- Franja entre el cuadrado original y el cuadrado de semilado `1-2δ`. -/
def franja (δ : ℝ) : Set Plano :=
  cuadrado \ EllipticPdes.Analysis.FrechetKolmogorov.dbox (n := 2) (1 - 2 * δ)

theorem volumen_real_franja {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    (volume : Measure Plano).real (franja δ) = 16 * δ - 16 * δ ^ 2 := by
  let S := EllipticPdes.Analysis.FrechetKolmogorov.dbox (n := 2) (1 - 2 * δ)
  have hS : S ⊆ cuadrado := by
    intro x hx i
    have hi := (EllipticPdes.Analysis.FrechetKolmogorov.mem_dbox.mp hx) i
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  have hsm : MeasurableSet S :=
    EllipticPdes.Analysis.FrechetKolmogorov.measurableSet_dbox _
  have hvol : (volume : Measure Plano) cuadrado ≠ ⊤ := by
    rw [cuadrado_eq_dbox]
    exact EllipticPdes.Analysis.FrechetKolmogorov.volume_dbox_ne_top 1
  change (volume : Measure Plano).real (cuadrado \ S) = _
  rw [measureReal_sdiff hS hsm hvol, cuadrado_eq_dbox,
    EllipticPdes.Analysis.FrechetKolmogorov.volume_real_dbox (by norm_num : (0 : ℝ) ≤ 1),
    EllipticPdes.Analysis.FrechetKolmogorov.volume_real_dbox (by linarith : 0 ≤ 1 - 2 * δ)]
  ring

theorem volumen_real_franja_le {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    (volume : Measure Plano).real (franja δ) ≤ 16 * δ := by
  rw [volumen_real_franja hδ hδ2]
  nlinarith [sq_nonneg δ]

private theorem uno_sub_cuadrado_no_neg {t : ℝ} (hlo : -1 < t) (hhi : t < 1) :
    0 ≤ 1 - t ^ 2 := by
  nlinarith [mul_pos (by linarith : 0 < 1 - t) (by linarith : 0 < 1 + t)]

private theorem uno_sub_cuadrado_cerca_izq {δ t : ℝ}
    (ht : -1 < t) (hc : t ≤ -1 + 2 * δ) : 1 - t ^ 2 ≤ 4 * δ := by
  nlinarith [sq_nonneg (1 + t)]

private theorem uno_sub_cuadrado_cerca_der {δ t : ℝ}
    (ht : t < 1) (hc : 1 - 2 * δ ≤ t) : 1 - t ^ 2 ≤ 4 * δ := by
  nlinarith [sq_nonneg (1 - t)]

theorem psiCuadrado_no_neg_le_uno {x : Plano} (hx : x ∈ cuadrado) :
    0 ≤ psiCuadrado x ∧ psiCuadrado x ≤ 1 := by
  have hx0 := hx 0
  have hx1 := hx 1
  have h0 : 0 ≤ 1 - (x 0) ^ 2 := uno_sub_cuadrado_no_neg hx0.1 hx0.2
  have h1 : 0 ≤ 1 - (x 1) ^ 2 := uno_sub_cuadrado_no_neg hx1.1 hx1.2
  have h0u : 1 - (x 0) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 0)]
  have h1u : 1 - (x 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 1)]
  constructor
  · unfold psiCuadrado
    positivity
  · unfold psiCuadrado
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1u)]

/-- El factor de Dirichlet es de orden `δ` en la franja donde el recorte
puede variar. Es la cancelación que compensa la derivada `O(1/δ)`. -/
theorem psiCuadrado_le_en_franja {δ : ℝ} (hδ : 0 < δ) {x : Plano}
    (hx : x ∈ franja δ) : 0 ≤ psiCuadrado x ∧ psiCuadrado x ≤ 4 * δ := by
  have hs : x ∈ cuadrado := hx.1
  have hx0 := hs 0
  have hx1 := hs 1
  have h0 : 0 ≤ 1 - (x 0) ^ 2 := uno_sub_cuadrado_no_neg hx0.1 hx0.2
  have h1 : 0 ≤ 1 - (x 1) ^ 2 := uno_sub_cuadrado_no_neg hx1.1 hx1.2
  have h0u : 1 - (x 0) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 0)]
  have h1u : 1 - (x 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 1)]
  have hnot : ¬(∀ i : Fin 2,
      x i ∈ Ioo (-(1 - 2 * δ)) (1 - 2 * δ)) := by
    intro hh
    exact hx.2 (EllipticPdes.Analysis.FrechetKolmogorov.mem_dbox.mpr hh)
  have hcase : x 0 ≤ -1 + 2 * δ ∨ 1 - 2 * δ ≤ x 0 ∨
      x 1 ≤ -1 + 2 * δ ∨ 1 - 2 * δ ≤ x 1 := by
    by_contra hc
    push_neg at hc
    apply hnot
    intro i
    fin_cases i
    · change -(1 - 2 * δ) < x 0 ∧ x 0 < 1 - 2 * δ
      exact ⟨by linarith [hc.1], by linarith [hc.2.1]⟩
    · change -(1 - 2 * δ) < x 1 ∧ x 1 < 1 - 2 * δ
      exact ⟨by linarith [hc.2.2.1], by linarith [hc.2.2.2]⟩
  constructor
  · unfold psiCuadrado
    positivity
  · unfold psiCuadrado
    rcases hcase with hc | hc | hc | hc
    · have hb := uno_sub_cuadrado_cerca_izq hx0.1 hc
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1u)]
    · have hb := uno_sub_cuadrado_cerca_der hx0.2 hc
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1u)]
    · have hb := uno_sub_cuadrado_cerca_izq hx1.1 hc
      nlinarith [mul_nonneg h1 (sub_nonneg.mpr h0u)]
    · have hb := uno_sub_cuadrado_cerca_der hx1.2 hc
      nlinarith [mul_nonneg h1 (sub_nonneg.mpr h0u)]

theorem fderiv_recorte_eq_zero_fuera_franja {δ : ℝ} (hδ : 0 < δ)
    {x : Plano} (hx : x ∈ cuadrado \ franja δ) :
    fderiv ℝ (recorte δ) x = 0 := by
  have hxK : x ∈ EllipticPdes.Poincare.euclBox
      (fun _ : Fin 2 => -1 + 2 * δ) (fun _ => 1 - 2 * δ) := by
    have hinner : x ∈ EllipticPdes.Analysis.FrechetKolmogorov.dbox (n := 2)
        (1 - 2 * δ) := by
      by_contra hnot
      exact hx.2 ⟨hx.1, hnot⟩
    have hi : ∀ i : Fin 2, x i ∈ Ioo (-(1 - 2 * δ)) (1 - 2 * δ) :=
      EllipticPdes.Analysis.FrechetKolmogorov.mem_dbox.mp hinner
    intro i
    have h := hi i
    exact ⟨by linarith [h.1], h.2⟩
  have heq : recorte δ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [(EllipticPdes.Poincare.isOpen_euclBox _ _).mem_nhds hxK]
      with y hy
    exact recorte_uno hδ (fun i => ⟨(hy i).1.le, (hy i).2.le⟩)
  simpa using heq.fderiv_eq (𝕜 := ℝ)

/-- La anulación lineal de `ψ` compensa el factor `1/δ` de `Dχδ`.
Esta cota es uniforme en `δ` sobre el cuadrado. -/
theorem abs_fderiv_recorte_mul_psi_le {δ C : ℝ} (hδ : 0 < δ)
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C)
    {x : Plano} (hx : x ∈ cuadrado) (w : Plano) :
    |fderiv ℝ (recorte δ) x w * psiCuadrado x| ≤ 16 * C * ‖w‖ := by
  by_cases hF : x ∈ franja δ
  · have hψ := psiCuadrado_le_en_franja hδ hF
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    have hD : 0 ≤ 4 * C / δ := div_nonneg (by positivity) hδ.le
    rw [abs_mul, abs_of_nonneg hψ.1]
    calc
      |fderiv ℝ (recorte δ) x w| * psiCuadrado x
          ≤ (4 * C / δ) * ‖w‖ * psiCuadrado x :=
            mul_le_mul_of_nonneg_right (abs_fderiv_recorte_le_norm hδ hC x w) hψ.1
      _ ≤ (4 * C / δ) * ‖w‖ * (4 * δ) :=
            mul_le_mul_of_nonneg_left hψ.2 (mul_nonneg hD (norm_nonneg w))
      _ = 16 * C * ‖w‖ := by field_simp; ring
  · have hz := fderiv_recorte_eq_zero_fuera_franja hδ ⟨hx, hF⟩
    simpa [hz] using mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 16)
      ((abs_nonneg _).trans (hC 0))) (norm_nonneg w)

theorem norm_psi_smul_fderiv_recorte_le {δ C : ℝ} (hδ : 0 < δ)
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C)
    {x : Plano} (hx : x ∈ cuadrado) :
    ‖(psiCuadrado x) • fderiv ℝ (recorte δ) x‖ ≤ 16 * C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have h := abs_fderiv_recorte_mul_psi_le hδ hC hx w
  simpa [norm_smul, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using h

/-- Cota del gradiente del producto recortado, uniforme al reducir `δ`.
`M` puede elegirse para cada `q` suave mediante
`existe_cota_q_y_deriv_psi_q`. -/
theorem norm_fderiv_recortePsi_le {δ C M : ℝ} (hδ : 0 < δ)
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C)
    (hM : 0 ≤ M) (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    {x : Plano} (hx : x ∈ cuadrado)
    (hqM : ‖q x‖ ≤ M)
    (heM : ‖fderiv ℝ (fun y => psiCuadrado y * q y) x‖ ≤ M) :
    ‖fderiv ℝ (fun y => recorte δ y * (psiCuadrado y * q y)) x‖ ≤
      M + 16 * C * M := by
  have hχd : DifferentiableAt ℝ (recorte δ) x :=
    (recorte_suave δ).differentiable (by simp) x
  have hed : DifferentiableAt ℝ (fun y => psiCuadrado y * q y) x :=
    (psiCuadrado_suave.mul hq).differentiable (by simp) x
  rw [fderiv_fun_mul hχd hed]
  have hχ : ‖recorte δ x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (recorte_no_neg δ x)]
    exact recorte_le_uno δ x
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  calc
    ‖recorte δ x • fderiv ℝ (fun y => psiCuadrado y * q y) x +
        (psiCuadrado x * q x) • fderiv ℝ (recorte δ) x‖
      ≤ ‖recorte δ x • fderiv ℝ (fun y => psiCuadrado y * q y) x‖ +
          ‖(psiCuadrado x * q x) • fderiv ℝ (recorte δ) x‖ := norm_add_le _ _
    _ ≤ M + 16 * C * M := by
      have hfirst : ‖recorte δ x • fderiv ℝ (fun y => psiCuadrado y * q y) x‖ ≤ M := by
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_left heM (norm_nonneg _)).trans
          (by simpa using mul_le_of_le_one_left hM hχ)
      have hsecond : ‖(psiCuadrado x * q x) • fderiv ℝ (recorte δ) x‖ ≤
          16 * C * M := by
        rw [mul_smul, smul_comm, norm_smul]
        have hψD := norm_psi_smul_fderiv_recorte_le hδ hC hx
        nlinarith [mul_nonneg (sub_nonneg.mpr hqM) (by positivity : 0 ≤ 16 * C),
          mul_nonneg (norm_nonneg (q x)) (sub_nonneg.mpr hψD)]
      linarith

/-- Secuencia de anchos de recorte que tiende a cero. -/
def ancho (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem ancho_pos (n : ℕ) : 0 < ancho n := by
  unfold ancho
  positivity

theorem ancho_tendsto_cero : Tendsto ancho atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- En cada punto interior, el recorte termina valiendo uno en un entorno,
lo que también anula su derivada allí. -/
theorem eventualmente_recorte_uno_cerca {x : Plano} (hx : x ∈ cuadrado) :
    ∀ᶠ n : ℕ in atTop, recorte (ancho n) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
  have hx0 := hx 0
  have hx1 := hx 1
  have ht : Tendsto (fun n => 2 * ancho n) atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul ancho_tendsto_cero
  have h0l : ∀ᶠ n in atTop, 2 * ancho n < x 0 + 1 :=
    ht.eventually (eventually_lt_nhds (by linarith [hx0.1]))
  have h0r : ∀ᶠ n in atTop, 2 * ancho n < 1 - x 0 :=
    ht.eventually (eventually_lt_nhds (by linarith [hx0.2]))
  have h1l : ∀ᶠ n in atTop, 2 * ancho n < x 1 + 1 :=
    ht.eventually (eventually_lt_nhds (by linarith [hx1.1]))
  have h1r : ∀ᶠ n in atTop, 2 * ancho n < 1 - x 1 :=
    ht.eventually (eventually_lt_nhds (by linarith [hx1.2]))
  filter_upwards [h0l, h0r, h1l, h1r] with n h0l h0r h1l h1r
  let K : Set Plano := EllipticPdes.Poincare.euclBox
    (fun _ : Fin 2 => -1 + 2 * ancho n) (fun _ => 1 - 2 * ancho n)
  have hxK : x ∈ K := by
    intro i
    fin_cases i
    · change -1 + 2 * ancho n < x 0 ∧ x 0 < 1 - 2 * ancho n
      exact ⟨by linarith, by linarith⟩
    · change -1 + 2 * ancho n < x 1 ∧ x 1 < 1 - 2 * ancho n
      exact ⟨by linarith, by linarith⟩
  filter_upwards [(EllipticPdes.Poincare.isOpen_euclBox _ _).mem_nhds hxK] with y hy
  exact recorte_uno (ancho_pos n) (fun i => ⟨(hy i).1.le, (hy i).2.le⟩)

theorem eventualmente_recorte_valor_y_derivada {x : Plano} (hx : x ∈ cuadrado) :
    ∀ᶠ n : ℕ in atTop,
      recorte (ancho n) x = 1 ∧ fderiv ℝ (recorte (ancho n)) x = 0 := by
  filter_upwards [eventualmente_recorte_uno_cerca hx] with n hn
  exact ⟨hn.self_of_nhds, by simpa using hn.fderiv_eq (𝕜 := ℝ)⟩

/-- Para cualquier `q` suave global, el recorte de `ψ q` ya es una prueba de
soporte compacto en el cuadrado. No se exige soporte compacto de `q`. -/
def recortePsiPrueba {δ : ℝ} (hδ : 0 < δ) (q : Plano → ℝ)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) : testFunctions cuadrado :=
  ⟨fun x => recorte δ x * (psiCuadrado x * q x),
    (recorte_suave δ).mul (psiCuadrado_suave.mul hq),
    (recorte_soporte_compacto hδ).mul_right,
    (tsupport_mul_subset_left (f := recorte δ)
      (g := fun x => psiCuadrado x * q x)).trans
      ((recorte_soporte_interior hδ).trans (cuadradoInteriorCerrado_sub_cuadrado hδ))⟩

/-- Convergencia puntual interior de la función y su gradiente clásico. El
paso a `L²` requiere además una cota integrable uniforme. -/
theorem eventualmente_recortePsi_valor_y_gradiente
    (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    {x : Plano} (hx : x ∈ cuadrado) :
    ∀ᶠ n : ℕ in atTop,
      (recortePsiPrueba (ancho_pos n) q hq : Plano → ℝ) x = psiCuadrado x * q x ∧
      gradient (recortePsiPrueba (ancho_pos n) q hq : Plano → ℝ) x =
        gradient (fun y => psiCuadrado y * q y) x := by
  filter_upwards [eventualmente_recorte_uno_cerca hx] with n hn
  have heq : (fun y : Plano => recorte (ancho n) y * (psiCuadrado y * q y))
      =ᶠ[𝓝 x] (fun y => psiCuadrado y * q y) := by
    filter_upwards [hn] with y hy
    simp [hy]
  constructor
  · exact heq.self_of_nhds
  · simp only [gradient]
    change (InnerProductSpace.toDual ℝ Plano).symm
      (fderiv ℝ (fun y : Plano => recorte (ancho n) y * (psiCuadrado y * q y)) x) = _
    rw [heq.fderiv_eq]

/-- La suavidad global de `q` proporciona, por compacidad del cuadrado
cerrado, cotas simultáneas de `q` y de la derivada de `ψ q`. -/
theorem existe_cota_q_y_deriv_psi_q (q : Plano → ℝ)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ cuadrado,
      ‖q x‖ ≤ M ∧ ‖fderiv ℝ (fun y => psiCuadrado y * q y) x‖ ≤ M := by
  have hK : IsCompact (closure cuadrado) := cuadrado_acotado.isCompact_closure
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn hq.continuous.continuousOn
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun y => psiCuadrado y * q y) :=
    psiCuadrado_suave.mul hq
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn
    (he.continuous_fderiv (by simp)).continuousOn
  refine ⟨max M₁ (max M₂ 0), le_max_of_le_right (le_max_right _ _), ?_⟩
  intro x hx
  have hxc : x ∈ closure cuadrado := subset_closure hx
  exact ⟨(hM₁ x hxc).trans (le_max_left _ _),
    (hM₂ x hxc).trans ((le_max_left _ _).trans (le_max_right _ _))⟩

#print axioms TesisPINN.recorte_suave
#print axioms TesisPINN.recorte_soporte_interior
#print axioms TesisPINN.recorte_uno
#print axioms TesisPINN.volumen_real_franja_le
#print axioms TesisPINN.recortePsiPrueba
#print axioms TesisPINN.eventualmente_recortePsi_valor_y_gradiente

end TesisPINN
