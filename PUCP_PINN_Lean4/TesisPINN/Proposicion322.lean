import TesisPINN.EspectroDirichletCuadrado
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Estimación de la serie espectral de Dirichlet. -/

noncomputable section

namespace TesisPINN

open MeasureTheory EllipticPdes EllipticPdes.H1Graph Filter Set
open scoped RealInnerProductSpace Topology

def coefSeno (z : Lp ℝ 2 volumenPoisson) (p : ℕ × ℕ) : ℝ := inner ℝ (modoSenoLp p) z

def serieSeno (z : Lp ℝ 2 volumenPoisson) (x : Plano) : ℝ :=
  ∑' p : ℕ × ℕ, coefSeno z p * modoSeno p x

theorem sumable_inv_autovalorSeno :
    Summable (fun p : ℕ × ℕ => (autovalorSeno p)⁻¹ ^ 2) := by
  simp_rw [autovalorSeno_inv_sq]
  exact terminoEspectral_sumable.mul_left _

theorem sqrt_suma_inv_autovalorSeno :
    Real.sqrt (∑' p : ℕ × ℕ, (autovalorSeno p)⁻¹ ^ 2) = constanteEspectralCuadrado := by
  simp_rw [autovalorSeno_inv_sq]
  rw [tsum_mul_left, Real.sqrt_mul (by positivity), constanteEspectralCuadrado, sumaEspectral]
  congr 1
  have hp := Real.pi_pos
  rw [show 16 / Real.pi ^ 4 = (4 / Real.pi ^ 2) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

theorem suma_coefSeno_acotada
    (e : H01 (volume : Measure Plano) cuadrado) (r : Lp ℝ 2 volumenPoisson)
    (hr : HasDistributionalLaplacian cuadradoOpens volume e r) :
    let z := fnL (e : H1Graph volume cuadrado)
    Summable (fun p => |coefSeno z p|) ∧
      (∑' p, |coefSeno z p|) ≤ constanteEspectralCuadrado * ‖r‖ := by
  intro z
  have hcoef (p : ℕ × ℕ) :
      |coefSeno z p| = |coefSeno (-r) p| * (autovalorSeno p)⁻¹ := by
    have he := coeficiente_laplaciano_modoSeno e r hr p
    rw [real_inner_comm (modoSenoLp p) (-r),
      real_inner_comm (modoSenoLp p) (fnL (e : H1Graph volume cuadrado))] at he
    change coefSeno (-r) p = autovalorSeno p * coefSeno z p at he
    rw [he, abs_mul, abs_of_pos (autovalorSeno_pos p)]
    field_simp [(autovalorSeno_pos p).ne']
  have hsum (s : Finset (ℕ × ℕ)) :
      ∑ p ∈ s, |coefSeno z p| ≤ constanteEspectralCuadrado * ‖r‖ := by
    simp_rw [hcoef]
    have hb := modoSenoLp_ortonormal.sum_inner_products_le (-r) (s := s)
    change ∑ p ∈ s, ‖coefSeno (-r) p‖ ^ 2 ≤ ‖-r‖ ^ 2 at hb
    rw [norm_neg] at hb
    simp only [Real.norm_eq_abs] at hb
    have hc := sumable_inv_autovalorSeno.sum_le_tsum s (fun p _ => sq_nonneg _)
    calc
      _ ≤ Real.sqrt (∑ p ∈ s, |coefSeno (-r) p| ^ 2) *
          Real.sqrt (∑ p ∈ s, (autovalorSeno p)⁻¹ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s _ _
      _ ≤ Real.sqrt (‖r‖ ^ 2) * Real.sqrt (∑' p, (autovalorSeno p)⁻¹ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hb) (Real.sqrt_le_sqrt hc) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_sq (norm_nonneg _), sqrt_suma_inv_autovalorSeno, mul_comm]
  have h := summable_of_sum_le (fun p => abs_nonneg (coefSeno z p)) hsum
  exact ⟨h, h.tsum_le_of_sum_le hsum⟩

/-- La serie de los coeficientes del error tiene convergencia absoluta
y uniforme. El enunciado de representación en L² requiere además densidad. -/
theorem serieSeno_convergencia
    (e : H01 (volume : Measure Plano) cuadrado) (r : Lp ℝ 2 volumenPoisson)
    (hr : HasDistributionalLaplacian cuadradoOpens volume e r) :
    let z := fnL (e : H1Graph volume cuadrado)
    (∀ x, Summable (fun p => |coefSeno z p * modoSeno p x|)) ∧
    TendstoUniformly (fun s : Finset (ℕ × ℕ) => fun x =>
      ∑ p ∈ s, coefSeno z p * modoSeno p x) (serieSeno z) atTop ∧
    Continuous (serieSeno z) ∧ EqOn (serieSeno z) 0 (frontier cuadrado) ∧
    ∀ x, |serieSeno z x| ≤ constanteEspectralCuadrado * ‖r‖ := by
  intro z
  obtain ⟨hs, hnorm⟩ := suma_coefSeno_acotada e r hr
  have hb (p : ℕ × ℕ) (x : Plano) :
      ‖coefSeno z p * modoSeno p x‖ ≤ |coefSeno z p| := by
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (abs_modoSeno_le_uno p x) (abs_nonneg (coefSeno z p))
  have hsum (x : Plano) : Summable (fun p => ‖coefSeno z p * modoSeno p x‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => hb p x) hs
  refine ⟨fun x => by simpa only [Real.norm_eq_abs] using hsum x,
    tendstoUniformly_tsum hs hb, continuous_tsum
      (fun p => continuous_const.mul (modoSeno_suave p).continuous) hs hb, ?_, ?_⟩
  · intro x hx
    simp [serieSeno, modoSeno_cero_frontera _ hx]
  · intro x
    calc
      |serieSeno z x| ≤ ∑' p, ‖coefSeno z p * modoSeno p x‖ := norm_tsum_le_tsum_norm (hsum x)
      _ ≤ ∑' p, |coefSeno z p| := (hsum x).tsum_le_tsum (fun p => hb p x) hs
      _ ≤ _ := hnorm

/-- Identifica el límite continuo con la suma en L² y conserva los
coeficientes en todos los modos. -/
theorem serieSeno_suma_L2
    (e : H01 (volume : Measure Plano) cuadrado) (r : Lp ℝ 2 volumenPoisson)
    (hr : HasDistributionalLaplacian cuadradoOpens volume e r) :
    let z := fnL (e : H1Graph volume cuadrado)
    ∃ w : Lp ℝ 2 volumenPoisson,
      HasSum (fun p => coefSeno z p • modoSenoLp p) w ∧
      (⇑w =ᵐ[volumenPoisson] serieSeno z) ∧
      ∀ p, coefSeno w p = coefSeno z p := by
  classical
  intro z
  have ⟨hs, _⟩ := suma_coefSeno_acotada e r hr
  let a (p : ℕ × ℕ) := coefSeno z p • modoSenoLp p
  have ha : Summable a := by
    apply Summable.of_norm
    simpa [a, norm_smul, modoSenoLp_norma, Real.norm_eq_abs] using hs
  let w := ∑' p, a p
  refine ⟨w, ha.hasSum, ?_, ?_⟩
  · have hsum (s : Finset (ℕ × ℕ)) :
        (⇑(∑ p ∈ s, a p) : Plano → ℝ) =ᵐ[volumenPoisson]
          (fun x => ∑ p ∈ s, coefSeno z p * modoSeno p x) := by
      refine (Lp.coeFn_finsetSum s a).trans ?_
      have h := eventuallyEq_sum (s := s) (fun p _ =>
          (Lp.coeFn_smul (coefSeno z p) (modoSenoLp p)).trans
            ((grafoModoSeno_fnL_ae p).mono fun x hx => by
              change coefSeno z p * (modoSenoLp p) x = _
              exact congrArg (coefSeno z p * ·) hx))
      filter_upwards [h] with x hx
      simpa only [a, Finset.sum_apply] using hx
    have hμ := tendstoInMeasure_of_tendsto_Lp ha.hasSum
    obtain ⟨ns, hns, hlim⟩ := hμ.exists_seq_tendsto_ae'
    have heq := ae_all_iff.mpr (fun n => hsum (ns n))
    filter_upwards [hlim, heq] with x hx hxs
    have hu := (serieSeno_convergencia e r hr).2.1.tendsto_at x
    apply tendsto_nhds_unique hx
    convert hu.comp hns using 1
    ext n
    exact hxs n
  · intro p
    have h := ha.hasSum.mapL (innerSL ℝ (modoSenoLp p))
    have hh : ∀ q, (innerSL ℝ (modoSenoLp p)) (a q) = if q = p then coefSeno z p else 0 := by
      intro q
      rw [innerSL_apply_apply, show a q = coefSeno z q • modoSenoLp q from rfl,
        real_inner_smul_right, orthonormal_iff_ite.mp modoSenoLp_ortonormal]
      by_cases hpq : q = p
      · subst q
        simp
      · simp [hpq, Ne.symm hpq]
    simp_rw [hh] at h
    exact h.unique (hasSum_ite_eq p (coefSeno z p))

#check serieSeno_convergencia
#check serieSeno_suma_L2
#print axioms suma_coefSeno_acotada
#print axioms serieSeno_convergencia
#print axioms serieSeno_suma_L2

end TesisPINN
