import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

/-! Geometría del contorno fijo de radio cuatro empleado en (3.89). -/

noncomputable section

namespace TesisPINN

open Filter
open scoped Topology

def productoNodosHermite {n : ℕ} (t : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∏ j, (z - (t j : ℂ)) ^ 4

def aManufacturadaCompleja (z : ℂ) : ℂ :=
  if z = 1 then (Real.pi : ℂ) / 2 else
    if z = -1 then -((Real.pi : ℂ) / 2) else
      Complex.sin ((Real.pi : ℂ) * z) / (1 - z ^ 2)

private def senoComplejoHermite (z : ℂ) : ℂ := Complex.sin ((Real.pi : ℂ) * z)

private theorem senoComplejoHermite_deriv (z : ℂ) :
    deriv senoComplejoHermite z = Complex.cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ) := by
  have h : HasDerivAt (fun v : ℂ => (Real.pi : ℂ) * v) (Real.pi : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (Real.pi : ℂ)
  exact ((Complex.hasDerivAt_sin _).comp z h).deriv

private theorem cociente_analitico_raiz_simple
    {f b A : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hf0 : f c = 0)
    (hb : AnalyticAt ℂ b c) (hb0 : b c ≠ 0)
    (hA : A c = deriv f c / b c)
    (he : ∀ᶠ z in 𝓝 c, z ≠ c → A z = f z / ((z - c) * b z)) :
    AnalyticAt ℂ A c := by
  have ho : (1 : ℕ) ≤ analyticOrderAt f c := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
    intro i hi
    have : i = 0 := by omega
    simp [this, hf0]
  obtain ⟨g, hg, hfac⟩ := (natCast_le_analyticOrderAt hf).mp ho
  have hh : f =ᶠ[𝓝 c] fun z => (z - c) * g z := by
    change ∀ᶠ z in 𝓝 c, f z = (z - c) * g z
    simpa only [pow_one, smul_eq_mul] using hfac
  have hd : deriv f c = g c := by
    rw [hh.deriv_eq, deriv_fun_mul (by fun_prop) hg.differentiableAt]
    simp
  apply (hg.div hb hb0).congr
  filter_upwards [hh, he, hb.continuousAt.eventually_ne hb0] with z h₁ h₂ h₃
  by_cases hz : z = c
  · subst z
    rw [hA, hd]
    rfl
  · change g z / b z = A z
    rw [h₂ hz, h₁]
    field_simp

theorem aManufacturadaCompleja_entera (c : ℂ) : AnalyticAt ℂ aManufacturadaCompleja c := by
  have hf (z : ℂ) : AnalyticAt ℂ senoComplejoHermite z := by
    unfold senoComplejoHermite
    exact Complex.analyticAt_sin.comp (by fun_prop)
  by_cases h₁ : c = 1
  · subst c
    apply cociente_analitico_raiz_simple (f := senoComplejoHermite) (b := fun z => -(z + 1))
      (hf 1) (by simp [senoComplejoHermite, Complex.sin_pi]) (by fun_prop) (by norm_num)
    · rw [senoComplejoHermite_deriv]
      simp [aManufacturadaCompleja, Complex.cos_pi] <;> ring
    · filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ -1)] with z hz h
      rw [aManufacturadaCompleja, if_neg h, if_neg hz]
      congr 1
      ring
  by_cases h₂ : c = -1
  · subst c
    apply cociente_analitico_raiz_simple (f := senoComplejoHermite) (b := fun z => 1 - z)
      (hf (-1)) (by simp [senoComplejoHermite, Complex.sin_neg, Complex.sin_pi])
      (by fun_prop) (by norm_num)
    · rw [senoComplejoHermite_deriv]
      simp [aManufacturadaCompleja, Complex.cos_neg, Complex.cos_pi, h₁] <;> ring
    · filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℂ) ≠ 1)] with z hz h
      rw [aManufacturadaCompleja, if_neg hz, if_neg h]
      congr 1
      ring
  have hb : 1 - c ^ 2 ≠ 0 := by
    intro h
    have hc : (c - 1) * (c + 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hc with hc | hc
    · exact h₁ (sub_eq_zero.mp hc)
    · exact h₂ (eq_neg_of_add_eq_zero_left hc)
  apply ((hf c).div (show AnalyticAt ℂ (fun z => 1 - z ^ 2) c by fun_prop) hb).congr
  filter_upwards [eventually_ne_nhds h₁, eventually_ne_nhds h₂] with z hz₁ hz₂
  simp [aManufacturadaCompleja, senoComplejoHermite, hz₁, hz₂]

def restoContornoHermite {n : ℕ} (t : Fin n → ℝ) (a : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    circleIntegral (fun ζ => a ζ * productoNodosHermite t z /
      (productoNodosHermite t ζ * (ζ - z))) 0 4

theorem distancia_contorno_nodo {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    {ζ : ℂ} (hζ : ‖ζ‖ = 4) : 3 ≤ ‖ζ - (t : ℂ)‖ := by
  have h := norm_sub_norm_le ζ (t : ℂ)
  rw [hζ, Complex.norm_real, Real.norm_eq_abs] at h
  linarith [(abs_le.mpr ht : |t| ≤ 1)]

theorem productoNodosHermite_contorno {n : ℕ} (t : Fin n → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1) {ζ : ℂ} (hζ : ‖ζ‖ = 4) :
    (3 : ℝ) ^ (4 * n) ≤ ‖productoNodosHermite t ζ‖ := by
  simp only [productoNodosHermite, norm_prod, norm_pow, pow_mul]
  calc
    ((3 : ℝ) ^ 4) ^ n = ∏ _ : Fin n, (3 : ℝ) ^ 4 := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ =>
      pow_le_pow_left₀ (by norm_num) (distancia_contorno_nodo (ht j) hζ) 4)

/-- Cociente del producto nodal en el disco de evaluación. Reduce a
`(2/3)^(4*n)` sobre el intervalo y a `(5/6)^(4*n)` en el disco de radio `3/2`. -/
theorem productoNodosHermite_cociente {n : ℕ} (t : Fin n → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1) {ζ z : ℂ}
    (hζ : ‖ζ‖ = 4) {R : ℝ} (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖productoNodosHermite t z / productoNodosHermite t ζ‖ ≤
      ((R + 1) / 3) ^ (4 * n) := by
  have hden := productoNodosHermite_contorno t ht hζ
  have hnum : ‖productoNodosHermite t z‖ ≤ (R + 1) ^ (4 * n) := by
    simp only [productoNodosHermite, norm_prod, norm_pow, pow_mul]
    calc
      _ ≤ ∏ _ : Fin n, (R + 1) ^ 4 := by
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro j _
        apply pow_le_pow_left₀ (norm_nonneg _)
        have h := norm_sub_le z (t j : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs] at h
        exact h.trans (add_le_add hz (abs_le.mpr (ht j)))
      _ = _ := by simp
  rw [norm_div, div_pow]
  exact div_le_div₀ (by positivity) hnum (by positivity) hden

/-- Cota del término integral de (3.89) en un disco fijo de evaluación. -/
theorem restoContornoHermite_cota {n : ℕ} (t : Fin n → ℝ) (a : ℂ → ℂ)
    (ht : ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1) {M R : ℝ}
    (hM : 0 ≤ M) (ha : ∀ ζ, ‖ζ‖ = 4 → ‖a ζ‖ ≤ M)
    (hR : 0 ≤ R) (hR4 : R < 4) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖restoContornoHermite t a z‖ ≤ 4 * (M * ((R + 1) / 3) ^ (4 * n) / (4 - R)) := by
  unfold restoContornoHermite
  change ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    (circleIntegral (fun ζ => a ζ * productoNodosHermite t z /
      (productoNodosHermite t ζ * (ζ - z))) 0 4 : ℂ)‖ ≤ _
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by norm_num)
  intro ζ hζ
  have hs : ‖ζ‖ = 4 := by simpa [Metric.mem_sphere, dist_zero_right] using hζ
  have hd : 4 - R ≤ ‖ζ - z‖ := by
    linarith [norm_sub_norm_le ζ z]
  have he : a ζ * productoNodosHermite t z / (productoNodosHermite t ζ * (ζ - z)) =
      a ζ * (productoNodosHermite t z / productoNodosHermite t ζ) / (ζ - z) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  rw [he, norm_div, norm_mul]
  exact div_le_div₀ (by positivity)
    (mul_le_mul (ha ζ hs) (productoNodosHermite_cociente t ht hs hR hz)
      (norm_nonneg _) hM) (by linarith) hd

/-- Si los cuatro jets de `f` se anulan en cada nodo, el cociente
por el producto nodal admite una prolongación entera. -/
theorem existe_cociente_entero_hermite {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t)
    (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z)
    (hjet : ∀ j k, k < 4 → iteratedDeriv k f (t j : ℂ) = 0) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧
      (∀ z, f z = productoNodosHermite t z * g z) := by
  classical
  let Q := productoNodosHermite t
  let g (z : ℂ) := if Q z = 0 then limUnder (𝓝[≠] z) (fun w => f w / Q w) else f z / Q z
  have hQ (z : ℂ) : AnalyticAt ℂ Q z := by
    unfold Q productoNodosHermite
    exact Finset.analyticAt_fun_prod _ (fun _ _ => by fun_prop)
  have hroot (z : ℂ) (hz : Q z = 0) : ∃ i, z = (t i : ℂ) := by
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz
    exact ⟨i, sub_eq_zero.mp (by by_contra hn; exact (pow_ne_zero 4 hn) hi)⟩
  refine ⟨g, ?_, ?_⟩
  · intro z
    by_cases hz : Q z = 0
    · obtain ⟨i, rfl⟩ := hroot z hz
      let c : ℂ := t i
      let B (w : ℂ) : ℂ := ∏ j ∈ Finset.univ.erase i, (w - (t j : ℂ)) ^ 4
      have hB : AnalyticAt ℂ B c := Finset.analyticAt_fun_prod _ (fun _ _ => by fun_prop)
      have hB0 : B c ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro j hj
        apply pow_ne_zero
        apply sub_ne_zero.mpr
        exact fun h => (Finset.mem_erase.mp hj).1 (ht (Complex.ofReal_injective h.symm))
      have hsplit (w : ℂ) : Q w = (w - c) ^ 4 * B w :=
        (Finset.mul_prod_erase _ (fun j => (w - (t j : ℂ)) ^ 4) (Finset.mem_univ i)).symm
      obtain ⟨G, hG, hF⟩ := (natCast_le_analyticOrderAt (hf c)).mp
        ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf c)).mpr (hjet i))
      let V (w : ℂ) := G w / B w
      have hV : AnalyticAt ℂ V c := hG.div hB hB0
      have hE : ∀ᶠ w in 𝓝 c, w ≠ c → Q w ≠ 0 ∧ f w / Q w = V w := by
        filter_upwards [hF, hB.continuousAt.eventually_ne hB0] with w hw hb hne
        have hpow : (w - c) ^ 4 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
        constructor
        · rw [hsplit]
          exact mul_ne_zero hpow hb
        · simp only [hsplit, hw, smul_eq_mul, V]
          field_simp
      have hlim : Tendsto (fun w => f w / Q w) (𝓝[≠] c) (𝓝 (V c)) := by
        apply (hV.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
        filter_upwards [hE.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hne
        exact (hw hne).2.symm
      apply hV.congr
      filter_upwards [hE] with w hw
      by_cases h : w = c
      · rw [h]
        change V c = g c
        have hzero : Q c = 0 := hz
        simp only [g, hzero, ite_true, hlim.limUnder_eq]
      · rw [show g w = f w / Q w by simp [g, (hw h).1]]
        exact (hw h).2.symm
    · apply ((hf z).div (hQ z) hz).congr
      filter_upwards [(hQ z).continuousAt.eventually_ne hz] with w hw
      simp [g, hw]
  · intro z
    by_cases hz : Q z = 0
    · obtain ⟨i, rfl⟩ := hroot z hz
      change f (t i : ℂ) = Q (t i : ℂ) * _
      rw [hz, zero_mul]
      simpa only [iteratedDeriv_zero] using hjet i 0 (by decide)
    · change f z = Q z * g z
      simp only [g, hz, ite_false]
      field_simp

/-- Fórmula de Cauchy para la diferencia que se anula con sus jets.
La fórmula con numerador `a` requiere además eliminar la contribución de `p`. -/
theorem restoContornoHermite_diferencia {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t)
    (hI : ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1)
    (a p : ℂ → ℂ) (ha : ∀ z, AnalyticAt ℂ a z) (hp : ∀ z, AnalyticAt ℂ p z)
    (hjet : ∀ j k, k < 4 → iteratedDeriv k (a - p) (t j : ℂ) = 0)
    {z : ℂ} (hz : ‖z‖ < 4) :
    restoContornoHermite t (a - p) z = a z - p z := by
  obtain ⟨g, hg, hfac⟩ := existe_cociente_entero_hermite t ht (a - p)
    (fun w => (ha w).sub (hp w)) hjet
  have hd : Differentiable ℂ (fun w => productoNodosHermite t z * g w) :=
    fun w => (analyticAt_const.mul (hg w)).differentiableAt
  have hb : z ∈ Metric.ball (0 : ℂ) 4 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  have hc := (hd.differentiableOn.diffContOnCl).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hb
  rw [← hfac z] at hc
  unfold restoContornoHermite
  change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    (circleIntegral (fun w => (a - p) w * productoNodosHermite t z /
      (productoNodosHermite t w * (w - z))) 0 4 : ℂ) = (a - p) z
  rw [← hc]
  congr 1
  apply circleIntegral.integral_congr (by norm_num)
  intro w hw
  have hw4 : ‖w‖ = 4 := by simpa [Metric.mem_sphere, dist_zero_right] using hw
  have hQ : productoNodosHermite t w ≠ 0 := by
    have hh := productoNodosHermite_contorno t hI hw4
    intro h
    rw [h, norm_zero] at hh
    exact (not_le_of_gt (show 0 < (3 : ℝ) ^ (4 * n) by positivity)) hh
  dsimp only
  rw [hfac w]
  simp only [smul_eq_mul]
  have hW : w - z ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    rw [he] at hw4
    exact hz.ne hw4
  field_simp <;> ring

/-- Diferenciación bajo la integral de Cauchy en todo el disco de radio cuatro. -/
theorem derivadas_nucleo_contorno_hermite (f : ℂ → ℂ) (hf : CircleIntegrable f 0 4)
    (k : ℕ) {z : ℂ} (hz : ‖z‖ < 4) :
    iteratedDeriv k
        (fun w => circleIntegral (fun ζ => (ζ - w) ^ (-1 : ℤ) • f ζ) 0 4) z =
      (k.factorial : ℂ) •
        circleIntegral (fun ζ => (ζ - z) ^ (-(k : ℤ) - 1) • f ζ) 0 4 := by
  induction k generalizing z with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hE : iteratedDeriv k
        (fun w => circleIntegral (fun ζ => (ζ - w) ^ (-1 : ℤ) • f ζ) 0 4) =ᶠ[𝓝 z]
        (fun w => (k.factorial : ℂ) •
          circleIntegral (fun ζ => (ζ - w) ^ (-(k : ℤ) - 1) • f ζ) 0 4) := by
      filter_upwards [((isOpen_lt continuous_norm continuous_const).mem_nhds hz)] with w hw
      exact ih hw
    rw [hE.deriv_eq]
    have hw : z ∉ Metric.sphere (0 : ℂ) |(4 : ℝ)| := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz.ne
    have hd := (Complex.hasDerivAt_circleIntegral_sub_zpow_smul
      (n := -(k : ℤ) - 1) hf hw).const_smul (k.factorial : ℂ)
    have heval := hd.deriv
    change deriv (fun w => (k.factorial : ℂ) •
      circleIntegral (fun ζ => (ζ - w) ^ (-(k : ℤ) - 1) • f ζ) 0 4) z = _ at heval
    rw [heval]
    have he : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by omega
    rw [he, smul_smul, Nat.factorial_succ]
    push_cast
    simp only [smul_eq_mul]
    ring

#check restoContornoHermite
#print axioms aManufacturadaCompleja_entera
#print axioms productoNodosHermite_cociente
#print axioms restoContornoHermite_cota
#print axioms restoContornoHermite_diferencia
#print axioms derivadas_nucleo_contorno_hermite

end TesisPINN
