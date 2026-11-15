import TesisPINN.Proposicion325
import TesisPINN.TransferenciaEnergetica

/-! Funcional de la clase polinómica en las coordenadas de L3.24. -/

noncomputable section

namespace TesisPINN

open Set MeasureTheory Filter EllipticPdes EllipticPdes.H1Graph
open scoped Topology Distributions

def polinomioPlano326 {D : ℕ} (a : Coeficientes324 D) (x : Plano) : ℝ :=
  polinomio324 a (fun b => if b then x 0 else x 1)

def candidato326 (D : ℕ) : Coeficientes324 D →ₗ[ℝ] (Plano → ℝ) where
  toFun a x := mapaCoeficientes324 D a (fun b => if b then x 0 else x 1)
  map_add' a b := funext fun x => congrFun ((mapaCoeficientes324 D).map_add a b) _
  map_smul' c a := funext fun x => congrFun ((mapaCoeficientes324 D).map_smul c a) _

theorem candidato326_eq {D : ℕ} (a : Coeficientes324 D) (x : Plano) :
    candidato326 D a x = psiCuadrado x * polinomioPlano326 a x := by
  change factor324 _ * polinomioPlano326 a x = _
  rw [factor324_eq_psiCuadrado]

theorem candidato326_inyectivo (D : ℕ) : Function.Injective (candidato326 D) := by
  intro a b hab
  apply mapaCoeficientes324_inyectivo D
  funext x
  let y : Plano := WithLp.toLp 2 ![x true, x false]
  have he : (fun b => if b then y 0 else y 1) = x := funext fun b => by cases b <;> rfl
  simpa only [candidato326, LinearMap.coe_mk, AddHom.coe_mk, he] using congrFun hab y

theorem polinomioPlano326_suave {D : ℕ} (a : Coeficientes324 D) :
    ContDiff ℝ (⊤ : ℕ∞) (polinomioPlano326 a) := by
  have hcoord (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plano => x i) :=
    (EuclideanSpace.proj i : Plano →L[ℝ] ℝ).contDiff
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : Plano => ∑ p : IndiceMonomio D,
    a p * (x 0 ^ p.1.val * x 1 ^ p.2.val))
  exact ContDiff.sum fun p _ => contDiff_const.mul ((hcoord 0).pow _ |>.mul ((hcoord 1).pow _))

theorem candidato326_suave {D : ℕ} (a : Coeficientes324 D) :
    ContDiff ℝ (⊤ : ℕ∞) (candidato326 D a) := by
  rw [show candidato326 D a = _ from funext (candidato326_eq a)]
  exact psiCuadrado_suave.mul (polinomioPlano326_suave a)

def laplaciano326 (D : ℕ) : Coeficientes324 D →ₗ[ℝ] (Plano → ℝ) where
  toFun a := laplacianoClásico (candidato326 D a)
  map_add' a b := by
    rw [(candidato326 D).map_add]
    have ha := candidato326_suave a
    have hb := candidato326_suave b
    have hs : ContDiff ℝ (⊤ : ℕ∞) (candidato326 D a + candidato326 D b) := ha.add hb
    rw [laplacianoClásico_eq_mathlib _ hs, laplacianoClásico_eq_mathlib _ ha,
      laplacianoClásico_eq_mathlib _ hb]
    exact funext fun x => (ha.contDiffAt.of_le (by simp)).laplacian_add
      (hb.contDiffAt.of_le (by simp))
  map_smul' c a := by
    rw [(candidato326 D).map_smul]
    have ha := candidato326_suave a
    have hs : ContDiff ℝ (⊤ : ℕ∞) (c • candidato326 D a) := ha.const_smul c
    rw [laplacianoClásico_eq_mathlib _ hs, laplacianoClásico_eq_mathlib _ ha]
    exact funext fun x => InnerProductSpace.laplacian_smul c (ha.contDiffAt.of_le (by simp))

private theorem holder_cuadrado_de_C1 (f : Plano → ℝ) (hf : ContDiff ℝ 1 f) :
    EsHolderInterior cuadrado (1 / 2) f := by
  obtain ⟨B, hB⟩ := cuadrado_acotado.isCompact_closure.exists_bound_of_continuousOn
    (hf.continuous_fderiv (by simp)).continuousOn
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hconv : Convex ℝ (closure cuadrado) := by
    rw [clausura_cuadrado]
    intro x hx y hy a b ha hb hab i
    change a * x i + b * y i ∈ Icc (-1 : ℝ) 1
    exact convex_Icc _ _ (hx i) (hy i) ha hb hab
  refine ⟨2 * M, by positivity, fun x hx y hy => ?_⟩
  have hLip : ‖f x - f y‖ ≤ M * dist x y := by
    rw [dist_eq_norm]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hf.differentiable (by simp) z)
      (fun z hz => (hB z hz).trans (le_max_left _ _)) hconv (subset_closure hy) (subset_closure hx)
  rw [← Real.norm_eq_abs, ← Real.sqrt_eq_rpow]
  exact hLip.trans ((mul_le_mul_of_nonneg_left
    (dist_le_dos_raiz_cuadrado (subset_closure hx) (subset_closure hy)) hM).trans_eq (by ring))

theorem laplaciano326_holder {D : ℕ} (a : Coeficientes324 D) :
    EsHolderInterior cuadrado (1 / 2) (laplaciano326 D a) :=
  holder_cuadrado_de_C1 _ ((laplacianoClásico_suave _ (candidato326_suave a)).of_le (by simp))

/-- La seminorma utilizada es el ínfimo de las constantes Hölder admisibles. -/
def seminorma326 (D : ℕ) : Seminorm ℝ (Coeficientes324 D) := by
  refine Seminorm.ofSMulLE (fun a => seminormaInterior cuadrado (1 / 2) (laplaciano326 D a))
    ?_ ?_ ?_
  · rw [(laplaciano326 D).map_zero]
    apply le_antisymm (csInf_le ⟨0, fun _ h => h.1⟩ ?_)
      (seminormaInterior_nonneg _ _ _ (by simpa using laplaciano326_holder (0 : Coeficientes324 D)))
    exact ⟨le_rfl, by simp⟩
  · intro a b
    rw [(laplaciano326 D).map_add]
    apply csInf_le ⟨0, fun _ h => h.1⟩
    let Sa := seminormaInterior cuadrado (1 / 2) (laplaciano326 D a)
    let Sb := seminormaInterior cuadrado (1 / 2) (laplaciano326 D b)
    refine ⟨add_nonneg (seminormaInterior_nonneg _ _ _ (laplaciano326_holder a))
      (seminormaInterior_nonneg _ _ _ (laplaciano326_holder b)), fun x hx y hy => ?_⟩
    simp only [Pi.add_apply, add_sub_add_comm, add_mul]
    exact (abs_add_le _ _).trans (add_le_add
      (seminormaInterior_cota _ _ _ (laplaciano326_holder a) (by norm_num) x hx y hy)
      (seminormaInterior_cota _ _ _ (laplaciano326_holder b) (by norm_num) x hx y hy))
  · intro c a
    rw [Real.norm_eq_abs]
    apply csInf_le ⟨0, fun _ h => h.1⟩
    refine ⟨mul_nonneg (abs_nonneg _) (seminormaInterior_nonneg _ _ _ (laplaciano326_holder a)),
      fun x hx y hy => ?_⟩
    rw [(laplaciano326 D).map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (seminormaInterior_cota _ _ _ (laplaciano326_holder a) (by norm_num) x hx y hy) (abs_nonneg _)
theorem seminorma326_continua (D : ℕ) : Continuous (seminorma326 D) := by
  classical
  let p := seminorma326 D
  let b := Pi.basisFun ℝ (IndiceMonomio D)
  let C := ∑ i : IndiceMonomio D, p (b i)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => apply_nonneg p _
  let q : Seminorm ℝ (Coeficientes324 D) := Seminorm.of
    (fun a => C * ‖a‖)
    (fun a b => (mul_le_mul_of_nonneg_left (norm_add_le a b) hC).trans_eq (mul_add _ _ _))
    (fun c a => by rw [norm_smul]; ring)
  apply Seminorm.continuous_of_le (q := q)
  · exact continuous_const.mul continuous_norm
  · intro a
    change p a ≤ (∑ i, p (b i)) * ‖a‖
    calc
      p a = p (∑ i, a i • b i) := by
        congr 1
        simpa only [b, Pi.basisFun_repr] using (b.sum_repr a).symm
      _ ≤ ∑ i, p (a i • b i) := by
        let u : Finset (IndiceMonomio D) := Finset.univ
        change p (∑ i ∈ u, a i • b i) ≤ ∑ i ∈ u, p (a i • b i)
        induction u using Finset.induction_on with
        | empty => simp
        | insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi]
          exact (map_add_le_add p _ _).trans (add_le_add_right ih _)
      _ ≤ (∑ i, p (b i)) * ‖a‖ := by
        rw [Finset.sum_mul]
        simp only [map_smul_eq_mul]
        exact Finset.sum_le_sum fun i _ =>
          (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_left (norm_le_pi_norm a i) (apply_nonneg p _))

def funcional326 {D m : ℕ} (s : Fin m → Plano) (peso : ℝ) (a : Coeficientes324 D) : ℝ :=
  funcionalInterior cuadrado (1 / 2) s (laplaciano326 D a) fuenteManufacturada peso

theorem funcional326_continuo {D m : ℕ} (s : Fin m → Plano) (peso : ℝ) :
    Continuous (funcional326 s peso : Coeficientes324 D → ℝ) := by
  unfold funcional326 funcionalInterior perdidaEmpiricaInterior
  have hc (i : Fin m) : Continuous (fun a : Coeficientes324 D => laplaciano326 D a (s i)) :=
    ((LinearMap.proj (s i)).comp (laplaciano326 D)).continuous_of_finiteDimensional
  exact ((continuous_finsetSum _ fun i _ => ((hc i).sub continuous_const).pow 2).div_const _).add
    (continuous_const.mul ((seminorma326_continua D).pow 2))

private theorem candidato326_analitico {D : ℕ} (a : Coeficientes324 D) :
    AnalyticOnNhd ℝ (candidato326 D a) univ := by
  intro x _
  rw [show candidato326 D a = _ from funext (candidato326_eq a)]
  have hcoord (i : Fin 2) : AnalyticAt ℝ (fun x : Plano => x i) x :=
    (EuclideanSpace.proj i : Plano →L[ℝ] ℝ).analyticAt x
  have hp : AnalyticAt ℝ (polinomioPlano326 a) x := by
    change AnalyticAt ℝ (fun y : Plano => ∑ p : IndiceMonomio D,
      a p * (y 0 ^ p.1.val * y 1 ^ p.2.val)) x
    exact Finset.analyticAt_fun_sum _ fun p _ => analyticAt_const.mul
      (((hcoord 0).pow _).mul ((hcoord 1).pow _))
  refine AnalyticAt.fun_mul ?_ hp
  unfold psiCuadrado
  exact (analyticAt_const.sub ((hcoord 0).pow 2)).mul
    (analyticAt_const.sub ((hcoord 1).pow 2))

theorem coeficientes326_eq_zero_of_laplaciano {D : ℕ} (a : Coeficientes324 D)
    (hΔ : EqOn (laplaciano326 D a) 0 cuadrado) : a = 0 := by
  let q := polinomioPlano326 a
  let hq := polinomioPlano326_suave a
  let e : H1Graph.H01 (volume : Measure Plano) cuadrado :=
    ⟨psiGraph q hq, psiGraph_mem_H01 q hq⟩
  have he : (fun x => psiCuadrado x * q x) = candidato326 D a :=
    (funext (candidato326_eq a)).symm
  let r := laplacianoLp (candidato326 D a) (candidato326_suave a)
  have hr : r = 0 := by
    apply Lp.ext
    apply (laplacianoLp_ae _ _).trans
    have hz : laplaciano326 D a =ᵐ[(volume : Measure Plano).restrict cuadrado] (0 : Plano → ℝ) :=
      (ae_restrict_iff' cuadrado_abierto.measurableSet).2
        (Filter.Eventually.of_forall fun x hx => hΔ hx)
    exact hz.trans (Lp.coeFn_zero _ _ _).symm
  have hdist : HasDistributionalLaplacian cuadradoOpens volume e r := by
    unfold HasDistributionalLaplacian
    rw [Distribution.ofFun_congr_ae (psiGraph_fnL_ae q hq), he]
    exact laplaciano_distribucional_eq_laplacianoLp _ _
  have hnorm := energia_cuadrado_uniforme e r hdist
  rw [hr, norm_zero, mul_zero] at hnorm
  have hgraph : psiGraph q hq = 0 := norm_le_zero_iff.mp hnorm
  have hae := psiGraph_fnL_ae q hq
  rw [hgraph, map_zero, he] at hae
  have hzero := Measure.eqOn_open_of_ae_eq
    (hae.symm.trans (Lp.coeFn_zero _ _ _)) cuadrado_abierto
    (candidato326_suave a).continuous.continuousOn continuous_zero.continuousOn
  have hnear : candidato326 D a =ᶠ[nhds 0] 0 := by
    apply Filter.mem_of_superset (cuadrado_abierto.mem_nhds ?_) hzero
    intro i
    change (-1 : ℝ) < 0 ∧ (0 : ℝ) < 1
    norm_num
  apply candidato326_inyectivo D
  rw [map_zero]
  exact (candidato326_analitico a).eq_of_eventuallyEq (fun _ _ => analyticAt_const) hnear

private theorem laplaciano326_esquina {D : ℕ} (a : Coeficientes324 D) :
    laplaciano326 D a (WithLp.toLp 2 ![1, 1]) = 0 := by
  classical
  let b := Pi.basisFun ℝ (IndiceMonomio D)
  have he : a = ∑ i, a i • b i := by
    simpa only [b, Pi.basisFun_repr] using (b.sum_repr a).symm
  rw [he, map_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul, Pi.smul_apply]
  let P (k : ℕ) (t : ℝ) := (1 - t ^ 2) * t ^ k
  have hP (k) : ContDiff ℝ 2 (P k) := by unfold P; fun_prop
  have hfun : candidato326 D (b i) = fun x => P i.1.val (x 0) * P i.2.val (x 1) := by
    funext x
    rw [candidato326_eq]
    unfold polinomioPlano326 polinomio324
    have hv (j : IndiceMonomio D) : b i j = if j = i then 1 else 0 := by
      simp [b, Pi.basisFun_apply, Pi.single_apply, eq_comm]
    simp only [hv, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, psiCuadrado, monomio324, Bool.false_eq_true, ite_false, P]
    ring
  change a i • laplacianoClásico (candidato326 D (b i)) (WithLp.toLp 2 ![1, 1]) = 0
  rw [hfun, laplaciano_separable325 _ _ (hP _) (hP _)]
  change a i • (deriv (deriv (P i.1.val)) 1 * P i.2.val 1 +
    P i.1.val 1 * deriv (deriv (P i.2.val)) 1) = 0
  simp [P]

theorem seminorma326_eq_zero_iff {D : ℕ} (a : Coeficientes324 D) :
    seminorma326 D a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    let v : Plano := WithLp.toLp 2 ![1, 1]
    have hv : v ∈ closure cuadrado := by
      rw [clausura_cuadrado]
      intro i
      fin_cases i <;> norm_num [v, PiLp.toLp_apply]
    have hz : (0 : Plano) ∈ cuadrado := by
      intro i
      change (-1 : ℝ) < 0 ∧ (0 : ℝ) < 1
      norm_num
    have hall : EqOn (laplaciano326 D a) (fun _ => laplaciano326 D a 0) cuadrado := by
      intro x hx
      have hd := seminormaInterior_cota _ _ _ (laplaciano326_holder a)
        (by norm_num : (0 : ℝ) < 1 / 2) x hx 0 hz
      change seminormaInterior cuadrado (1 / 2) (laplaciano326 D a) = 0 at ha
      rw [ha, zero_mul] at hd
      exact sub_eq_zero.mp (abs_nonpos_iff.mp hd)
    have hcont : Continuous (laplaciano326 D a) :=
      (laplacianoClásico_suave _ (candidato326_suave a)).continuous
    have hc := (hall.closure hcont continuous_const) hv
    have hc0 : laplaciano326 D a 0 = 0 := hc.symm.trans (laplaciano326_esquina a)
    exact coeficientes326_eq_zero_of_laplaciano a fun x hx => (hall hx).trans hc0
  · rintro rfl
    exact map_zero _

/-- Equivalencia con la norma usual mediante el mínimo de la seminorma en la esfera. -/
theorem seminorma326_domina_norma (D : ℕ) :
    ∃ c > (0 : ℝ), ∀ a : Coeficientes324 D, c * ‖a‖ ≤ seminorma326 D a := by
  obtain ⟨b, hb, hmin⟩ := (isCompact_sphere (0 : Coeficientes324 D) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num)) (seminorma326_continua D).continuousOn
  have hbn : ‖b‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hb
  refine ⟨seminorma326 D b, ?_, fun a => ?_⟩
  · exact lt_of_le_of_ne (apply_nonneg _ _) (fun he =>
      (by simpa [(seminorma326_eq_zero_iff b).mp he.symm] using hbn : False))
  by_cases ha : a = 0
  · simp [ha]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let u := ‖a‖⁻¹ • a
  have hun : ‖u‖ = 1 := by
    rw [show u = ‖a‖⁻¹ • a from rfl, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le),
      inv_mul_cancel₀ hn.ne']
  have hu : u ∈ Metric.sphere (0 : Coeficientes324 D) 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hun
  have hm := hmin hu
  change _ ≤ seminorma326 D (‖a‖⁻¹ • a) at hm
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le), ← div_eq_inv_mul] at hm
  exact (le_div_iff₀ hn).mp hm

#check seminorma326_eq_zero_iff
#print axioms seminorma326_eq_zero_iff
#print axioms seminorma326_domina_norma


#check funcional326_continuo
#print axioms funcional326_continuo

end TesisPINN

