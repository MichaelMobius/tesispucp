import TesisPINN.HermiteRegularidad
import TesisPINN.Proposicion321
import TesisPINN.ProblemaInterior

/-! Regularidad del producto tensorial en el cuadrado cerrado. -/

noncomputable section

namespace TesisPINN

open Polynomial Set

private def factorComparador325 {m : ℕ} (s : Fin m → Plano) (j : Fin 2) (t : ℝ) : ℝ :=
  (1 - t ^ 2) * (factorHermite325 s j).eval t

private theorem factorComparador325_suave {m : ℕ} (s : Fin m → Plano) (j : Fin 2)
    (n : WithTop ℕ∞) : ContDiff ℝ n (factorComparador325 s j) :=
  (show ContDiff ℝ n (fun t : ℝ => 1 - t ^ 2) by fun_prop).mul
    (eval_polynomial_contDiff _ n)

private theorem factorComparador325_uniforme :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {m : ℕ} (s : Fin m → Plano) (j : Fin 2),
      (∀ i, s i j ∈ Icc (-1 : ℝ) 1) →
      ∀ (k : ℕ), k ≤ 3 → ∀ x ∈ Icc (-1 : ℝ) 1,
        ‖iteratedDeriv k (factorComparador325 s j) x‖ ≤ B := by
  classical
  obtain ⟨M, hM, hbound⟩ := factorHermite325_c3_uniforme
  let w (t : ℝ) := 1 - t ^ 2
  have hw (n : WithTop ℕ∞) : ContDiff ℝ n w := by unfold w; fun_prop
  have hb (j : Fin 4) : ∃ A : ℝ, ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv (j : ℕ) w t‖ ≤ A :=
    isCompact_Icc.exists_bound_of_continuousOn
      ((hw ⊤).continuous_iteratedDeriv _ (by simp)).continuousOn
  choose A hA using hb
  let D := ∑ j : Fin 4, max (A j) 0
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ => le_max_right _ _
  refine ⟨8 * (D * M), by positivity, fun s j hs k hk x hx => ?_⟩
  let p := (factorHermite325 s j).eval
  change ‖iteratedDeriv k (fun t => w t * p t) x‖ ≤ _
  rw [iteratedDeriv_fun_mul (hw k).contDiffAt (eval_polynomial_contDiff _ k).contDiffAt]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (D * M) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      let l : Fin 4 := ⟨i, by omega⟩
      have hW := (hA l x hx).trans ((le_max_left _ _).trans
        (Finset.single_le_sum (fun a _ => le_max_right (A a) 0) (Finset.mem_univ l)))
      simp only [norm_mul, Real.norm_natCast]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hW (hbound s j hs (k - i) (by omega) x hx) (norm_nonneg _) hD)
        (Nat.cast_nonneg _)
    _ = (2 : ℝ) ^ k * (D * M) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk).trans_eq (by norm_num))
      (mul_nonneg hD hM)

private theorem comparador325_separable {m : ℕ} (s : Fin m → Plano) :
    comparador325 s = fun x => factorComparador325 s 0 (x 0) * factorComparador325 s 1 (x 1) := by
  funext x
  unfold comparador325 psiCuadrado factorComparador325
  ring

/-- Cota conjunta de todas las derivadas parciales mixtas de orden total a lo sumo tres.
La primera desigualdad corresponde al tensor polinómico y la segunda al comparador. -/
theorem comparador325_c3_uniforme :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {m : ℕ} (s : Fin m → Plano), (∀ i, s i ∈ closure cuadrado) →
      ∀ (a b : ℕ), a + b ≤ 3 → ∀ x ∈ closure cuadrado,
      ‖iteratedDeriv a (fun u => iteratedDeriv b (fun v =>
        (factorHermite325 s 0).eval u * (factorHermite325 s 1).eval v) (x 1)) (x 0)‖ ≤ K ∧
      ‖iteratedDeriv a (fun u => iteratedDeriv b (fun v =>
        comparador325 s (WithLp.toLp 2 ![u, v])) (x 1)) (x 0)‖ ≤ K := by
  obtain ⟨M, hM, hbound⟩ := factorHermite325_c3_uniforme
  obtain ⟨B, hB, hcomp⟩ := factorComparador325_uniforme
  refine ⟨max (M * M) (B * B), (mul_nonneg hM hM).trans (le_max_left _ _),
    fun s hs a b hab x hx => ?_⟩
  have hcoord (i j) : s i j ∈ Icc (-1 : ℝ) 1 := by
    have hi := hs i
    rw [clausura_cuadrado] at hi
    exact hi j
  rw [clausura_cuadrado] at hx
  rw [comparador325_separable]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field, norm_mul]
  exact ⟨(mul_le_mul (hbound s 0 (fun i => hcoord i 0) a (by omega) _ (hx 0))
      (hbound s 1 (fun i => hcoord i 1) b (by omega) _ (hx 1)) (norm_nonneg _) hM).trans
        (le_max_left _ _),
    (mul_le_mul (hcomp s 0 (fun i => hcoord i 0) a (by omega) _ (hx 0))
      (hcomp s 1 (fun i => hcoord i 1) b (by omega) _ (hx 1)) (norm_nonneg _) hB).trans
        (le_max_right _ _)⟩

private theorem laplaciano_comparador325_forma {m : ℕ} (s : Fin m → Plano) (x : Plano) :
    laplacianoClásico (comparador325 s) x =
      iteratedDeriv 2 (factorComparador325 s 0) (x 0) * factorComparador325 s 1 (x 1) +
      factorComparador325 s 0 (x 0) * iteratedDeriv 2 (factorComparador325 s 1) (x 1) := by
  rw [comparador325_separable, laplaciano_separable325 _ _
    (factorComparador325_suave s 0 2) (factorComparador325_suave s 1 2)]
  simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]

theorem dist_le_dos_raiz_cuadrado {x y : Plano}
    (hx : x ∈ closure cuadrado) (hy : y ∈ closure cuadrado) :
    dist x y ≤ 2 * √(dist x y) := by
  rw [clausura_cuadrado] at hx hy
  have hdist₀ (j : Fin 2) : dist (x j) (y j) ≤ 2 := by
    rw [Real.dist_eq, abs_le]
    exact ⟨by linarith [(hx j).1, (hy j).2], by linarith [(hx j).2, (hy j).1]⟩
  have hdist : dist x y ≤ 4 := by
    rw [PiLp.dist_eq_of_L2, Fin.sum_univ_two]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h₀ := pow_le_pow_left₀ dist_nonneg (hdist₀ 0) 2
    have h₁ := pow_le_pow_left₀ dist_nonneg (hdist₀ 1) 2
    linarith
  have he : √(dist x y) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; exact hdist⟩
  nlinarith [Real.sq_sqrt (dist_nonneg (x := x) (y := y)),
    mul_nonneg (Real.sqrt_nonneg (dist x y)) (sub_nonneg.mpr he)]

/-- Regularidad de los datos fijos del problema manufacturado. -/
theorem datosPoisson325_regulares :
    ContDiff ℝ ⊤ solucionManufacturada ∧
      EsHolderInterior (closure cuadrado) (1 / 2) fuenteManufacturada := by
  have hcoord (i : Fin 2) : ContDiff ℝ ⊤ (fun x : Plano => x i) :=
    (EuclideanSpace.proj i : Plano →L[ℝ] ℝ).contDiff
  have hsol : ContDiff ℝ ⊤ solucionManufacturada :=
    ((contDiff_const.mul (hcoord 0)).sin).mul ((contDiff_const.mul (hcoord 1)).sin)
  have hf : ContDiff ℝ ⊤ fuenteManufacturada := contDiff_const.mul hsol
  obtain ⟨B, hB⟩ := cuadrado_acotado.isCompact_closure.exists_bound_of_continuousOn
    (hf.continuous_fderiv (by simp)).continuousOn
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hconv : Convex ℝ (closure cuadrado) := by
    rw [clausura_cuadrado]
    intro x hx y hy a b ha hb hab i
    change a * x i + b * y i ∈ Icc (-1 : ℝ) 1
    exact convex_Icc _ _ (hx i) (hy i) ha hb hab
  refine ⟨hsol, 2 * M, by positivity, fun x hx y hy => ?_⟩
  have hLip : ‖fuenteManufacturada x - fuenteManufacturada y‖ ≤ M * dist x y := by
    rw [dist_eq_norm]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hf.differentiable (by simp) z)
      (fun z hz => (hB z hz).trans (le_max_left _ _)) hconv hy hx
  rw [← Real.norm_eq_abs, ← Real.sqrt_eq_rpow]
  exact hLip.trans ((mul_le_mul_of_nonneg_left (dist_le_dos_raiz_cuadrado hx hy) hM).trans_eq
    (by ring))


/-- La seminorma Hölder exacta está acotado en el cuadrado cerrado,
uniformemente en el tamaño de muestra y las colisiones. -/
theorem laplaciano_comparador325_holder_uniforme :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {m : ℕ} (s : Fin m → Plano), (∀ i, s i ∈ closure cuadrado) →
      EsHolderInterior (closure cuadrado) (1 / 2) (laplacianoClásico (comparador325 s)) ∧
      seminormaInterior (closure cuadrado) (1 / 2) (laplacianoClásico (comparador325 s)) ≤ K := by
  obtain ⟨B, hB, hb⟩ := factorComparador325_uniforme
  refine ⟨8 * (B * B), by positivity, fun s hs => ?_⟩
  have hcoord (i j) : s i j ∈ Icc (-1 : ℝ) 1 := by
    have hi := hs i
    rw [clausura_cuadrado] at hi
    exact hi j
  have hLip (j : Fin 2) (k : ℕ) (hk : k ≤ 2) {u v : ℝ}
      (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
      ‖iteratedDeriv k (factorComparador325 s j) u -
        iteratedDeriv k (factorComparador325 s j) v‖ ≤ B * dist u v := by
    rw [dist_eq_norm]
    exact Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => (factorComparador325_suave s j ⊤).differentiable_iteratedDeriv k (by simp) x)
      (fun x hx => by
        rw [← iteratedDeriv_succ]
        exact hb s j (fun i => hcoord i j) _ (by omega) x hx)
      (convex_Icc _ _) hv hu
  have hC : 8 * (B * B) ∈ constantesHolderInterior (closure cuadrado) (1 / 2)
      (laplacianoClásico (comparador325 s)) := by
    refine ⟨by positivity, fun x hx y hy => ?_⟩
    have hsqrt := dist_le_dos_raiz_cuadrado hx hy
    rw [clausura_cuadrado] at hx hy
    have hprod (k l : ℕ) (hk : k ≤ 2) (hl : l ≤ 2) :
        ‖iteratedDeriv k (factorComparador325 s 0) (x 0) *
            iteratedDeriv l (factorComparador325 s 1) (x 1) -
          iteratedDeriv k (factorComparador325 s 0) (y 0) *
            iteratedDeriv l (factorComparador325 s 1) (y 1)‖ ≤ 2 * (B * B) * dist x y := by
      let a := iteratedDeriv k (factorComparador325 s 0) (x 0)
      let b := iteratedDeriv l (factorComparador325 s 1) (x 1)
      let c := iteratedDeriv k (factorComparador325 s 0) (y 0)
      let d := iteratedDeriv l (factorComparador325 s 1) (y 1)
      have hab : ‖a - c‖ ≤ B * dist x y := (hLip 0 k hk (hx 0) (hy 0)).trans
        (mul_le_mul_of_nonneg_left (PiLp.dist_apply_le x y 0) hB)
      have hbd : ‖b - d‖ ≤ B * dist x y := (hLip 1 l hl (hx 1) (hy 1)).trans
        (mul_le_mul_of_nonneg_left (PiLp.dist_apply_le x y 1) hB)
      have hb' : ‖b‖ ≤ B := hb s 1 (fun i => hcoord i 1) l (by omega) _ (hx 1)
      have hc' : ‖c‖ ≤ B := hb s 0 (fun i => hcoord i 0) k (by omega) _ (hy 0)
      change ‖a * b - c * d‖ ≤ _
      rw [show a * b - c * d = (a - c) * b + c * (b - d) by ring]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      calc
        _ ≤ B * dist x y * B + B * (B * dist x y) :=
          add_le_add (mul_le_mul hab hb' (norm_nonneg _) (by positivity))
            (mul_le_mul hc' hbd (norm_nonneg _) hB)
        _ = _ := by ring
    rw [← Real.norm_eq_abs, laplaciano_comparador325_forma, laplaciano_comparador325_forma,
      add_sub_add_comm, ← Real.sqrt_eq_rpow]
    calc
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add
        (hprod 2 0 le_rfl (by decide)) (hprod 0 2 (by decide) le_rfl))
      _ ≤ _ := by
        rw [show 2 * (B * B) * dist x y + 2 * (B * B) * dist x y =
          (4 * (B * B)) * dist x y by ring]
        convert mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 4 * (B * B) by positivity) using 1
        ring
  exact ⟨⟨_, hC⟩, csInf_le ⟨0, fun _ h => h.1⟩ hC⟩

#print axioms datosPoisson325_regulares
#check laplaciano_comparador325_holder_uniforme
#print axioms laplaciano_comparador325_holder_uniforme


#check comparador325_c3_uniforme
#print axioms comparador325_c3_uniforme

end TesisPINN

