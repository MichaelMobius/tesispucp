import TesisPINN.TaylorManufacturada
import TesisPINN.ConvergenciaManufacturada

/-! Paso univariado–tensorial en la aproximación de Taylor. -/

noncomputable section

namespace TesisPINN

open Polynomial Set
open scoped Polynomial

def escalaTaylor (N : ℕ) : ℝ := ((N : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ N

theorem escalaTaylor_acotada : ∃ B : ℝ, 0 ≤ B ∧ ∀ N, escalaTaylor N ≤ B := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ 3 * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 3 (by norm_num)
  have hshift := (summable_nat_add_iff 1).2 h
  have hs : Summable escalaTaylor := by
    rw [show escalaTaylor = (fun n : ℕ => 2 * (((n + 1 : ℕ) : ℝ) ^ 3 * (1 / 2 : ℝ) ^ (n + 1))) from by
      funext n
      simp only [escalaTaylor, Nat.cast_add, Nat.cast_one, pow_succ (1 / 2 : ℝ)]
      ring]
    exact hshift.mul_left 2
  have hpos (N : ℕ) : 0 ≤ escalaTaylor N := by unfold escalaTaylor; positivity
  exact ⟨∑' N, escalaTaylor N, tsum_nonneg hpos,
    fun N => hs.le_tsum N fun k _ => hpos k⟩

private theorem cota_derivadas_Icc (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ≤ 3, ∀ t ∈ Icc (-1 : ℝ) 1, ‖iteratedDeriv k f t‖ ≤ B := by
  classical
  have hb (k : Fin 4) : ∃ A : ℝ, ∀ t ∈ Icc (-1 : ℝ) 1, ‖iteratedDeriv (k : ℕ) f t‖ ≤ A :=
    isCompact_Icc.exists_bound_of_continuousOn
      (hf.continuous_iteratedDeriv _ (by simp)).continuousOn
  choose A hA using hb
  let D := ∑ i : Fin 4, max (A i) 0
  refine ⟨D, Finset.sum_nonneg fun _ _ => le_max_right _ _, fun k hk t ht => ?_⟩
  let j : Fin 4 := ⟨k, by omega⟩
  exact (hA j t ht).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun i _ => le_max_right (A i) 0) (Finset.mem_univ j)))

private theorem cota_leibniz (p q : ℝ → ℝ) (hp : ContDiff ℝ ⊤ p) (hq : ContDiff ℝ ⊤ q)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpa : ∀ k ≤ 3, ∀ t ∈ Icc (-1 : ℝ) 1, ‖iteratedDeriv k p t‖ ≤ A)
    (hqb : ∀ k ≤ 3, ∀ t ∈ Icc (-1 : ℝ) 1, ‖iteratedDeriv k q t‖ ≤ B)
    (k : ℕ) (hk : k ≤ 3) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖iteratedDeriv k (fun x => p x * q x) t‖ ≤ 8 * (A * B) := by
  rw [iteratedDeriv_fun_mul (hp.contDiffAt.of_le le_top) (hq.contDiffAt.of_le le_top)]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (A * B) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := Finset.mem_range.mp hi
      simp only [norm_mul, Real.norm_natCast]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hpa i (by omega) t ht) (hqb (k - i) (by omega) t ht) (norm_nonneg _) hA)
        (Nat.cast_nonneg _)
    _ = (2 : ℝ) ^ k * (A * B) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk).trans_eq (by norm_num)) (mul_nonneg hA hB)

def factorTaylor (N : ℕ) (t : ℝ) : ℝ := (1 - t ^ 2) * (taylorManufacturada N).eval t

def factorSenoTaylor (t : ℝ) : ℝ := (1 - t ^ 2) * aManufacturada t

theorem factorTaylor_suave (N : ℕ) : ContDiff ℝ ⊤ (factorTaylor N) :=
  (show ContDiff ℝ ⊤ (fun t : ℝ => 1 - t ^ 2) by fun_prop).mul (eval_polynomial_contDiff _ _)

theorem factorSenoTaylor_suave : ContDiff ℝ ⊤ factorSenoTaylor :=
  (show ContDiff ℝ ⊤ (fun t : ℝ => 1 - t ^ 2) by fun_prop).mul (aManufacturada_suave _)

theorem factoresTaylor_cotas :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ ∀ N k : ℕ, k ≤ 3 → ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv k (factorTaylor N) t‖ ≤ M ∧
      ‖iteratedDeriv k factorSenoTaylor t‖ ≤ M ∧
      ‖iteratedDeriv k (factorTaylor N - factorSenoTaylor) t‖ ≤ C * escalaTaylor N := by
  let w (t : ℝ) := 1 - t ^ 2
  have hw : ContDiff ℝ ⊤ w := by dsimp [w]; fun_prop
  obtain ⟨B, hB, hb⟩ := cota_derivadas_Icc w hw
  obtain ⟨A, hA, ha⟩ := cota_derivadas_Icc factorSenoTaylor factorSenoTaylor_suave
  obtain ⟨C, hC, hc⟩ := resto_taylorManufacturada_c3
  obtain ⟨S, hS, hs⟩ := escalaTaylor_acotada
  let K := 8 * (B * C)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨A + K * S, K, by positivity, hK, fun N k hk t ht => ?_⟩
  let q := (taylorManufacturada N).eval
  have hscale : 0 ≤ escalaTaylor N := by unfold escalaTaylor; positivity
  have hp : ContDiff ℝ ⊤ q := eval_polynomial_contDiff _ _
  have hd : ∀ i ≤ 3, ∀ x ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv i (q - aManufacturada) x‖ ≤ C * escalaTaylor N := by
    intro i hi x hx
    rw [show q - aManufacturada = -(aManufacturada - q) by abel, iteratedDeriv_neg, norm_neg]
    simpa [escalaTaylor, mul_assoc] using hc N i hi x hx
  have heq : factorTaylor N - factorSenoTaylor = fun t => w t * (q - aManufacturada) t := by
    funext t
    simp [factorTaylor, factorSenoTaylor, w, q, mul_sub]
  have he : ‖iteratedDeriv k (factorTaylor N - factorSenoTaylor) t‖ ≤ K * escalaTaylor N := by
    rw [heq]
    exact (cota_leibniz w _ hw (hp.sub (aManufacturada_suave _)) hB
      (mul_nonneg hC hscale) hb hd k hk t ht).trans_eq (by dsimp [K]; ring)
  have hsplit : ‖iteratedDeriv k (factorTaylor N) t - iteratedDeriv k factorSenoTaylor t‖ ≤ K * escalaTaylor N := by
    rw [iteratedDeriv_sub ((factorTaylor_suave N).contDiffAt.of_le le_top)
      (factorSenoTaylor_suave.contDiffAt.of_le le_top)] at he
    exact he
  exact ⟨(norm_le_insert' _ _).trans
      (add_le_add (ha k hk t ht) (hsplit.trans (mul_le_mul_of_nonneg_left (hs N) hK))),
    (ha k hk t ht).trans (le_add_of_nonneg_right (mul_nonneg hK hS)), he⟩

def tensorTaylor (N : ℕ) (x : Plano) : ℝ := factorTaylor N (x 0) * factorTaylor N (x 1)

theorem tensorTaylor_factor (N : ℕ) (x : Plano) :
    tensorTaylor N x = psiCuadrado x *
      ((taylorManufacturada N).eval (x 0) * (taylorManufacturada N).eval (x 1)) := by
  unfold tensorTaylor factorTaylor psiCuadrado
  ring

theorem tensorTaylor_dirichlet (N : ℕ) :
    EqOn (tensorTaylor N) 0 (frontier cuadrado) := by
  intro x hx
  simp [tensorTaylor_factor, psiCuadrado_cero_frontera _ hx]

theorem solucionManufacturada_separableTaylor :
    solucionManufacturada = fun x => factorSenoTaylor (x 0) * factorSenoTaylor (x 1) := by
  funext x
  rw [solucionManufacturada_factorizada]
  unfold factorSenoTaylor psiCuadrado
  ring

def mixtaTaylor (j k : ℕ) (f : Plano → ℝ) (x : Plano) : ℝ :=
  iteratedDeriv j (fun u => iteratedDeriv k (fun v => f (WithLp.toLp 2 ![u, v])) (x 1)) (x 0)

private theorem mixtaTaylor_error (N j k : ℕ) (x : Plano) :
    mixtaTaylor j k (tensorTaylor N - solucionManufacturada) x =
      iteratedDeriv j (factorTaylor N) (x 0) * iteratedDeriv k (factorTaylor N) (x 1) -
      iteratedDeriv j factorSenoTaylor (x 0) * iteratedDeriv k factorSenoTaylor (x 1) := by
  unfold mixtaTaylor
  rw [solucionManufacturada_separableTaylor]
  unfold tensorTaylor
  have h (u : ℝ) : iteratedDeriv k (fun v =>
      factorTaylor N u * factorTaylor N v - factorSenoTaylor u * factorSenoTaylor v) (x 1) =
      factorTaylor N u * iteratedDeriv k (factorTaylor N) (x 1) -
        factorSenoTaylor u * iteratedDeriv k factorSenoTaylor (x 1) := by
    rw [iteratedDeriv_fun_sub
      ((contDiff_const.mul (factorTaylor_suave N)).contDiffAt.of_le le_top)
      ((contDiff_const.mul factorSenoTaylor_suave).contDiffAt.of_le le_top)]
    simp only [iteratedDeriv_const_mul_field]
  simp only [Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, h]
  rw [iteratedDeriv_fun_sub
    (((factorTaylor_suave N).mul contDiff_const).contDiffAt.of_le le_top)
    ((factorSenoTaylor_suave.mul contDiff_const).contDiffAt.of_le le_top)]
  simp only [iteratedDeriv_mul_const_field]

/-- Transferencia de (3.92) a las derivadas mixtas de orden total a lo sumo tres. -/
theorem tensorTaylor_error_c3 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N j k : ℕ, j + k ≤ 3 → ∀ x ∈ closure cuadrado,
      ‖mixtaTaylor j k (tensorTaylor N - solucionManufacturada) x‖ ≤ C * escalaTaylor N := by
  obtain ⟨M, C, hM, hC, hb⟩ := factoresTaylor_cotas
  refine ⟨2 * M * C, by positivity, fun N j k hjk x hx => ?_⟩
  rw [clausura_cuadrado] at hx
  rw [mixtaTaylor_error]
  let a := iteratedDeriv j (factorTaylor N) (x 0)
  let b := iteratedDeriv k (factorTaylor N) (x 1)
  let c := iteratedDeriv j factorSenoTaylor (x 0)
  let d := iteratedDeriv k factorSenoTaylor (x 1)
  obtain ⟨_, hc', hac⟩ := hb N j (by omega) (x 0) (hx 0)
  obtain ⟨hb', _, hbd⟩ := hb N k (by omega) (x 1) (hx 1)
  rw [iteratedDeriv_sub ((factorTaylor_suave N).contDiffAt.of_le le_top)
    (factorSenoTaylor_suave.contDiffAt.of_le le_top)] at hac hbd
  change ‖a * b - c * d‖ ≤ _
  rw [show a * b - c * d = (a - c) * b + c * (b - d) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hpos : 0 ≤ C * escalaTaylor N := by unfold escalaTaylor; positivity
  calc
    _ ≤ C * escalaTaylor N * M + M * (C * escalaTaylor N) :=
      add_le_add (mul_le_mul hac hb' (norm_nonneg _) hpos)
        (mul_le_mul hc' hbd (norm_nonneg _) hM)
    _ = _ := by ring

/-- Los productos de los coeficientes de Taylor llenan el banco rectangular. -/
def coeficientesTaylor {D : ℕ} (N : ℕ) : Coeficientes324 D :=
  fun i => (taylorManufacturada N).coeff i.1 * (taylorManufacturada N).coeff i.2

theorem tensorTaylor_en_clase {D N : ℕ} (hN : N ≤ D) :
    candidato326 D (coeficientesTaylor N) = tensorTaylor N := by
  have hdeg := (taylorManufacturada_grado N).trans_lt (Nat.lt_succ_of_le hN)
  have hev (t : ℝ) : (taylorManufacturada N).eval t =
      ∑ i : Fin (D + 1), (taylorManufacturada N).coeff i * t ^ i.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (taylorManufacturada N).coeff j * t ^ j)]
    exact eval_eq_sum_range' hdeg t
  funext x
  rw [candidato326_eq, tensorTaylor_factor, hev (x 0), hev (x 1)]
  unfold polinomioPlano326 polinomio324
  rw [Finset.sum_mul, Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [coeficientesTaylor, monomio324]
  ring

private theorem producto_lipschitz_cuadrado (p q : ℝ → ℝ)
    (hp : Differentiable ℝ p) (hq : Differentiable ℝ q) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hPA : ∀ t ∈ Icc (-1 : ℝ) 1, ‖p t‖ ≤ A ∧ ‖deriv p t‖ ≤ A)
    (hQB : ∀ t ∈ Icc (-1 : ℝ) 1, ‖q t‖ ≤ B ∧ ‖deriv q t‖ ≤ B)
    {x y : Plano} (hx : x ∈ closure cuadrado) (hy : y ∈ closure cuadrado) :
    ‖p (x 0) * q (x 1) - p (y 0) * q (y 1)‖ ≤ 2 * (A * B) * dist x y := by
  rw [clausura_cuadrado] at hx hy
  have hp0 : ‖p (x 0) - p (y 0)‖ ≤ A * dist x y := by
    refine (Convex.norm_image_sub_le_of_norm_deriv_le (fun t _ => hp t)
      (fun t ht => (hPA t ht).2) (convex_Icc _ _) (hy 0) (hx 0)).trans ?_
    rw [← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (PiLp.dist_apply_le x y 0) hA
  have hq1 : ‖q (x 1) - q (y 1)‖ ≤ B * dist x y := by
    refine (Convex.norm_image_sub_le_of_norm_deriv_le (fun t _ => hq t)
      (fun t ht => (hQB t ht).2) (convex_Icc _ _) (hy 1) (hx 1)).trans ?_
    rw [← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (PiLp.dist_apply_le x y 1) hB
  rw [show p (x 0) * q (x 1) - p (y 0) * q (y 1) =
    (p (x 0) - p (y 0)) * q (x 1) + p (y 0) * (q (x 1) - q (y 1)) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  exact (add_le_add (mul_le_mul hp0 (hQB _ (hx 1)).1 (norm_nonneg _) (by positivity))
    (mul_le_mul (hPA _ (hy 0)).1 hq1 (norm_nonneg _) hA)).trans_eq (by ring)

theorem tensorTaylor_error_holder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N j k : ℕ, j + k ≤ 2 →
      C * escalaTaylor N ∈ constantesHolderInterior (closure cuadrado) (1 / 2)
        (mixtaTaylor j k (tensorTaylor N - solucionManufacturada)) := by
  obtain ⟨M, K, hM, hK, hbound⟩ := factoresTaylor_cotas
  refine ⟨8 * (M * K), by positivity, fun N j k hjk => ?_⟩
  let p := factorTaylor N
  let q := factorSenoTaylor
  let d := p - q
  let C := K * escalaTaylor N
  have hC : 0 ≤ C := by dsimp [C, escalaTaylor]; positivity
  have hp := factorTaylor_suave N
  have hq := factorSenoTaylor_suave
  have hd := hp.sub hq
  have control (f : ℝ → ℝ) (B : ℝ) (hf : ∀ l ≤ 3, ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv l f t‖ ≤ B) (l : ℕ) (hl : l ≤ 2) :
      ∀ t ∈ Icc (-1 : ℝ) 1,
        ‖iteratedDeriv l f t‖ ≤ B ∧ ‖deriv (iteratedDeriv l f) t‖ ≤ B := by
    intro t ht
    exact ⟨hf l (by omega) t ht, by rw [← iteratedDeriv_succ]; exact hf _ (by omega) _ ht⟩
  have hsplit (x : Plano) :
      mixtaTaylor j k (tensorTaylor N - solucionManufacturada) x =
        iteratedDeriv j d (x 0) * iteratedDeriv k p (x 1) +
          iteratedDeriv j q (x 0) * iteratedDeriv k d (x 1) := by
    rw [mixtaTaylor_error]
    unfold d
    rw [iteratedDeriv_sub (hp.contDiffAt.of_le le_top) (hq.contDiffAt.of_le le_top),
      iteratedDeriv_sub (hp.contDiffAt.of_le le_top) (hq.contDiffAt.of_le le_top)]
    ring
  refine ⟨by unfold escalaTaylor; positivity, fun x hx y hy => ?_⟩
  have hdq (l : ℕ) (hl : l ≤ 2) := control d C
    (fun l hl t ht => (hbound N l hl t ht).2.2) l hl
  have h1 := producto_lipschitz_cuadrado _ _
    (hd.differentiable_iteratedDeriv j (by simp)) (hp.differentiable_iteratedDeriv k (by simp))
    hC hM (hdq j (by omega)) (control p M (fun l hl t ht => (hbound N l hl t ht).1)
      k (by omega)) hx hy
  have h2 := producto_lipschitz_cuadrado _ _
    (hq.differentiable_iteratedDeriv j (by simp)) (hd.differentiable_iteratedDeriv k (by simp))
    hM hC (control q M (fun l hl t ht => (hbound N l hl t ht).2.1) j (by omega))
    (hdq k (by omega)) hx hy
  rw [← Real.norm_eq_abs, hsplit, hsplit, add_sub_add_comm, ← Real.sqrt_eq_rpow]
  refine ((norm_add_le _ _).trans (add_le_add h1 h2)).trans ?_
  calc
    _ = (4 * (M * C)) * dist x y := by ring
    _ ≤ (4 * (M * C)) * (2 * √(dist x y)) :=
      mul_le_mul_of_nonneg_left (dist_le_dos_raiz_cuadrado hx hy) (by positivity)
    _ = _ := by dsimp [C]; ring

theorem laplaciano_tensorTaylor_error (N : ℕ) (x : Plano) :
    laplacianoClásico (tensorTaylor N) x - fuenteManufacturada x =
      mixtaTaylor 2 0 (tensorTaylor N - solucionManufacturada) x +
      mixtaTaylor 0 2 (tensorTaylor N - solucionManufacturada) x := by
  rw [← laplaciano_solucionManufacturada, mixtaTaylor_error, mixtaTaylor_error]
  simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
  unfold tensorTaylor
  rw [laplaciano_separable325 _ _ ((factorTaylor_suave N).of_le le_top)
    ((factorTaylor_suave N).of_le le_top)]
  conv_lhs => rw [solucionManufacturada_separableTaylor,
    laplaciano_separable325 _ _ (factorSenoTaylor_suave.of_le le_top)
      (factorSenoTaylor_suave.of_le le_top)]
  ring

/-- Control puntual y de seminorma Hölder del residuo, y del regularizador. -/
theorem tensorTaylor_cotas_Poisson :
    ∃ C S : ℝ, 0 ≤ C ∧ 0 ≤ S ∧ ∀ N,
      (∀ x ∈ closure cuadrado, |laplacianoClásico (tensorTaylor N) x - fuenteManufacturada x|
        ≤ C * escalaTaylor N) ∧
      C * escalaTaylor N ∈ constantesHolderInterior (closure cuadrado) (1 / 2)
        (laplacianoClásico (tensorTaylor N) - fuenteManufacturada) ∧
      EsHolderInterior cuadrado (1 / 2) (laplacianoClásico (tensorTaylor N)) ∧
      seminormaInterior cuadrado (1 / 2) (laplacianoClásico (tensorTaylor N)) ≤ S := by
  obtain ⟨A, hA, ha⟩ := tensorTaylor_error_c3
  obtain ⟨B, hB, hb⟩ := tensorTaylor_error_holder
  obtain ⟨U, hU, hu⟩ := escalaTaylor_acotada
  obtain ⟨F, hF, hf⟩ := datosPoisson325_regulares.2
  let C := max (2 * A) (2 * B)
  have hC : 0 ≤ C := (by positivity : 0 ≤ 2 * A).trans (le_max_left _ _)
  refine ⟨C, C * U + F, hC, by positivity, fun N => ?_⟩
  have hscale : 0 ≤ escalaTaylor N := by unfold escalaTaylor; positivity
  have hI : C * escalaTaylor N ∈ constantesHolderInterior (closure cuadrado) (1 / 2)
      (laplacianoClásico (tensorTaylor N) - fuenteManufacturada) := by
    refine ⟨mul_nonneg hC hscale, fun x hx y hy => ?_⟩
    have h1 := (hb N 2 0 (by decide)).2 x hx y hy
    have h2 := (hb N 0 2 (by decide)).2 x hx y hy
    simp only [Pi.sub_apply, laplaciano_tensorTaylor_error, add_sub_add_comm]
    refine ((abs_add_le _ _).trans (add_le_add h1 h2)).trans ?_
    rw [← add_mul, ← add_mul, ← two_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hscale)
      (Real.rpow_nonneg dist_nonneg _)
  have hU' : C * U + F ∈ constantesHolderInterior cuadrado (1 / 2)
      (laplacianoClásico (tensorTaylor N)) := by
    refine ⟨by positivity, fun x hx y hy => ?_⟩
    let L := laplacianoClásico (tensorTaylor N)
    let f := fuenteManufacturada
    change |L x - L y| ≤ _
    rw [show L x - L y = ((L x - f x) - (L y - f y)) + (f x - f y) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [add_mul]
    exact add_le_add ((hI.2 x (subset_closure hx) y (subset_closure hy)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hu N) hC)
        (Real.rpow_nonneg dist_nonneg _))) (hf x (subset_closure hx) y (subset_closure hy))
  refine ⟨?_, hI, ⟨_, hU'⟩, csInf_le ⟨0, fun _ h => h.1⟩ hU'⟩
  intro x hx
  rw [laplaciano_tensorTaylor_error, ← Real.norm_eq_abs]
  exact ((norm_add_le _ _).trans (add_le_add (ha N 2 0 (by decide) x hx)
    (ha N 0 2 (by decide) x hx))).trans (by
      rw [← add_mul, ← two_mul]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hscale)

#print axioms tensorTaylor_error_holder
#print axioms tensorTaylor_cotas_Poisson


theorem tensorTaylor_grados_parciales (N : ℕ) :
    ∃ q : MvPolynomial Bool ℝ, (∀ b, q.degreeOf b ≤ N) ∧
      ∀ x : Plano, tensorTaylor N x =
        psiCuadrado x * MvPolynomial.eval (fun b => if b then x 0 else x 1) q := by
  let a : Coeficientes324 N := coeficientesTaylor N
  refine ⟨polinomioFormal324 a, polinomioFormal324_degreeOf a, fun x => ?_⟩
  rw [← tensorTaylor_en_clase (D := N) (N := N) le_rfl, candidato326_eq, polinomioFormal324_eval]
  rfl

#print axioms tensorTaylor_grados_parciales

#check tensorTaylor_error_c3
#print axioms tensorTaylor_en_clase
#print axioms tensorTaylor_error_c3

end TesisPINN

