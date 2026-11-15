import TesisPINN.TaylorTensorial
import TesisPINN.Proposicion311

/-! Escalas y condiciones de aproximación de la Proposición 3.27. -/

noncomputable section

namespace TesisPINN

open Polynomial Set Filter Asymptotics

def gradoTaylor327 (m : ℕ) : ℕ := ⌈2 * Real.log (m : ℝ) / Real.log 2⌉₊

def escalaComparador327 (m : ℕ) : ℝ := (1 + Real.log (m : ℝ)) ^ 3 / (m : ℝ) ^ 2

def comparadorTaylor327 (m : ℕ) : Plano → ℝ := tensorTaylor (gradoTaylor327 m)

private theorem medio_le_log_dos : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ)⁻¹ by positivity)
  rw [Real.log_inv] at h
  norm_num at h ⊢
  linarith

theorem gradoTaylor327_uno : gradoTaylor327 1 = 0 := by simp [gradoTaylor327]

theorem gradoTaylor327_admisible (m : ℕ) (hm : 1 ≤ m) : gradoTaylor327 m ≤ 4 * m - 1 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl := Real.log_le_sub_one_of_pos (show 0 < (m : ℝ) by linarith)
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm'
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : 2 * Real.log (m : ℝ) / Real.log 2 ≤ 4 * ((m : ℝ) - 1) := by
    apply (div_le_iff₀ h₂).2
    have hh := mul_le_mul_of_nonneg_left medio_le_log_dos
      (show 0 ≤ 4 * ((m : ℝ) - 1) by linarith)
    linarith
  apply Nat.ceil_le.mpr
  push_cast [Nat.cast_sub (show 1 ≤ 4 * m by omega)]
  linarith

theorem escalaTaylor_grado327 (m : ℕ) (hm : 1 ≤ m) :
    escalaTaylor (gradoTaylor327 m) ≤ 64 * escalaComparador327 m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have hl := Real.log_nonneg hm'
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 2 * Real.log (m : ℝ) / Real.log 2 ≤ (gradoTaylor327 m : ℝ) := Nat.le_ceil _
  have hq' := (div_le_iff₀ h₂).mp hq
  have hu := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log (m : ℝ) / Real.log 2 by positivity)
  have hfrac : 2 * Real.log (m : ℝ) / Real.log 2 ≤ 4 * Real.log m := by
    apply (div_le_iff₀ h₂).2
    linarith [mul_le_mul_of_nonneg_left medio_le_log_dos (show 0 ≤ 4 * Real.log m by positivity)]
  have hN : (gradoTaylor327 m : ℝ) + 1 ≤ 4 * (1 + Real.log m) := by
    change (gradoTaylor327 m : ℝ) < 2 * Real.log (m : ℝ) / Real.log 2 + 1 at hu
    linarith
  have hp : (1 / 2 : ℝ) ^ gradoTaylor327 m ≤ ((m : ℝ) ^ 2)⁻¹ := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2), ← Real.exp_nat_mul]
    rw [one_div, Real.log_inv]
    have he : Real.exp (-(2 * Real.log (m : ℝ))) = ((m : ℝ) ^ 2)⁻¹ := by
      rw [Real.exp_neg]
      rw [show 2 * Real.log (m : ℝ) = Real.log m + Real.log m by ring, Real.exp_add, Real.exp_log hm0, pow_two]
    rw [← he]
    apply Real.exp_le_exp.mpr
    linarith
  unfold escalaTaylor escalaComparador327
  calc
    _ ≤ (4 * (1 + Real.log (m : ℝ))) ^ 3 * ((m : ℝ) ^ 2)⁻¹ :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hN 3) hp (by positivity) (by positivity)
    _ = _ := by ring

theorem comparadorTaylor327_red (m : ℕ) (hm : 1 ≤ m) :
    redManufacturada326 hm (coeficientesTaylor (gradoTaylor327 m)) = comparadorTaylor327 m :=
  (redManufacturada326_eq hm _).trans (tensorTaylor_en_clase (gradoTaylor327_admisible m hm))

theorem comparadorTaylor327_error_c3 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m j k : ℕ, 1 ≤ m → j + k ≤ 3 → ∀ x ∈ closure cuadrado,
      ‖mixtaTaylor j k (comparadorTaylor327 m - solucionManufacturada) x‖ ≤ C * escalaComparador327 m := by
  obtain ⟨A, hA, ha⟩ := tensorTaylor_error_c3
  refine ⟨64 * A, by positivity, fun m j k hm hjk x hx => ?_⟩
  exact (ha _ j k hjk x hx).trans
    ((mul_le_mul_of_nonneg_left (escalaTaylor_grado327 m hm) hA).trans_eq (by ring))

private theorem escalaComparador327_le (m : ℕ) (hm : 1 ≤ m) :
    escalaComparador327 m ≤ 216 / (m : ℝ) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have hp : 0 < (m : ℝ) ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hm0 _
  have hl := Real.log_le_sub_one_of_pos hp
  rw [Real.log_rpow hm0] at hl
  have he : 1 + Real.log (m : ℝ) ≤ 6 * (m : ℝ) ^ (1 / 6 : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm'
  have hpow : ((m : ℝ) ^ (1 / 6 : ℝ)) ^ 3 = (m : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    congr 1
    norm_num
  unfold escalaComparador327
  calc
    _ ≤ (6 * (m : ℝ) ^ (1 / 6 : ℝ)) ^ 3 / (m : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by linarith) he 3) (by positivity)
    _ = (216 * (m : ℝ) ^ (1 / 2 : ℝ)) / (m : ℝ) ^ 2 := by rw [mul_pow, hpow]; norm_num
    _ ≤ (216 * (m : ℝ)) / (m : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (Real.rpow_le_rpow_of_exponent_le hm' (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans_eq
        (Real.rpow_one _)
    _ = _ := by field_simp

private theorem pesosComparador327 (m : ℕ) (hm : 3 ≤ m) :
    ∃ c : ℝ, c = min (2 * Real.sqrt 2 / (3 * Real.pi)) (2 * Real.sqrt 6 / (9 * Real.pi)) ∧
      c / m ≤ pesoRaizInterior (1 / 2) m ∧ c / m ≤ pesoLogInterior m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : 0 < (m : ℝ) := by linarith
  let A := 2 * Real.sqrt 2 / (3 * Real.pi)
  let B := 2 * Real.sqrt 6 / (9 * Real.pi)
  refine ⟨min A B, rfl, ?_, ?_⟩
  · rw [pesoRaizInterior_medio m (by omega)]
    calc
      min A B / m ≤ A / m := div_le_div_of_nonneg_right (min_le_left _ _) hm0.le
      _ = A * (m : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg hm0.le, Real.rpow_one, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hm' (by norm_num)) (by dsimp [A]; positivity)
  · have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hh := Real.log_le_sub_one_of_pos hm0
    have hden : Real.sqrt ((m : ℝ) * Real.log m) ≤ (m : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨hm0.le, (mul_le_mul_of_nonneg_left (show Real.log (m : ℝ) ≤ m by linarith) hm0.le).trans_eq (by ring)⟩
    have hp : 0 < Real.sqrt ((m : ℝ) * Real.log m) := by positivity
    rw [pesoLogInterior_eq m hm]
    calc
      min A B / m ≤ B / m := div_le_div_of_nonneg_right (min_le_right _ _) hm0.le
      _ ≤ B / Real.sqrt ((m : ℝ) * Real.log m) := div_le_div_of_nonneg_left (by dsimp [B]; positivity) hp hden
      _ = _ := by dsimp [B]; ring

theorem escalaComparador327_tolerancias :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 3 ≤ m →
      escalaComparador327 m ≤ A * Real.sqrt (pesoRaizInterior (1 / 2) m) ∧
      escalaComparador327 m ≤ A * Real.sqrt (pesoLogInterior m) := by
  let c := min (2 * Real.sqrt 2 / (3 * Real.pi)) (2 * Real.sqrt 6 / (9 * Real.pi))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨216 / Real.sqrt c, by positivity, fun m hm => ?_⟩
  obtain ⟨c', he, hR, hL⟩ := pesosComparador327 m hm
  change c' = c at he
  subst c'
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : 0 < (m : ℝ) := by linarith
  have hs : 0 ≤ escalaComparador327 m := by
    have := Real.log_nonneg hm'
    unfold escalaComparador327
    positivity
  have hbound (p : ℝ) (hp : c / m ≤ p) :
      escalaComparador327 m ≤ (216 / Real.sqrt c) * Real.sqrt p := by
    have hp0 : 0 ≤ p := (div_nonneg hc.le hm0.le).trans hp
    have hq : (1 / (m : ℝ)) ^ 2 ≤ (1 / (m : ℝ)) := by
      have h := (div_le_one hm0).mpr hm'
      rw [pow_two]
      exact mul_le_of_le_one_right (by positivity) h
    have hs' : escalaComparador327 m ^ 2 ≤ (216 / Real.sqrt c * Real.sqrt p) ^ 2 := by
      calc
        _ ≤ (216 / (m : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hs (escalaComparador327_le m (by omega)) 2
        _ = 216 ^ 2 * (1 / (m : ℝ)) ^ 2 := by ring
        _ ≤ 216 ^ 2 * (1 / (m : ℝ)) := mul_le_mul_of_nonneg_left hq (by norm_num)
        _ = (216 ^ 2 / c) * (c / m) := by field_simp
        _ ≤ (216 ^ 2 / c) * p := mul_le_mul_of_nonneg_left hp (by positivity)
        _ = _ := by rw [mul_pow, div_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hp0]
    exact (sq_le_sq₀ hs (by positivity)).mp hs'
  exact ⟨hbound _ hR, hbound _ hL⟩

theorem comparadorTaylor327_cotas_Poisson :
    ∃ C S : ℝ, 0 ≤ C ∧ 0 ≤ S ∧ ∀ m : ℕ, 1 ≤ m →
      (∀ x ∈ closure cuadrado, |laplacianoClásico (comparadorTaylor327 m) x - fuenteManufacturada x|
        ≤ C * escalaComparador327 m) ∧
      C * escalaComparador327 m ∈ constantesHolderInterior (closure cuadrado) (1 / 2)
        (laplacianoClásico (comparadorTaylor327 m) - fuenteManufacturada) ∧
      EsHolderInterior cuadrado (1 / 2) (laplacianoClásico (comparadorTaylor327 m)) ∧
      seminormaInterior cuadrado (1 / 2) (laplacianoClásico (comparadorTaylor327 m)) ≤ S := by
  obtain ⟨B, S, hB, hS, hb⟩ := tensorTaylor_cotas_Poisson
  refine ⟨64 * B, S, by positivity, hS, fun m hm => ?_⟩
  obtain ⟨hP, hH, hL, hS'⟩ := hb (gradoTaylor327 m)
  have hrate : B * escalaTaylor (gradoTaylor327 m) ≤ 64 * B * escalaComparador327 m :=
    (mul_le_mul_of_nonneg_left (escalaTaylor_grado327 m hm) hB).trans_eq (by ring)
  exact ⟨fun x hx => (hP x hx).trans hrate, ⟨hH.1.trans hrate, fun x hx y hy =>
    (hH.2 x hx y hy).trans (mul_le_mul_of_nonneg_right hrate (Real.rpow_nonneg dist_nonneg _))⟩,
    hL, hS'⟩

theorem perdidaEmpiricaTaylor327_cota :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℕ, 1 ≤ m → ∀ s : Fin m → Plano, (∀ i, s i ∈ cuadrado) →
      perdidaEmpiricaInterior s (laplacianoClásico (comparadorTaylor327 m)) fuenteManufacturada ≤
        B * escalaComparador327 m ^ 2 := by
  obtain ⟨C, _, _, _, hc⟩ := comparadorTaylor327_cotas_Poisson
  refine ⟨C ^ 2, sq_nonneg _, fun m hm s hs => ?_⟩
  let L := laplacianoClásico (comparadorTaylor327 m)
  let E := escalaComparador327 m
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  unfold perdidaEmpiricaInterior
  apply (div_le_iff₀ hm').mpr
  calc
    _ ≤ ∑ _ : Fin m, (C * E) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sq_abs (L (s i) - fuenteManufacturada (s i))]
      exact pow_le_pow_left₀ (abs_nonneg _) ((hc m hm).1 (s i) (subset_closure (hs i))) 2
    _ = _ := by simp [E, Finset.sum_const, nsmul_eq_mul, mul_pow]; ring

theorem escalaComparador327_cuadrado (m : ℕ) :
    escalaComparador327 m ^ 2 = (1 + Real.log (m : ℝ)) ^ 6 / (m : ℝ) ^ 4 := by
  unfold escalaComparador327
  rw [div_pow, ← pow_mul, ← pow_mul]

/-- Cotas de cada parcial y de su seminorma Hölder. La constante controla
la norma C²,¹ᐟ² con la convención de máximo sobre los multiíndices. -/
def CotaC2Holder327 (m : ℕ) (B : ℝ) : Prop :=
  ∀ j k : ℕ, j + k ≤ 2 →
    (∀ x ∈ closure cuadrado, ‖mixtaTaylor j k (comparadorTaylor327 m - solucionManufacturada) x‖ ≤ B) ∧
    B ∈ constantesHolderInterior (closure cuadrado) (1 / 2)
      (mixtaTaylor j k (comparadorTaylor327 m - solucionManufacturada))

theorem comparadorTaylor327_criterio_fuerte :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 3 ≤ m →
      CotaC2Holder327 m (A * Real.sqrt (pesoRaizInterior (1 / 2) m)) ∧
      CotaC2Holder327 m (A * Real.sqrt (pesoLogInterior m)) := by
  obtain ⟨B, hB, hb⟩ := comparadorTaylor327_error_c3
  obtain ⟨C, hC, hc⟩ := tensorTaylor_error_holder
  obtain ⟨T, hT, ht⟩ := escalaComparador327_tolerancias
  let K := max B (64 * C)
  have hK : 0 ≤ K := hB.trans (le_max_left _ _)
  refine ⟨K * T, by positivity, fun m hm => ?_⟩
  have hscale : 0 ≤ escalaComparador327 m := by
    unfold escalaComparador327
    have := Real.log_nonneg (show (1 : ℝ) ≤ m by exact_mod_cast (show 1 ≤ m by omega))
    positivity
  have hbound (p : ℝ) (hp : escalaComparador327 m ≤ T * Real.sqrt p) :
      CotaC2Holder327 m ((K * T) * Real.sqrt p) := by
    intro j k hjk
    have hrate : K * escalaComparador327 m ≤ (K * T) * Real.sqrt p :=
      (mul_le_mul_of_nonneg_left hp hK).trans_eq (by ring)
    have hhold := hc (gradoTaylor327 m) j k hjk
    have hrate' : C * escalaTaylor (gradoTaylor327 m) ≤ (K * T) * Real.sqrt p := calc
      _ ≤ (64 * C) * escalaComparador327 m :=
        (mul_le_mul_of_nonneg_left (escalaTaylor_grado327 m (by omega)) hC).trans_eq (by ring)
      _ ≤ _ := (mul_le_mul_of_nonneg_right (le_max_right _ _) hscale).trans hrate
    exact ⟨fun x hx => (hb m j k (by omega) (by omega) x hx).trans
      ((mul_le_mul_of_nonneg_right (le_max_left _ _) hscale).trans hrate),
      ⟨hhold.1.trans hrate', fun x hx y hy =>
        (hhold.2 x hx y hy).trans (mul_le_mul_of_nonneg_right hrate' (Real.rpow_nonneg dist_nonneg _))⟩⟩
  exact ⟨hbound _ (ht m hm).1, hbound _ (ht m hm).2⟩

/-- La pérdida del comparador satisface la tolerancia variacional para ambos
pesos, uniformemente en la muestra. -/
theorem comparadorTaylor327_tolerancia_empirica :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, 3 ≤ m → ∀ s : Fin m → Plano, (∀ i, s i ∈ cuadrado) →
      let E := perdidaEmpiricaInterior s (laplacianoClásico (comparadorTaylor327 m)) fuenteManufacturada
      E ≤ K * pesoRaizInterior (1 / 2) m ∧ E ≤ K * pesoLogInterior m := by
  obtain ⟨B, hB, hb⟩ := perdidaEmpiricaTaylor327_cota
  obtain ⟨A, hA, ha⟩ := escalaComparador327_tolerancias
  refine ⟨B * A ^ 2, by positivity, fun m hm s hs => ?_⟩
  have hs0 : 0 ≤ escalaComparador327 m := by
    unfold escalaComparador327
    have := Real.log_nonneg (show (1 : ℝ) ≤ m by exact_mod_cast (show 1 ≤ m by omega))
    positivity
  have hbound (p : ℝ) (hp : 0 ≤ p) (hc : escalaComparador327 m ≤ A * Real.sqrt p) :
      perdidaEmpiricaInterior s (laplacianoClásico (comparadorTaylor327 m)) fuenteManufacturada ≤
      B * A ^ 2 * p := calc
    _ ≤ B * escalaComparador327 m ^ 2 := hb m (by omega) s hs
    _ ≤ B * (A * Real.sqrt p) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hc 2) hB
    _ = _ := by rw [mul_pow, Real.sq_sqrt hp, ← mul_assoc]
  have hL : 0 ≤ pesoLogInterior m := by
    rw [pesoLogInterior_eq m hm]
    positivity
  exact ⟨hbound _ (pesoRaizInterior_pos _ _ (by omega)).le (ha m hm).1,
    hbound _ hL (ha m hm).2⟩

/-- Comparador determinista de (3.92)–(3.93) y criterio fuerte (3.56). -/
theorem proposicion327 :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ m : ℕ, 3 ≤ m →
      gradoTaylor327 m ≤ 4 * m - 1 ∧
      comparadorTaylor327 m ∈ range (candidato326 (4 * m - 1)) ∧
      EqOn (comparadorTaylor327 m) 0 (frontier cuadrado) ∧
      (∀ j k : ℕ, j + k ≤ 3 → ∀ x ∈ closure cuadrado,
        ‖mixtaTaylor j k (comparadorTaylor327 m - solucionManufacturada) x‖ ≤ C * escalaComparador327 m) ∧
      CotaC2Holder327 m (A * Real.sqrt (pesoRaizInterior (1 / 2) m)) ∧
      CotaC2Holder327 m (A * Real.sqrt (pesoLogInterior m)) := by
  obtain ⟨C, hC, hc⟩ := comparadorTaylor327_error_c3
  obtain ⟨A, hA, ha⟩ := comparadorTaylor327_criterio_fuerte
  refine ⟨C, A, hC, hA, fun m hm => ?_⟩
  have hdeg := gradoTaylor327_admisible m (by omega)
  exact ⟨hdeg, ⟨coeficientesTaylor (gradoTaylor327 m), tensorTaylor_en_clase hdeg⟩,
    tensorTaylor_dirichlet _, fun j k hjk => hc m j k (by omega) hjk, ha m hm⟩

#check proposicion327
#print axioms comparadorTaylor327_criterio_fuerte
#print axioms comparadorTaylor327_tolerancia_empirica
#print axioms proposicion327


#check comparadorTaylor327_error_c3
#print axioms gradoTaylor327_admisible
#print axioms comparadorTaylor327_red
#print axioms comparadorTaylor327_error_c3
#print axioms escalaComparador327_tolerancias

end TesisPINN

