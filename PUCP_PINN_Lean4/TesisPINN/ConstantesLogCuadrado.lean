import TesisPINN.OcupacionLogaritmica
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Constantes de (3.64) y certificado del umbral de la Proposición 3.15. -/

noncomputable section

namespace TesisPINN

open Real

theorem signo_log_cuadrado_309 : (309 : ℝ) - 54 * Real.log 309 < 0 := by
  have h := Real.exp_bound' (x := 309 / 432) (n := 7) (by norm_num) (by norm_num)
    (by norm_num)
  have hexp : Real.exp (309 / 432) ≤ (1023 / 500 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hp := pow_le_pow_left₀ (Real.exp_nonneg _) hexp 8
  rw [← Real.exp_nat_mul] at hp
  have hlt : Real.exp (309 / 54) < (309 : ℝ) := by
    norm_num at hp ⊢
    exact hp.trans_lt (by norm_num)
  linarith [(Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 309)).2 hlt]

theorem signo_log_cuadrado_310 : 0 < (310 : ℝ) - 54 * Real.log 310 := by
  have h := Real.sum_le_exp_of_nonneg (x := 310 / 432) (by norm_num) 7
  have hexp : (2049 / 1000 : ℝ) ≤ Real.exp (310 / 432) := by
    exact (show (2049 / 1000 : ℝ) ≤ ∑ i ∈ Finset.range 7,
      (310 / 432 : ℝ) ^ i / (i.factorial : ℝ) by
      norm_num [Finset.sum_range_succ, Nat.factorial]).trans h
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2049 / 1000) hexp 8
  rw [← Real.exp_nat_mul] at hp
  have hlt : (310 : ℝ) < Real.exp (310 / 54) := by
    norm_num at hp ⊢
    apply lt_of_lt_of_le _ hp
    norm_num
  linarith [(Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 310)).2 hlt]

/-- La cota tangente `log t ≤ t−1` da la monotonía para `x≥54`. -/
theorem monotona_diferencia_log_cuadrado :
    MonotoneOn (fun x : ℝ => x - 54 * Real.log x) (Set.Ici 54) := by
  intro x hx y _ hxy
  have hx' : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hy' := hx'.trans_le hxy
  have h := Real.log_le_sub_one_of_pos (div_pos hy' hx')
  rw [Real.log_div hy'.ne' hx'.ne', sub_le_iff_le_add] at h
  have h' : x * (Real.log y - Real.log x) ≤ y - x := by
    have hh := mul_le_mul_of_nonneg_left h hx'.le
    rw [mul_add, mul_sub, mul_div_cancel₀ _ hx'.ne'] at hh
    linarith
  have hh : 0 ≤ Real.log y - Real.log x :=
    sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn hx' hy' hxy)
  have hmul := mul_le_mul_of_nonneg_right (show (54 : ℝ) ≤ x from hx) hh
  change x - 54 * Real.log x ≤ y - 54 * Real.log y
  nlinarith

theorem umbral_log_cuadrado (m : ℕ) (hm : 310 ≤ m) :
    54 * Real.log (m : ℝ) ≤ m := by
  have hm' : (310 : ℝ) ≤ m := by exact_mod_cast hm
  have h := monotona_diferencia_log_cuadrado (show (310 : ℝ) ∈ Set.Ici 54 by norm_num)
    (show (m : ℝ) ∈ Set.Ici 54 from (by norm_num : (54 : ℝ) ≤ 310).trans hm') hm'
  linarith [signo_log_cuadrado_310]

def radioLogCuadrado (m : ℕ) : ℝ := Real.sqrt (54 * Real.log (m : ℝ) / m)

def factorLogInterior (m : ℕ) : ℝ := (81 * Real.pi / 2) * Real.log (m : ℝ)

def pesoLogInterior (m : ℕ) : ℝ := 3 * radioLogCuadrado m / factorLogInterior m

theorem escalaAuxiliarLogCuadrado_eq (m : ℕ) :
    escalaAuxiliarLog (1 / 9) 2 3 m = Real.sqrt (27 * Real.log (m : ℝ) / m) := by
  rw [escalaAuxiliarLog, Real.sqrt_eq_rpow]
  congr 1
  ring

theorem radioLogCuadrado_eq (m : ℕ) :
    radioCoberturaLog (Real.sqrt 2) (1 / 9) 2 3 m = radioLogCuadrado m := by
  have hl := Real.log_natCast_nonneg m
  unfold radioCoberturaLog escalaAuxiliarLog radioLogCuadrado
  rw [Real.sqrt_eq_rpow, ← Real.mul_rpow (by norm_num) (by positivity), ← Real.sqrt_eq_rpow]
  congr 1
  ring

theorem radioLogCuadrado_admisible (m : ℕ) (hm : 310 ≤ m) :
    RadioLogAdmisible (Real.sqrt 2) (1 / 9) 2 3 1 1 m := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hl : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have he := umbral_log_cuadrado m hm
  have hη : 0 < escalaAuxiliarLog (1 / 9) 2 3 m := by
    unfold escalaAuxiliarLog
    positivity
  have hr : radioCoberturaLog (Real.sqrt 2) (1 / 9) 2 3 m ≤ 1 := by
    rw [radioLogCuadrado_eq, radioLogCuadrado]
    simpa using Real.sqrt_le_sqrt ((div_le_iff₀ hm').2 (by simpa using he) :
      54 * Real.log (m : ℝ) / m ≤ 1)
  have hs : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  exact ⟨by omega, hη, (le_mul_of_one_le_left hη.le hs).trans hr, by linarith,
    mul_pos (by positivity) hη, hr⟩

theorem factorLogInterior_eq (m : ℕ) (hm : 0 < m) :
    3 * (Real.pi / 4) * (m : ℝ) * radioLogCuadrado m ^ 2 = factorLogInterior m := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hl := Real.log_natCast_nonneg m
  rw [radioLogCuadrado, Real.sq_sqrt (by positivity), factorLogInterior]
  field_simp
  ring

theorem producto_pesoLogInterior (m : ℕ) (hm : 3 ≤ m) :
    factorLogInterior m * pesoLogInterior m = 3 * radioLogCuadrado m := by
  have hl : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hc : 0 < factorLogInterior m := by unfold factorLogInterior; positivity
  rw [pesoLogInterior, mul_div_cancel₀ _ hc.ne']

theorem pesoLogInterior_eq (m : ℕ) (hm : 3 ≤ m) :
    pesoLogInterior m = 2 * Real.sqrt 6 / (9 * Real.pi * Real.sqrt ((m : ℝ) * Real.log m)) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hl : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have h54 : Real.sqrt 54 = 3 * Real.sqrt 6 := by
    rw [show (54 : ℝ) = 9 * 6 by norm_num, Real.sqrt_mul (by norm_num)]
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [pesoLogInterior, factorLogInterior, radioLogCuadrado,
    Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num), h54, Real.sqrt_mul hm'.le]
  field_simp [Real.pi_pos.ne', hl.ne', (Real.sqrt_pos.2 hm').ne', (Real.sqrt_pos.2 hl).ne']
  nlinarith [Real.sq_sqrt hl.le]

theorem falloLogCuadrado_eq (m : ℕ) (hm : 3 ≤ m) :
    mayoranteFalloLog 3 m = 1 / (3 * (m : ℝ) ^ 2 * Real.log m) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hl : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  unfold mayoranteFalloLog
  rw [show (1 - 3 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hm'.le, Real.rpow_two]
  field_simp

#check radioLogCuadrado_admisible
#check pesoLogInterior_eq
#print axioms signo_log_cuadrado_309
#print axioms signo_log_cuadrado_310
#print axioms radioLogCuadrado_admisible
#print axioms escalaAuxiliarLogCuadrado_eq
#print axioms pesoLogInterior_eq

end TesisPINN
