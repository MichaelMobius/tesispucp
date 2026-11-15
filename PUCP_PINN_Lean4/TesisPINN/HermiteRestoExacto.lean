import TesisPINN.TaylorManufacturada

/-! Mayorante de base 2/3 para (3.90), mediante el resto integral y Cauchy. -/

noncomputable section

namespace TesisPINN

open Polynomial Set Filter
open scoped Polynomial Topology

/-- La constante es independiente de las separaciones y del número de nodos.
El grado `N` del producto nodal es cuatro veces el cardinal de la proyección. -/
theorem factorHermite325_resto_c3_base_dos_tercios :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} (s : Fin m → Plano) (j : Fin 2),
      (∀ i, s i j ∈ Icc (-1 : ℝ) 1) →
      let N := 4 * (nodosDistintosHermite (fun i => s i j)).card
      ∀ k : ℕ, k ≤ 3 → ∀ t ∈ Icc (-1 : ℝ) 1,
        ‖iteratedDeriv k (aManufacturada - (factorHermite325 s j).eval) t‖ ≤
          C * ((N : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ N := by
  obtain ⟨M, hM, hM4, _⟩ := factorHermite325_resto_uniforme
  refine ⟨192 * M * Real.exp 1, by positivity, fun s j hs => ?_⟩
  dsimp only
  intro k hk t ht
  let N := 4 * (nodosDistintosHermite (fun i => s i j)).card
  let δ := 1 / ((N : ℝ) + 2)
  let q := factorHermite325 s j
  let p := (q.map Complex.ofRealHom).eval
  let F := aManufacturadaCompleja - p
  let B := 4 * M * Real.exp 1 * (2 / 3 : ℝ) ^ N
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ2 : δ ≤ 1 / 2 := by
    dsimp [δ]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hA : ContDiff ℂ ⊤ aManufacturadaCompleja :=
    contDiff_iff_contDiffAt.mpr fun x => (aManufacturadaCompleja_entera x).contDiffAt
  have hF : ContDiff ℂ ⊤ F := hA.sub (eval_polynomial_contDiff _ _)
  have hpow : ((1 + δ + 1) / 3) ^ N ≤ Real.exp 1 * (2 / 3 : ℝ) ^ N := by
    have hsmall : (1 + δ / 2) ^ N ≤ Real.exp 1 := by
      calc
        _ ≤ (1 + δ) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ ≤ (1 + δ) ^ (N + 1) := pow_le_pow_right₀ (by linarith) (Nat.le_succ _)
        _ ≤ _ := potencia_uno_mas_inverso N
    rw [show (1 + δ + 1) / 3 = (1 + δ / 2) * (2 / 3 : ℝ) by ring, mul_pow]
    exact mul_le_mul_of_nonneg_right hsmall (by positivity)
  have hb (z : ℂ) (hz : z ∈ Metric.sphere (t : ℂ) δ) : ‖F z‖ ≤ B := by
    have hzt : ‖z - (t : ℂ)‖ = δ := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have ht' : ‖(t : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, Real.norm_eq_abs] using abs_le.mpr ht
    have hzn : ‖z‖ ≤ 1 + δ := by linarith [norm_sub_norm_le z (t : ℂ)]
    change ‖aManufacturadaCompleja z - ((factorHermite325 s j).map Complex.ofRealHom).eval z‖ ≤ _
    rw [← factorHermite325_formula s j hs (show ‖z‖ < 4 by linarith)]
    have hh := restoContornoHermite_cota (nodosOrdenadosHermite _) aManufacturadaCompleja
      (nodosOrdenadosHermite_mem_Icc _ hs) hM hM4 (show 0 ≤ 1 + δ by positivity)
      (show 1 + δ < 4 by linarith) hzn
    refine hh.trans ?_
    change 4 * (M * ((1 + δ + 1) / 3) ^ N / (4 - (1 + δ))) ≤ B
    calc
      _ ≤ 4 * (M * ((1 + δ + 1) / 3) ^ N) :=
        mul_le_mul_of_nonneg_left (div_le_self (by positivity) (by linarith)) (by norm_num)
      _ ≤ 4 * (M * (Real.exp 1 * (2 / 3 : ℝ) ^ N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hM) (by norm_num)
      _ = B := by dsimp [B]; ring
  have hc := cota_cauchy_radio_grado F (hF.differentiable (by simp)) N k hk (t : ℂ) B
    (by dsimp [B]; positivity) hb
  have he (x : ℝ) : F x = ((aManufacturada - q.eval) x : ℝ) := by
    change aManufacturadaCompleja x - p (x : ℂ) = ((aManufacturada x - q.eval x : ℝ) : ℂ)
    rw [Complex.ofReal_sub, aManufacturada_extension]
    congr 1
    exact eval_map_apply Complex.ofRealHom x
  rw [iteratedDeriv_eje_real F _ hF ((aManufacturada_suave _).sub
    (eval_polynomial_contDiff _ _)) he, Complex.norm_real] at hc
  apply hc.trans_eq
  change _ = 192 * M * Real.exp 1 * ((N : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ N
  dsimp [B]
  ring

#check factorHermite325_resto_c3_base_dos_tercios
#print axioms factorHermite325_resto_c3_base_dos_tercios

end TesisPINN

