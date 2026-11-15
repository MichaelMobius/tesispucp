import TesisPINN.HermiteCancelacion
import TesisPINN.HermiteTensorial
import Mathlib.Analysis.Complex.Liouville

/-! Cotas uniformes de los interpolantes manufacturados. -/

noncomputable section

namespace TesisPINN

open Polynomial
open scoped Polynomial

theorem factorHermite325_formula {m : ℕ} (s : Fin m → Plano) (j : Fin 2)
    (hs : ∀ i, s i j ∈ Set.Icc (-1 : ℝ) 1) {z : ℂ} (hz : ‖z‖ < 4) :
    let t := nodosOrdenadosHermite (fun i => s i j)
    let p := ((factorHermite325 s j).map Complex.ofRealHom).eval
    restoContornoHermite t aManufacturadaCompleja z = aManufacturadaCompleja z - p z := by
  dsimp only
  apply restoContornoHermite_formula _ (nodosOrdenadosHermite _).injective
    (nodosOrdenadosHermite_mem_Icc _ hs) _ aManufacturadaCompleja_entera
  · exact degree_map_le.trans_lt
      (mem_degreeLT.mp (hermiteMuestra (fun i => s i j) datosManufacturados).property)
  · exact factorHermite325_jet_complejo s j
  · exact hz

theorem factorHermite325_resto_uniforme :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ ζ : ℂ, ‖ζ‖ = 4 → ‖aManufacturadaCompleja ζ‖ ≤ M) ∧
    ∀ {m : ℕ} (s : Fin m → Plano) (j : Fin 2),
      (∀ i, s i j ∈ Set.Icc (-1 : ℝ) 1) → ∀ z : ℂ, ‖z‖ ≤ 3 / 2 →
      ‖aManufacturadaCompleja z - ((factorHermite325 s j).map Complex.ofRealHom).eval z‖ ≤
        (4 * M / (4 - 3 / 2)) *
          ((5 : ℝ) / 6) ^ (4 * (nodosDistintosHermite (fun i => s i j)).card) := by
  have hc : Continuous aManufacturadaCompleja := continuous_iff_continuousAt.mpr
    fun w => (aManufacturadaCompleja_entera w).continuousAt
  obtain ⟨M₀, hM₀⟩ := (isCompact_sphere (0 : ℂ) 4).exists_bound_of_continuousOn hc.continuousOn
  let M := max M₀ 0
  have hM (w : ℂ) (hw : ‖w‖ = 4) : ‖aManufacturadaCompleja w‖ ≤ M :=
    (hM₀ w (by simpa [Metric.mem_sphere, dist_zero_right] using hw)).trans (le_max_left _ _)
  refine ⟨M, le_max_right _ _, hM, fun s j hs z hz => ?_⟩
  rw [← factorHermite325_formula s j hs (show ‖z‖ < 4 by linarith)]
  convert restoContornoHermite_cota (nodosOrdenadosHermite _) aManufacturadaCompleja
      (nodosOrdenadosHermite_mem_Icc _ hs) (le_max_right M₀ 0) hM
      (show 0 ≤ (3 : ℝ) / 2 by norm_num) (by norm_num) hz using 1
  rw [show ((3 : ℝ) / 2 + 1) / 3 = 5 / 6 by norm_num]
  ring

theorem factorHermite325_derivadas_resto_uniforme :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} (s : Fin m → Plano) (j : Fin 2),
      (∀ i, s i j ∈ Set.Icc (-1 : ℝ) 1) → ∀ (k : ℕ) (x : ℝ), x ∈ Set.Icc (-1 : ℝ) 1 →
      ‖iteratedDeriv k (aManufacturada - (factorHermite325 s j).eval) x‖ ≤
        (k.factorial : ℝ) * 2 ^ k * C *
          ((5 : ℝ) / 6) ^ (4 * (nodosDistintosHermite (fun i => s i j)).card) := by
  obtain ⟨M, hM, _, hrest⟩ := factorHermite325_resto_uniforme
  let C : ℝ := 4 * M / (4 - 3 / 2)
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (by norm_num) hM) (by norm_num)
  refine ⟨C, hC, fun s j hs k x hx => ?_⟩
  let p := factorHermite325 s j
  let P := (p.map Complex.ofRealHom).eval
  let F := aManufacturadaCompleja - P
  have hA : ContDiff ℂ ⊤ aManufacturadaCompleja :=
    contDiff_iff_contDiffAt.mpr (fun w => (aManufacturadaCompleja_entera w).contDiffAt)
  have hF : ContDiff ℂ ⊤ F := hA.sub (eval_polynomial_contDiff _ ⊤)
  have hE (y : ℝ) : F y = ((aManufacturada - p.eval) y : ℂ) := by
    change aManufacturadaCompleja y - P y = (aManufacturada y - p.eval y : ℝ)
    rw [Complex.ofReal_sub, aManufacturada_extension]
    congr 1
    exact eval_map_apply Complex.ofRealHom y
  have hb (w : ℂ) (hw : w ∈ Metric.sphere (x : ℂ) (1 / 2)) :
      ‖F w‖ ≤ C * ((5 : ℝ) / 6) ^ (4 * (nodosDistintosHermite (fun i => s i j)).card) := by
    apply hrest s j hs
    have hw' : ‖w - (x : ℂ)‖ = 1 / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
    have hx' : ‖(x : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, Real.norm_eq_abs] using abs_le.mpr hx
    calc
      ‖w‖ = ‖w - (x : ℂ) + (x : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (by rw [hw']; linarith)
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (show 0 < (1 : ℝ) / 2 by norm_num)
    (hF.differentiable (by simp)).differentiableOn.diffContOnCl hb
  rw [iteratedDeriv_eje_real F _ hF ((aManufacturada_suave ⊤).sub
    (eval_polynomial_contDiff p ⊤)) hE, Complex.norm_real] at hh
  convert hh using 1
  rw [div_pow (1 : ℝ) 2 k, one_pow, one_div, div_inv_eq_mul]
  ring

/-- Cota de todas las derivadas reales de orden a lo sumo tres en el intervalo cerrado. -/
theorem factorHermite325_c3_uniforme :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {m : ℕ} (s : Fin m → Plano) (j : Fin 2),
      (∀ i, s i j ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ (k : ℕ), k ≤ 3 → ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        ‖iteratedDeriv k (factorHermite325 s j).eval x‖ ≤ M := by
  classical
  obtain ⟨C, hC, hrest⟩ := factorHermite325_derivadas_resto_uniforme
  have hA (k : Fin 4) : ∃ A : ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖iteratedDeriv (k : ℕ) aManufacturada x‖ ≤ A :=
    isCompact_Icc.exists_bound_of_continuousOn
      ((aManufacturada_suave ⊤).continuous_iteratedDeriv _ (by simp)).continuousOn
  choose A hA using hA
  let N (k : Fin 4) := max (A k) 0 + (k.val.factorial : ℝ) * 2 ^ k.val * C
  have hN (k) : 0 ≤ N k := add_nonneg (le_max_right _ _) (by positivity)
  refine ⟨∑ k, N k, Finset.sum_nonneg fun k _ => hN k, fun s j hs k hk x hx => ?_⟩
  let i : Fin 4 := ⟨k, by omega⟩
  let p := factorHermite325 s j
  have hr := hrest s j hs k x hx
  rw [iteratedDeriv_sub ((aManufacturada_suave ⊤).contDiffAt.of_le (by simp))
    ((eval_polynomial_contDiff p ⊤).contDiffAt.of_le (by simp))] at hr
  have hr' : ‖iteratedDeriv k aManufacturada x - iteratedDeriv k p.eval x‖ ≤
      (k.factorial : ℝ) * 2 ^ k * C :=
    hr.trans (mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num)))
  calc
    ‖iteratedDeriv k p.eval x‖ ≤ ‖iteratedDeriv k aManufacturada x‖ +
        ‖iteratedDeriv k aManufacturada x - iteratedDeriv k p.eval x‖ := by
      exact norm_le_insert _ _
    _ ≤ N i := add_le_add ((hA i x hx).trans (le_max_left _ _)) hr'
    _ ≤ ∑ k, N k := Finset.single_le_sum (fun k _ => hN k) (Finset.mem_univ i)

#check factorHermite325_c3_uniforme
#print axioms factorHermite325_formula
#print axioms factorHermite325_resto_uniforme
#print axioms factorHermite325_derivadas_resto_uniforme
#print axioms factorHermite325_c3_uniforme

end TesisPINN

