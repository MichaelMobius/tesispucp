import TesisPINN.Corolario326
import TesisPINN.Proposicion311

/-! Cobertura raíz para los mínimos de C3.26 con el peso original. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Filter Asymptotics Set
open scoped Topology

/-- El comparador exacto de Hermite da las tres cotas de (3.91).
La estimación de cobertura de P3.11 da (3.94) para estos mismos mínimos. -/
theorem perdida_minimizadores326_raiz {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Muestreo38 P medidaUniformeCuadrado) :
    ∃ a : ∀ m : ℕ, (Fin m → Plano) → Coeficientes324 (4 * m - 1),
      (∀ m, Measurable (a m)) ∧
      (∀ m, 1 ≤ m → ∀ s : Fin m → Plano,
        IsMinOn (funcional326 s (pesoRaizInterior (1 / 2) m)) univ (a m s) ∧
        ∀ b : Coeficientes324 (4 * m - 1),
          IsMinOn (funcional326 s (pesoRaizInterior (1 / 2) m)) univ b →
          normaEuclideaCuad326 (a m s) ≤ normaEuclideaCuad326 b) ∧
      (∃ R : ℝ, 0 ≤ R ∧ ∀ m, 1 ≤ m → ∀ s : Fin m → Plano, (∀ i, s i ∈ cuadrado) →
        funcional326 s (pesoRaizInterior (1 / 2) m) (a m s) ≤ pesoRaizInterior (1 / 2) m * R ∧
        perdidaEmpiricaInterior s (laplaciano326 (4 * m - 1) (a m s)) fuenteManufacturada ≤
          pesoRaizInterior (1 / 2) m * R ∧ seminorma326 (4 * m - 1) (a m s) ^ 2 ≤ R) ∧
      ∀ᵐ ω ∂P,
        (fun m => perdidaPoissonInterior
          (laplaciano326 (4 * m - 1) (a m (prefijoPoisson P Z m ω))) fuenteManufacturada)
            =O[atTop] (fun m : ℕ => (m : ℝ) ^ (-(1 / 4 : ℝ))) := by
  let peso (m : ℕ) := if 1 ≤ m then pesoRaizInterior (1 / 2) m else 1
  have hpeso (m : ℕ) : 0 < peso m := by
    by_cases hm : 1 ≤ m
    · simpa [peso, hm] using pesoRaizInterior_pos (1 / 2) m hm
    · simp [peso, hm]
  choose a ha haMin using fun m =>
    existe_minimizador_borel_menorNorma326 (4 * m - 1) m (peso m) (hpeso m)
  have hmin (m : ℕ) (hm : 1 ≤ m) (s : Fin m → Plano) :
      IsMinOn (funcional326 s (pesoRaizInterior (1 / 2) m)) univ (a m s) ∧
      ∀ b : Coeficientes324 (4 * m - 1),
        IsMinOn (funcional326 s (pesoRaizInterior (1 / 2) m)) univ b →
        normaEuclideaCuad326 (a m s) ≤ normaEuclideaCuad326 b := by
    simpa [peso, hm] using haMin m s
  obtain ⟨R, hR₀, hR⟩ := cotas_minimizador326
  have hbounds (m : ℕ) (hm : 1 ≤ m) (s : Fin m → Plano) (hs : ∀ i, s i ∈ cuadrado) :=
    hR hm s hs _ (pesoRaizInterior_pos _ m hm) (a m s) (hmin m hm s).1
  refine ⟨a, ha, hmin, ⟨R, hR₀, hbounds⟩, ?_⟩
  have hf : EsHolderInterior cuadrado (1 / 2) fuenteManufacturada := by
    obtain ⟨C, hC, h⟩ := datosPoisson325_regulares.2
    exact ⟨C, hC, fun x hx y hy => h x (subset_closure hx) y (subset_closure hy)⟩
  have hs := muestras_en_soporte_ae P medidaUniformeCuadrado Z.Z cuadrado
    medidaUniformeCuadrado_concentrada Z.medible Z.ley
  filter_upwards [(ocupacion311 P Z).2, hs] with ω hc hω
  apply isBigO_de_cota_eventual _ _ (3 * (3 * Real.sqrt 2) *
    (R + seminormaInterior cuadrado (1 / 2) fuenteManufacturada ^ 2))
  filter_upwards [hc, eventually_ge_atTop 324] with m hmCov hm
  let s := prefijoPoisson P Z m ω
  let L := laplaciano326 (4 * m - 1) (a m s)
  have hsup : ∀ i, s i ∈ cuadrado := fun i => hω i
  have hm' : 0 < m := by omega
  have hJ := (hbounds m hm' s hsup).1
  have hpop := perdida311_bajo_cobertura hm (1 / 2) (by norm_num) s hsup hmCov L
    fuenteManufacturada (laplaciano326_holder (a m s)) hf
  rw [show 2 * (1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] at hpop
  refine ⟨perdidaInterior_nonneg _ _ _, Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_⟩
  calc
    _ ≤ factorRaizInterior m * (pesoRaizInterior (1 / 2) m * R) +
        3 * radioRaizCuadrado m * seminormaInterior cuadrado (1 / 2) fuenteManufacturada ^ 2 :=
      hpop.trans (add_le_add_left
        (mul_le_mul_of_nonneg_left hJ (factorRaizInterior_pos m hm').le) _)
    _ = _ := by
      rw [← mul_assoc (factorRaizInterior m), producto_pesoRaizInterior _ m hm',
        show 2 * (1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one, radioRaizCuadrado_eq m hm']
      ring

#check perdida_minimizadores326_raiz
#print axioms perdida_minimizadores326_raiz

end TesisPINN
