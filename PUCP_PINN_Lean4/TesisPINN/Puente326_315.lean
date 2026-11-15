import TesisPINN.Corolario326
import TesisPINN.Proposicion315

/-! Aplicación interior de la cobertura logarítmica a la clase neuronal de C3.26. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Filter Asymptotics
open scoped Topology

/-- Los mínimos del funcional logarítmico en la clase de L3.24 satisfacen la
tasa poblacional de P3.15 para el dato manufacturado, con tolerancias nulas. -/
theorem perdida_minimizadores326_logaritmica {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Muestreo38 P medidaUniformeCuadrado) :
    ∃ a : ∀ m : ℕ, (Fin m → Plano) → Coeficientes324 (4 * m - 1),
      (∀ m, Measurable (a m)) ∧
      (∀ m : ℕ, 310 ≤ m → ∀ s : Fin m → Plano,
        IsMinOn (funcional326 s (pesoLogInterior m)) Set.univ (a m s)) ∧
      ∀ᵐ ω ∂P,
        (fun m => perdidaPoissonInterior
          (laplaciano326 (4 * m - 1) (a m (prefijoPoisson P Z m ω))) fuenteManufacturada)
            =O[atTop] escalaPerdida315 := by
  have hpos (m : ℕ) (hm : 310 ≤ m) : 0 < pesoLogInterior m := by
    have hlog : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hr : 0 < radioLogCuadrado m := by
      simpa only [radioLogCuadrado_eq] using (radioLogCuadrado_admisible m hm).2.2.2.2.1
    have hfac : 0 < factorLogInterior m := by unfold factorLogInterior; positivity
    unfold pesoLogInterior
    positivity
  let peso (m : ℕ) := if 310 ≤ m then pesoLogInterior m else 1
  have hpeso (m : ℕ) : 0 < peso m := by
    by_cases hm : 310 ≤ m
    · simpa only [peso, if_pos hm] using hpos m hm
    · simp [peso, hm]
  have hsel (m : ℕ) := existe_minimizador_borel326 (4 * m - 1) m (peso m) (hpeso m)
  choose a ha haMin using hsel
  have hmin (m : ℕ) (hm : 310 ≤ m) (s : Fin m → Plano) :
      IsMinOn (funcional326 s (pesoLogInterior m)) Set.univ (a m s) := by
    simpa only [peso, if_pos hm] using haMin m s
  refine ⟨a, ha, hmin, ?_⟩
  obtain ⟨R, _, hR⟩ := cotas_minimizador326
  have hf : EsHolderInterior cuadrado (1 / 2) fuenteManufacturada := by
    obtain ⟨C, hC, h⟩ := datosPoisson325_regulares.2
    exact ⟨C, hC, fun x hx y hy => h x (subset_closure hx) y (subset_closure hy)⟩
  have hs := muestras_en_soporte_ae P medidaUniformeCuadrado Z.Z cuadrado
    medidaUniformeCuadrado_concentrada Z.medible Z.ley
  filter_upwards [(ocupacion315 P Z).2, hs] with ω hc hω
  apply isBigO_de_cota_eventual _ _
    (3 * Real.sqrt 54 * (R + seminormaInterior cuadrado (1 / 2) fuenteManufacturada ^ 2))
  filter_upwards [hc, eventually_ge_atTop 310] with m hmCov hm
  let s := prefijoPoisson P Z m ω
  let L := laplaciano326 (4 * m - 1) (a m s)
  have hsup : ∀ i, s i ∈ cuadrado := fun i => hω i
  have hJ := (hR (by omega) s hsup (pesoLogInterior m) (hpos m hm)
    (a m s) (hmin m hm s)).1
  have hpop := cotaPoissonInterior hm s hsup hmCov L fuenteManufacturada
    (laplaciano326_holder (a m s)) hf
  have hlog : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hfac : 0 ≤ factorLogInterior m := by unfold factorLogInterior; positivity
  refine ⟨perdidaInterior_nonneg _ _ _, Real.sqrt_nonneg _, ?_⟩
  calc
    _ ≤ factorLogInterior m * (pesoLogInterior m * R) +
        3 * radioLogCuadrado m * seminormaInterior cuadrado (1 / 2) fuenteManufacturada ^ 2 :=
      hpop.trans (add_le_add_left (mul_le_mul_of_nonneg_left hJ hfac) _)
    _ = _ := by
      rw [← mul_assoc (factorLogInterior m), producto_pesoLogInterior m (by omega),
        radioLogCuadrado_eq_escala]
      ring

#check perdida_minimizadores326_logaritmica
#print axioms perdida_minimizadores326_logaritmica

end TesisPINN

