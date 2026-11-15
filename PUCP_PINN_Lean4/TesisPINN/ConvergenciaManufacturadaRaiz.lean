import TesisPINN.ConvergenciaManufacturada
import TesisPINN.Puente326_311

/-! Convergencia manufacturada con el peso raíz de (3.94). -/

noncomputable section

namespace TesisPINN

open MeasureTheory Filter Asymptotics Set EllipticPdes EllipticPdes.H1Graph
open scoped Topology

/-- El selector del funcional con peso raíz da la tasa de (3.94) y la
estimación simultánea en las dos normas de C3.23. -/
theorem convergencia_neuronal_manufacturada_raiz {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Muestreo38 P medidaUniformeCuadrado) :
    ∃ a : ∀ m : ℕ, (Fin m → Plano) → Coeficientes324 (4 * m - 1),
      (∀ m, Measurable (a m) ∧ Measurable (fun s => pesoSalida324 (a m s))) ∧
      (∀ m (hm : 1 ≤ m) (s : Fin m → Plano),
        EqOn (redManufacturada326 hm (a m s)) 0 (frontier cuadrado) ∧
        IsMinOn (fun h : Plano → ℝ => funcional311 (1 / 2) s (laplacianoClásico h)
          fuenteManufacturada) (range (candidato326 (4 * m - 1))) (redManufacturada326 hm (a m s)) ∧
        ∀ b : Coeficientes324 (4 * m - 1),
          IsMinOn (funcional326 s (pesoRaizInterior (1 / 2) m)) univ b →
          normaEuclideaCuad326 (a m s) ≤ normaEuclideaCuad326 b) ∧
      ∀ᵐ ω ∂P,
        let b := fun m => a m (prefijoPoisson P Z m ω)
        let e := fun m => (errorSobolevManufacturado (b m) : H1Graph volume cuadrado)
        (fun m => perdidaPoissonInterior (laplaciano326 (4 * m - 1) (b m)) fuenteManufacturada)
          =O[atTop] (fun m : ℕ => (m : ℝ) ^ (-(1 / 4 : ℝ))) ∧
        (fun m => ‖e m‖ + normaEsencial323 (e m)) =O[atTop]
          (fun m : ℕ => (m : ℝ) ^ (-(1 / 8 : ℝ))) ∧
        Tendsto (fun m => (candidatoSobolev326 (b m) : H1Graph volume cuadrado))
          atTop (𝓝 (solucionSobolevManufacturada : H1Graph volume cuadrado)) ∧
        Tendsto (fun m => normaEsencial323 (e m)) atTop (𝓝 0) ∧
        (∀ m, supResiduo (closure cuadrado) (candidato326 _ (b m) - solucionManufacturada) =
          normaEsencial323 (e m)) := by
  obtain ⟨a, hmeas, hmin, _, hrate⟩ := perdida_minimizadores326_raiz P Z
  refine ⟨a, fun m => ⟨hmeas m, (pesosSalida324_continuos _).measurable.comp (hmeas m)⟩,
    ?_, ?_⟩
  · intro m hm s
    rw [redManufacturada326_eq]
    refine ⟨fun x hx => ?_, (minimo326_equiv_clase s _ (a m s)).mp (hmin m hm s).1,
      (hmin m hm s).2⟩
    simp [candidato326_eq, psiCuadrado_cero_frontera _ hx]
  · filter_upwards [hrate] with ω hω
    let b := fun m => a m (prefijoPoisson P Z m ω)
    let E := fun m => perdidaPoissonInterior (laplaciano326 (4 * m - 1) (b m)) fuenteManufacturada
    let e := fun m => (errorSobolevManufacturado (b m) : H1Graph volume cuadrado)
    let r := fun m : ℕ => (m : ℝ) ^ (-(1 / 8 : ℝ))
    have hE (m : ℕ) : 0 ≤ E m := perdidaInterior_nonneg _ _ _
    have hr (m : ℕ) : 0 ≤ r m := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hC : 0 ≤ 2 * constanteSimultanea323 := by
      unfold constanteSimultanea323 constanteH1323
      positivity
    obtain ⟨K, hK, hbound⟩ := isBigO_iff'.mp hω
    let M := (2 * constanteSimultanea323) * Real.sqrt K
    have hsum : ∀ᶠ m in atTop, ‖e m‖ + normaEsencial323 (e m) ≤ M * r m := by
      filter_upwards [hbound] with m hm
      have hpow : 0 ≤ (m : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hle : E m ≤ K * (m : ℝ) ^ (-(1 / 4 : ℝ)) := by
        change ‖E m‖ ≤ K * ‖(m : ℝ) ^ (-(1 / 4 : ℝ))‖ at hm
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hE m), abs_of_nonneg hpow] using hm
      have hrSqrt : Real.sqrt ((m : ℝ) ^ (-(1 / 4 : ℝ))) = r m := by
        dsimp [r]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg m)]
        congr 1
        norm_num
      have hs : Real.sqrt (E m) ≤ Real.sqrt K * r m := by
        simpa only [Real.sqrt_mul hK.le, hrSqrt] using Real.sqrt_le_sqrt hle
      exact (estimacion_simultanea_manufacturada (b m)).1.trans
        (by simpa only [M, mul_assoc] using mul_le_mul_of_nonneg_left hs hC)
    have hInf (m : ℕ) : 0 ≤ normaEsencial323 (e m) := ENNReal.toReal_nonneg
    have hlim : Tendsto r atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (show 0 < (1 / 8 : ℝ) by norm_num)).comp
        tendsto_natCast_atTop_atTop
    have hlim' : Tendsto (fun m => M * r m) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hlim
    refine ⟨hω, isBigO_de_cota_eventual _ _ M (hsum.mono fun m hm =>
      ⟨add_nonneg (norm_nonneg _) (hInf m), hr m, hm⟩), ?_, ?_,
      fun m => (estimacion_simultanea_manufacturada (b m)).2⟩
    · apply tendsto_iff_norm_sub_tendsto_zero.mpr
      exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        (hsum.mono fun m hm => (le_add_of_nonneg_right (hInf m)).trans hm) hlim'
    · exact squeeze_zero' (Eventually.of_forall hInf)
        (hsum.mono fun m hm => (le_add_of_nonneg_left (norm_nonneg (e m))).trans hm) hlim'

#check convergencia_neuronal_manufacturada_raiz
#print axioms convergencia_neuronal_manufacturada_raiz

end TesisPINN
