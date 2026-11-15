import TesisPINN.TransferenciaEnergeticaDimensional
import TesisPINN.Teorema38Dimensional
import TesisPINN.Teorema38Unidimensional
import TesisPINN.PoincareEspectralCuadrado

/-!
# Poisson con Dirichlet fuerte y candidatos Sobolev
-/

noncomputable section

open Set MeasureTheory TopologicalSpace Topology Filter Asymptotics
open EllipticPdes EllipticPdes.H1Graph

namespace TesisPINN

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem estimacion320_de_perdida (U : Opens E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (C : ℝ) (hC : 0 < C)
    (hP : ∀ e : H01 μ (U : Set E),
      ‖fnL (e : H1Graph μ (U : Set E))‖ ≤ C * ‖gradL (e : H1Graph μ (U : Set E))‖)
    (h u : H1Graph μ (U : Set E)) (Lh f : Lp ℝ 2 (μ.restrict (U : Set E)))
    (he : h - u ∈ H01 μ (U : Set E))
    (hh : HasDistributionalLaplacianDimensional U μ h Lh)
    (hu : HasDistributionalLaplacianDimensional U μ u f)
    (D : DensidadInferiorEn (μ.restrict (U : Set E))) (v : E → ℝ)
    (hv : ⇑(Lh - f) =ᵐ[μ.restrict (U : Set E)] v)
    (hi : Integrable (fun x => (v x) ^ 2) D.ley)
    (lr loss : ℝ) (hlr : 0 < lr)
    (hdom : lr * (∫ x, (v x) ^ 2 ∂D.ley) ≤ loss) :
    ‖h - u‖ ≤ (C * Real.sqrt (1 + C ^ 2) / Real.sqrt (D.rho0 * lr)) * Real.sqrt loss := by
  have hE := estimacion320_dimensional U μ C hC hP h u Lh f he hh hu
  have hL := cota_L2_de_perdida_dimensional D (Lh - f) v hv hi lr loss hlr hdom
  calc
    ‖h - u‖ ≤ C * Real.sqrt (1 + C ^ 2) * ‖Lh - f‖ := hE
    _ ≤ C * Real.sqrt (1 + C ^ 2) * (Real.sqrt loss / Real.sqrt (D.rho0 * lr)) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    _ = _ := by ring

/-- (3.74) seguida de la comparación con el supremo puntual. -/
theorem estimacion320_de_supremo (U : Opens E) (μ : Measure E) [μ.IsAddHaarMeasure]
    [IsFiniteMeasure (μ.restrict (U : Set E))] (C : ℝ) (hC : 0 < C)
    (hP : ∀ e : H01 μ (U : Set E),
      ‖fnL (e : H1Graph μ (U : Set E))‖ ≤ C * ‖gradL (e : H1Graph μ (U : Set E))‖)
    (h u : H1Graph μ (U : Set E)) (Lh f : Lp ℝ 2 (μ.restrict (U : Set E)))
    (he : h - u ∈ H01 μ (U : Set E))
    (hh : HasDistributionalLaplacianDimensional U μ h Lh)
    (hu : HasDistributionalLaplacianDimensional U μ u f)
    (v : E → ℝ) (hv : ⇑(Lh - f) =ᵐ[μ.restrict (U : Set E)] v)
    (hb : ∃ M : ℝ, ∀ x ∈ (U : Set E), |v x| ≤ M) :
    ‖h - u‖ ≤ C * Real.sqrt (1 + C ^ 2) * Real.sqrt (μ.real (U : Set E)) *
      supResiduo (U : Set E) v := by
  have hE := estimacion320_dimensional U μ C hC hP h u Lh f he hh hu
  have hL := cota_L2_de_supremo_puntual μ (U : Set E) U.isOpen.measurableSet
    (Lh - f) v hv hb
  rw [mul_assoc (C * Real.sqrt (1 + C ^ 2))]
  exact hE.trans (mul_le_mul_of_nonneg_left hL (by positivity))

private theorem residuo_acotado_de_cota_holder {X : Type*} [PseudoMetricSpace X]
    {U : Set X} (hU : Bornology.IsBounded U) (hUne : U.Nonempty)
    (v : X → ℝ) (M α : ℝ) (hM : 0 ≤ M) (hα : 0 ≤ α)
    (hH : ∀ x ∈ U, ∀ y ∈ U, |v x - v y| ≤ M * dist x y ^ α) :
    ∃ B : ℝ, ∀ x ∈ U, |v x| ≤ B := by
  obtain ⟨x₀, hx₀⟩ := hUne
  refine ⟨M * (Metric.diam U) ^ α + |v x₀|, fun x hx => ?_⟩
  calc
    |v x| ≤ |v x - v x₀| + |v x₀| := by
      simpa only [sub_add_cancel] using abs_add_le (v x - v x₀) (v x₀)
    _ ≤ _ := add_le_add ((hH x hx x₀ hx₀).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (Metric.dist_le_diam_of_mem hU hx hx₀) hα) hM)) le_rfl

set_option maxHeartbeats 1200000 in
/-- (3.72)–(3.75) sobre los mismos prefijos y selecciones de T3.8.
El operador residual se identifica con el laplaciano por igualdad casi en
todas partes de sus representantes. La condición afín se da en H₀¹. -/
theorem teorema320_dimension_ge_dos
    {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (hd : 2 ≤ d)
    (U : Opens (EspacioEliptico d))
    (D : DensidadInferiorEn (volume.restrict (U : Set (EspacioEliptico d))))
    [IsProbabilityMeasure D.ley]
    (μb : Measure (EspacioEliptico d)) [IsProbabilityMeasure μb] (ε₀ : ℝ)
    (dr : DatosMasaDimensional D.ley (U : Set (EspacioEliptico d)) (Real.sqrt d) (d : ℝ) ε₀)
    (db : DatosMasaDimensional μb (frontier (U : Set (EspacioEliptico d))) (Real.sqrt d) ((d : ℝ) - 1) ε₀)
    (Zr : Muestreo38 P D.ley) (Zb : Muestreo38 P μb)
    (op : Operadores38 H (EspacioEliptico d) (EspacioEliptico d))
    (hε₀ : 0 < ε₀)
    (grafo : H → W12 volume (U : Set (EspacioEliptico d)))
    (u : W12 volume (U : Set (EspacioEliptico d)))
    (lap : H → Lp ℝ 2 (volume.restrict (U : Set (EspacioEliptico d))))
    (f : Lp ℝ 2 (volume.restrict (U : Set (EspacioEliptico d))))
    (hsol : HasDistributionalLaplacianDimensional U volume u f)
    (hf : ⇑f =ᵐ[volume.restrict (U : Set (EspacioEliptico d))] op.f)
    (mr mb : ℕ → ℕ) (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (hgr : ∀ᶠ n in atTop, n ≤ mr n) (hgb : ∀ᶠ n in atTop, n ≤ mb n)
    (lr lb α Sf Sg K : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α) (hK : 0 < K)
    (hrel : ∀ᶠ n in atTop, (mr n : ℝ) ≤ K * (mb n : ℝ) ^ ((d : ℝ) / ((d : ℝ) - 1)))
    (Hm : ℕ → Set H) (h v : ∀ n, Ω → Hm n)
    (hhMeas : ∀ n, Measurable (fun ω => (h n ω : H)))
    (hvMeas : ∀ n, Measurable (fun ω => (v n ω : H)))
    (hHolder : ∀ n, op.CotasHolder34 (Hm n) (U : Set (EspacioEliptico d)) (frontier (U : Set (EspacioEliptico d))) α Sf Sg)
    (hDiri : ∀ n, ∀ k ∈ Hm n,
      (grafo k).val - u.val ∈
        H01 volume (U : Set (EspacioEliptico d)))
    (hLap : ∀ n, ∀ k ∈ Hm n, HasDistributionalLaplacianDimensional U volume (grafo k) (lap k))
    (hRep : ∀ n, ∀ k ∈ Hm n, ⇑(lap k) =ᵐ[volume.restrict (U : Set (EspacioEliptico d))] op.L k) :
    let Pn := fun ω n => op.problemaRaizDimensional D.ley μb (hmr n) (hmb n) (Real.sqrt d)
      (d : ℝ) ((d : ℝ) - 1) dr.C db.C dr.c db.c lr lb α
      (Real.sqrt_pos.2 (Nat.cast_pos.mpr (by omega))) dr.C_pos dr.c_pos db.c_pos hlr hlb true
      (fun i => Zr.Z i ω) (fun i => Zb.Z i ω)
    (∀ᵐ ω ∂P, ∃ R : ℝ, 0 ≤ R ∧ ∀ n,
      (Pn ω n).EsMinimizadorGlobal (Hm n) (h n ω : H) ∧
      (Pn ω n).ComparadorExacto (Hm n) (v n ω : H) ∧
      (Pn ω n).regularidadTotal (v n ω : H) ≤ R) →
    ∀ᵐ ω ∂P,
      let e := fun n => (grafo (h n ω : H)).val
      ((fun n => (Pn ω n).perdidaPoblacional (h n ω : H)) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α / (d : ℝ))))) ∧
      Tendsto e atTop (𝓝 u.val) ∧
      ((fun n => ‖e n - u.val‖) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α / (2 * (d : ℝ)))))) ∧
      ((fun n => ‖e n - u.val‖) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α ^ 2 / ((d : ℝ) * (2 * α + (d : ℝ))))))) := by
  intro Pn hvar
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  let V : Set (EspacioEliptico d) := U
  let Γ := frontier V
  let : IsFiniteMeasure (volume.restrict V) :=
    isFiniteMeasure_restrict.mpr ((measure_mono subset_closure).trans_lt
      dr.acotado.isCompact_closure.measure_lt_top).ne
  obtain ⟨C, hC, hP⟩ := exists_poincare_constant (μ := volume) dr.acotado
  let A := C * Real.sqrt (1 + C ^ 2)
  let Kρ := A / Real.sqrt (D.rho0 * lr)
  let Ksup := A * Real.sqrt (volume.real V)
  have h38 := teorema38_dimension_ge_dos P D.ley μb V Γ d hd ε₀ dr db Zr Zb op hε₀
    mr mb hmr hmb hgr hgb lr lb α Sf Sg K hlr hlb hα hK hrel Hm h v hhMeas hvMeas hHolder hvar
  filter_upwards [h38] with ω hω
  obtain ⟨hLoss, ⟨hLim, _⟩, hSup, _⟩ := hω
  let k := fun n => (h n ω : H)
  let er := fun n x => op.L (k n) x - op.f x
  let loss := fun n => (Pn ω n).perdidaPoblacional (k n)
  let err := fun n => ‖(grafo (k n)).val - u.val‖
  have hres (n : ℕ) : ⇑(lap (k n) - f) =ᵐ[volume.restrict V] er n :=
    (Lp.coeFn_sub _ _).trans ((hRep n _ (h n ω).2).sub hf)
  have hPw (n : ℕ) : (Pn ω n).PoblacionIntegrable (k n) := by
    have hh := (hHolder n).2.2.1 _ (h n ω).2
    exact poblacionIntegrable_de_holder_acotado (Pn ω n) (Hm n) V Γ
      dr.acotado db.acotado (soporte_no_vacio D.ley V dr.concentrada)
      (soporte_no_vacio μb Γ db.concentrada) dr.concentrada db.concentrada
      α Sf Sg hα (hHolder n) _ (h n ω).2
      (aestronglyMeasurable_residuo_sq_de_continuidad D.ley V dr.medible dr.concentrada _ _
        (continuo_de_cota_holder V _ _ α hα hh.2.2.1)
        (continuo_de_cota_holder V _ Sf α hα (hHolder n).2.2.2.1))
      (aestronglyMeasurable_residuo_sq_de_continuidad μb Γ db.medible db.concentrada _ _
        (continuo_de_cota_holder Γ _ _ α hα hh.2.2.2)
        (continuo_de_cota_holder Γ _ Sg α hα (hHolder n).2.2.2.2))
  have hBound (n : ℕ) : ∃ M : ℝ, ∀ x ∈ V, |er n x| ≤ M := by
    have hh := (hHolder n).2.2.1 _ (h n ω).2
    exact residuo_acotado_de_cota_holder dr.acotado (soporte_no_vacio D.ley V dr.concentrada)
      _ (op.seminormaL (k n) + Sf) α (add_nonneg hh.1 (hHolder n).1) hα.le
      (holder_resta V _ _ _ _ _ hh.2.2.1 (hHolder n).2.2.2.1)
  have hEρ (n : ℕ) : err n ≤ Kρ * Real.sqrt (loss n) := by
    have hdom : lr * (∫ x, (er n x) ^ 2 ∂D.ley) ≤ loss n := by
      change _ ≤ _ + lb * (∫ x, (op.B (k n) x - op.g x) ^ 2 ∂μb)
      exact le_add_of_nonneg_right (mul_nonneg hlb.le (integral_nonneg fun _ => sq_nonneg _))
    exact estimacion320_de_perdida U volume C hC hP _ _ _ _
      (hDiri n _ (h n ω).2) (hLap n _ (h n ω).2) hsol D _ (hres n) (hPw n).1
      lr _ hlr hdom
  have hEsup (n : ℕ) : err n ≤ Ksup * supResiduo V (er n) :=
    estimacion320_de_supremo U volume C hC hP _ _ _ _
      (hDiri n _ (h n ω).2) (hLap n _ (h n ω).2) hsol _ (hres n) (hBound n)
  have hroot := tasa_raiz_perdida loss mr (α / (d : ℝ)) hLoss
  have hexp : α / (d : ℝ) / 2 = α / (2 * (d : ℝ)) := by ring
  rw [hexp] at hroot
  refine ⟨hLoss, tendsto_iff_norm_sub_tendsto_zero.mpr ?_, ?_, ?_⟩
  · exact squeeze_zero (fun n => norm_nonneg _) hEsup
      (by simpa only [mul_zero] using hLim.const_mul Ksup)
  · exact tasa_de_cota_no_negativa err _ _ Kρ (fun n => norm_nonneg _)
      (Eventually.of_forall fun _ => Real.sqrt_nonneg _) (Eventually.of_forall hEρ) hroot
  · exact tasa_de_cota_no_negativa err _ _ Ksup (fun n => norm_nonneg _)
      (Eventually.of_forall fun n => supResiduo_nonneg_de_acotada (hBound n))
      (Eventually.of_forall hEsup) hSup

/-- Recupera la constante exacta del cuadrado a partir de L3.19 dimensional. -/
theorem lema319_cuadrado_constante_optima
    (e : H01 (volume : Measure Plano) cuadrado)
    (r : Lp ℝ 2 (volume.restrict cuadrado))
    (hΔ : HasDistributionalLaplacian cuadradoOpens volume e r) :
    ‖(e : H1Graph volume cuadrado)‖ ≤
      (Real.sqrt 2 / Real.pi) * Real.sqrt (1 + (Real.sqrt 2 / Real.pi) ^ 2) * ‖r‖ :=
  lema319_constante_dada cuadradoOpens volume (Real.sqrt 2 / Real.pi)
    (div_pos (by positivity) Real.pi_pos) poincare_cuadrado_espectral e r hΔ

set_option maxHeartbeats 1000000 in
/-- Transferencia en un intervalo con los dos extremos deterministas de (3.12). -/
theorem teorema320_unidimensional {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] (a b ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (D : DensidadInferiorEn (volume.restrict (Ioo a b))) [IsProbabilityMeasure D.ley]
    (dm : DatosMasaDimensional D.ley (Ioo a b) 1 1 ε₀)
    (Z : Muestreo38 P D.ley) (op : OperadoresPINN1D H)
    (grafo : H → W12 volume (Ioo a b)) (u : W12 volume (Ioo a b))
    (lap : H → Lp ℝ 2 (volume.restrict (Ioo a b)))
    (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    (hsol : HasDistributionalLaplacianDimensional ⟨Ioo a b, isOpen_Ioo⟩ volume u f)
    (hf : ⇑f =ᵐ[volume.restrict (Ioo a b)] op.f)
    (m : ℕ → ℕ) (hm : ∀ n, 0 < m n) (hg : ∀ᶠ n in atTop, n ≤ m n)
    (lr lb α Sf : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (Hm : ℕ → Set H) (h v : ∀ n, Ω → Hm n)
    (hhMeas : ∀ n, Measurable (fun ω => (h n ω : H)))
    (hvMeas : ∀ n, Measurable (fun ω => (v n ω : H)))
    (hHolder : ∀ n, op.CotasHolder (Hm n) a b α Sf)
    (hDiri : ∀ n, ∀ k ∈ Hm n, (grafo k).val - u.val ∈ H01 volume (Ioo a b))
    (hLap : ∀ n, ∀ k ∈ Hm n,
      HasDistributionalLaplacianDimensional ⟨Ioo a b, isOpen_Ioo⟩ volume (grafo k) (lap k))
    (hRep : ∀ n, ∀ k ∈ Hm n, ⇑(lap k) =ᵐ[volume.restrict (Ioo a b)] op.L k) :
    let w := fun n => peso34Unidimensional (m n) dm.C (radio34Unidimensional dm.c (m n)) lr α
    (∀ᵐ ω ∂P, ∃ R : ℝ, 0 ≤ R ∧ ∀ n,
      let xs := fun i : Fin (m n) => Z.Z i ω
      IsMinOn (op.funcional xs a b lr lb (w n)) (Hm n) (h n ω : H) ∧
      op.perdidaEmpirica xs a b lr lb (v n ω : H) = 0 ∧ op.seminormaL (v n ω : H) ^ 2 ≤ R) →
    ∀ᵐ ω ∂P,
      let e := fun n => (grafo (h n ω : H)).val
      ((fun n => op.perdidaPoblacional D.ley a b lr lb (h n ω : H)) =O[atTop]
        (fun n => (m n : ℝ) ^ (-α))) ∧
      Tendsto e atTop (𝓝 u.val) ∧
      ((fun n => ‖e n - u.val‖) =O[atTop] (fun n => (m n : ℝ) ^ (-(α / 2)))) ∧
      ((fun n => ‖e n - u.val‖) =O[atTop] (fun n => (m n : ℝ) ^ (-(α ^ 2 / (2 * α + 1))))) := by
  intro w hvar
  let U : Opens ℝ := ⟨Ioo a b, isOpen_Ioo⟩
  let : IsFiniteMeasure (volume.restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono subset_closure).trans_lt
      dm.acotado.isCompact_closure.measure_lt_top).ne
  obtain ⟨C, hC, hP⟩ := exists_poincare_constant (μ := volume) dm.acotado
  let Kρ := C * Real.sqrt (1 + C ^ 2) / Real.sqrt (D.rho0 * lr)
  let Ksup := C * Real.sqrt (1 + C ^ 2) * Real.sqrt (volume.real (Ioo a b))
  have h38 := teorema38_unidimensional P D.ley a b ε₀ hε₀ dm Z op
    m hm hg lr lb α Sf hlr hlb hα Hm h v hhMeas hvMeas hHolder hvar
  filter_upwards [h38] with ω hω
  obtain ⟨hLoss, ⟨hLim, hSup⟩, _, _⟩ := hω
  let k := fun n => (h n ω : H)
  let er := fun n x => op.L (k n) x - op.f x
  let loss := fun n => op.perdidaPoblacional D.ley a b lr lb (k n)
  let err := fun n => ‖(grafo (k n)).val - u.val‖
  have hne := soporte_no_vacio D.ley (Ioo a b) dm.concentrada
  have hres (n : ℕ) : ⇑(lap (k n) - f) =ᵐ[volume.restrict (Ioo a b)] er n :=
    (Lp.coeFn_sub _ _).trans ((hRep n _ (h n ω).2).sub hf)
  have hBound (n : ℕ) : ∃ B : ℝ, ∀ x ∈ Ioo a b, |er n x| ≤ B := by
    obtain ⟨hSf, hF, hCandidates⟩ := hHolder n
    obtain ⟨hL, hHL⟩ := hCandidates _ (h n ω).2
    exact residuo_acotado_de_cota_holder dm.acotado hne _ _ α (add_nonneg hL hSf) hα.le
      (holder_resta (Ioo a b) _ _ _ _ _ hHL hF)
  have hEρ (n : ℕ) : err n ≤ Kρ * Real.sqrt (loss n) := by
    have hi := op.residuoInterior_integrable D.ley a b α Sf dm.concentrada hα
      (Hm n) (hHolder n) _ (h n ω).2
    have hdom : lr * (∫ x, (er n x) ^ 2 ∂D.ley) ≤ loss n :=
      le_add_of_nonneg_right (op.perdidaFrontera_nonneg hlb.le (k n))
    exact estimacion320_de_perdida U volume C hC hP _ _ _ _
      (hDiri n _ (h n ω).2) (hLap n _ (h n ω).2) hsol D _ (hres n) hi lr _ hlr hdom
  have hEsup (n : ℕ) : err n ≤ Ksup * supResiduo (Ioo a b) (er n) :=
    estimacion320_de_supremo U volume C hC hP _ _ _ _
      (hDiri n _ (h n ω).2) (hLap n _ (h n ω).2) hsol _ (hres n) (hBound n)
  refine ⟨hLoss, tendsto_iff_norm_sub_tendsto_zero.mpr ?_, ?_, ?_⟩
  · exact squeeze_zero (fun n => norm_nonneg _) hEsup
      (by simpa only [mul_zero] using hLim.const_mul Ksup)
  · exact tasa_de_cota_no_negativa err _ _ Kρ (fun n => norm_nonneg _)
      (Eventually.of_forall fun _ => Real.sqrt_nonneg _) (Eventually.of_forall hEρ)
      (tasa_raiz_perdida loss m α hLoss)
  · exact tasa_de_cota_no_negativa err _ _ Ksup (fun n => norm_nonneg _)
      (Eventually.of_forall fun n => supResiduo_nonneg_de_acotada (hBound n))
      (Eventually.of_forall hEsup) hSup

#check teorema320_dimension_ge_dos
#check teorema320_unidimensional
#print axioms lema319_cuadrado_constante_optima
#print axioms teorema320_unidimensional
#print axioms estimacion320_de_perdida
#print axioms estimacion320_de_supremo
#print axioms teorema320_dimension_ge_dos


end TesisPINN
