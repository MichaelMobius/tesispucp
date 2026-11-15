import TesisPINN.Teorema34Dimensional

/-! Rama unidimensional de T3.4, con ambos extremos observados. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Set Filter Asymptotics

/-- El dato de frontera se evalúa en los extremos fijos. Solo el operador
interior contribuye al regularizador. -/
structure OperadoresPINN1D (H : Type*) where
  L : H → ℝ → ℝ
  f : ℝ → ℝ
  B : H → ℝ → ℝ
  g : ℝ → ℝ
  seminormaL : H → ℝ

namespace OperadoresPINN1D

variable {H : Type*} (op : OperadoresPINN1D H)

def residuoFrontera (h : H) (x : ℝ) : ℝ := op.B h x - op.g x

def perdidaFrontera (a b lb : ℝ) (h : H) : ℝ :=
  lb / 2 * (op.residuoFrontera h a ^ 2 + op.residuoFrontera h b ^ 2)

def perdidaEmpiricaInterior {m : ℕ} (xs : Fin m → ℝ) (lr : ℝ) (h : H) : ℝ :=
  lr / (m : ℝ) * ∑ i, (op.L h (xs i) - op.f (xs i)) ^ 2

def perdidaEmpirica {m : ℕ} (xs : Fin m → ℝ) (a b lr lb : ℝ) (h : H) : ℝ :=
  op.perdidaEmpiricaInterior xs lr h + op.perdidaFrontera a b lb h

def perdidaPoblacional (μ : Measure ℝ) (a b lr lb : ℝ) (h : H) : ℝ :=
  lr * (∫ x, (op.L h x - op.f x) ^ 2 ∂μ) + op.perdidaFrontera a b lb h

def funcional {m : ℕ} (xs : Fin m → ℝ) (a b lr lb peso : ℝ) (h : H) : ℝ :=
  op.perdidaEmpirica xs a b lr lb h + peso * op.seminormaL h ^ 2

def CotasHolder (Hm : Set H) (a b α Sf : ℝ) : Prop :=
  0 ≤ Sf ∧
  (∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, |op.f x - op.f y| ≤ Sf * dist x y ^ α) ∧
  ∀ h ∈ Hm, 0 ≤ op.seminormaL h ∧
    ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, |op.L h x - op.L h y| ≤ op.seminormaL h * dist x y ^ α

theorem perdidaFrontera_nonneg {a b lb : ℝ} (hlb : 0 ≤ lb) (h : H) :
    0 ≤ op.perdidaFrontera a b lb h := by unfold perdidaFrontera; positivity

theorem perdidaEmpiricaInterior_nonneg {m : ℕ} (xs : Fin m → ℝ) {lr : ℝ}
    (hlr : 0 ≤ lr) (h : H) : 0 ≤ op.perdidaEmpiricaInterior xs lr h := by
  unfold perdidaEmpiricaInterior
  exact mul_nonneg (div_nonneg hlr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem residuoInterior_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b α Sf : ℝ)
    (hμ : μ (Ioo a b)ᶜ = 0) (hα : 0 < α) (Hm : Set H) (hC : op.CotasHolder Hm a b α Sf)
    (h : H) (hh : h ∈ Hm) : Integrable (fun x => (op.L h x - op.f x) ^ 2) μ := by
  obtain ⟨hf₀, hf, hc⟩ := hC
  obtain ⟨hL₀, hL⟩ := hc h hh
  exact integrable_sq_of_holder_on_bounded μ (Ioo a b) (Metric.isBounded_Ioo a b)
    (soporte_no_vacio μ (Ioo a b) hμ) hμ (fun x => op.L h x - op.f x) _ α
    (add_nonneg hL₀ hf₀) hα
    (aestronglyMeasurable_residuo_sq_de_continuidad μ (Ioo a b) measurableSet_Ioo hμ _ _
      (continuo_de_cota_holder _ _ _ _ hα hL) (continuo_de_cota_holder _ _ _ _ hα hf))
    (holder_resta (Ioo a b) (op.L h) op.f _ _ α hL hf)

end OperadoresPINN1D

def radio34Unidimensional (c : ℝ) (m : ℕ) : ℝ := radioRaizDimensional 1 c 1 m

def factor34Unidimensional (m : ℕ) (C r : ℝ) : ℝ := max 1 (3 * C * (m : ℝ) * r)

def peso34Unidimensional (m : ℕ) (C r lr α : ℝ) : ℝ :=
  pesoCobertura lr r α (factor34Unidimensional m C r)

theorem factor34Unidimensional_pos (m : ℕ) (C r : ℝ) :
    0 < factor34Unidimensional m C r := zero_lt_one.trans_le (le_max_left _ _)

theorem radio34Unidimensional_eq (c : ℝ) (m : ℕ) (hc : 0 < c) (hm : 0 < m) :
    radio34Unidimensional c m = c⁻¹ * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [radio34Unidimensional, radioRaizDimensional_eq _ _ _ _ hc (by norm_num) hm]
  norm_num [Real.rpow_neg hc.le]

theorem radio34Unidimensional_potencia (c α : ℝ) (m : ℕ) (hc : 0 < c) (hm : 0 < m) :
    radio34Unidimensional c m ^ (2 * α) = c ^ (-(2 * α)) * (m : ℝ) ^ (-α) := by
  rw [radio34Unidimensional, radioRaizDimensional_potencia _ _ _ _ _ zero_le_one hc (by norm_num) hm]
  simp only [div_one, one_mul, ← Real.rpow_mul hc.le]
  congr 2 <;> ring

theorem factor34Unidimensional_eq (m : ℕ) (C c : ℝ) (hc : 0 < c) (hm : 0 < m) :
    factor34Unidimensional m C (radio34Unidimensional c m) =
      max 1 (3 * (C / c) * Real.sqrt (m : ℝ)) := by
  have hpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hroot := Real.sqrt_pos.2 hpos
  rw [factor34Unidimensional, radio34Unidimensional_eq _ _ hc hm, Real.rpow_neg hpos.le,
    ← Real.sqrt_eq_rpow]
  congr 1
  field_simp
  rw [Real.sq_sqrt hpos.le]

theorem factor34Unidimensional_isBigO (C c : ℝ) (hc : 0 < c) :
    (fun m : ℕ => factor34Unidimensional m C (radio34Unidimensional c m)) =O[atTop]
      (fun m : ℕ => Real.sqrt (m : ℝ)) := by
  apply isBigO_de_cota_eventual _ _ (max 1 (3 * (C / c)))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  rw [factor34Unidimensional_eq _ _ _ hc hm]
  have h1 : 1 ≤ Real.sqrt (m : ℝ) := by
    have h : (1 : ℝ) ≤ m := by exact_mod_cast hm
    simpa using Real.sqrt_le_sqrt h
  refine ⟨zero_le_one.trans (le_max_left _ _), Real.sqrt_nonneg _, max_le ?_ ?_⟩
  · exact h1.trans (le_mul_of_one_le_left (Real.sqrt_nonneg _) (le_max_left _ _))
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)

theorem factor_peso34Unidimensional (m : ℕ) (C r lr α : ℝ) :
    factor34Unidimensional m C r * peso34Unidimensional m C r lr α = 3 * lr * r ^ (2 * α) := by
  rw [peso34Unidimensional, pesoCobertura,
    mul_div_cancel₀ _ (factor34Unidimensional_pos m C r).ne']

theorem peso34Unidimensional_pos (m : ℕ) (C r lr α : ℝ) (hr : 0 < r) (hlr : 0 < lr) :
    0 < peso34Unidimensional m C r lr α := by
  unfold peso34Unidimensional pesoCobertura
  exact div_pos (by positivity) (factor34Unidimensional_pos m C r)

theorem cota34_unidimensional_bajo_cobertura {H : Type*}
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b ε₀ : ℝ)
    (dm : DatosMasaDimensional μ (Ioo a b) 1 1 ε₀)
    (op : OperadoresPINN1D H) (Hm : Set H)
    (m : ℕ) (hm : 0 < m) (xs : Fin m → ℝ)
    (lr lb α Sf : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (hsmall : radio34Unidimensional dm.c m ≤ ε₀)
    (hHolder : op.CotasHolder Hm a b α Sf) (hs : ∀ i, xs i ∈ Ioo a b)
    (hcov : MuestrasCubren (Ioo a b) xs (radio34Unidimensional dm.c m))
    (h : H) (hh : h ∈ Hm) :
    let r := radio34Unidimensional dm.c m
    let F := factor34Unidimensional m dm.C r
    let w := peso34Unidimensional m dm.C r lr α
    op.perdidaPoblacional μ a b lr lb h ≤ F * op.funcional xs a b lr lb w h +
      3 * lr * dm.c ^ (-(2 * α)) * Sf ^ 2 * (m : ℝ) ^ (-α) := by
  intro r F w
  have hr : 0 < r := radioRaizDimensional_pos _ _ _ _ zero_lt_one dm.c_pos hm
  have hInt := op.residuoInterior_integrable μ a b α Sf dm.concentrada hα Hm hHolder h hh
  obtain ⟨hS, hf, hreg⟩ := hHolder
  obtain ⟨hL, hHol⟩ := hreg h hh
  have hI := integral_residuo_le_cobertura μ (Ioo a b) measurableSet_Ioo measure_univ
    dm.concentrada (op.L h) op.f xs hm α r ε₀ (op.seminormaL h) Sf dm.C 1
    hα hr hsmall hL hS dm.C_pos.le hs hcov dm.superior hHol hf hInt
  rw [Real.rpow_one, cuadrado_holder _ _ _ hr.le, cuadrado_holder _ _ _ hr.le] at hI
  have hM : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  have hnorm :
      (3 * dm.C * (m : ℝ) * r) * op.perdidaEmpiricaInterior xs lr h =
        lr * (3 * dm.C * r * ∑ i, (op.L h (xs i) - op.f (xs i)) ^ 2) := by
    unfold OperadoresPINN1D.perdidaEmpiricaInterior
    field_simp
  have he := mul_le_mul_of_nonneg_right (le_max_right 1 (3 * dm.C * (m : ℝ) * r))
    (op.perdidaEmpiricaInterior_nonneg xs hlr.le h)
  rw [hnorm] at he
  have hb := mul_le_mul_of_nonneg_right (le_max_left 1 (3 * dm.C * (m : ℝ) * r))
    (op.perdidaFrontera_nonneg (a := a) (b := b) hlb.le h)
  have hw : F * w = 3 * lr * r ^ (2 * α) := factor_peso34Unidimensional _ _ _ _ _
  have hp : r ^ (2 * α) = dm.c ^ (-(2 * α)) * (m : ℝ) ^ (-α) :=
    radio34Unidimensional_potencia _ _ _ dm.c_pos hm
  have hI' := mul_le_mul_of_nonneg_left hI hlr.le
  change _ ≤ F * op.perdidaEmpiricaInterior xs lr h at he
  change _ ≤ F * op.perdidaFrontera a b lb h at hb
  have hbound : op.perdidaPoblacional μ a b lr lb h ≤
      F * op.funcional xs a b lr lb w h + 3 * lr * r ^ (2 * α) * Sf ^ 2 := by
    unfold OperadoresPINN1D.perdidaPoblacional OperadoresPINN1D.funcional OperadoresPINN1D.perdidaEmpirica
    rw [mul_add, ← mul_assoc F w, hw]
    linarith only [hI', he, hb]
  exact hbound.trans (by rw [hp]; linarith)

/-- (3.12), con un solo evento aleatorio y los dos extremos deterministas. -/
theorem teorema34_unidimensional {Ω H : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b ε₀ : ℝ) (hab : a < b) (dm : DatosMasaDimensional μ (Ioo a b) 1 1 ε₀)
    (Z : Muestreo38 P μ) (op : OperadoresPINN1D H) (Hm : Set H)
    (m : ℕ) (hm : 0 < m) (lr lb α Sf : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (hsmall : radio34Unidimensional dm.c m ≤ ε₀) (hHolder : op.CotasHolder Hm a b α Sf) :
    let r := radio34Unidimensional dm.c m
    let F := factor34Unidimensional m dm.C r
    let w := peso34Unidimensional m dm.C r lr α
    frontier (Ioo a b) = {a, b} ∧
    ∃ A : Set Ω, MeasurableSet A ∧ 1 - falloRaiz34 m ≤ P.real A ∧
      ∀ ω ∈ A, let xs := fun i : Fin m => Z.Z i ω
        (∀ i, xs i ∈ Ioo a b) ∧ MuestrasCubren (Ioo a b) xs r ∧
        ∀ h ∈ Hm, op.perdidaPoblacional μ a b lr lb h ≤ F * op.funcional xs a b lr lb w h +
          3 * lr * dm.c ^ (-(2 * α)) * Sf ^ 2 * (m : ℝ) ^ (-α) := by
  intro r F w
  refine ⟨frontier_Ioo hab, ?_⟩
  obtain ⟨A, hA, hf, hcov⟩ := evento_raiz_dimensional P μ Z (Ioo a b) 1 1 ε₀ dm
    le_rfl (by norm_num) m hm hsmall
  let S := muestrasEnSoporte Z.Z m (Ioo a b)
  have hS : MeasurableSet S := muestrasEnSoporte_measurable Z.Z m (Ioo a b) dm.medible Z.medible
  have hnull : P.real Sᶜ = 0 := medidaReal_fallo_soporte P μ Z.Z m (Ioo a b) dm.concentrada Z.medible Z.ley
  have hmeas := hA.inter hS
  have hle : P.real (A ∩ S)ᶜ ≤ falloRaiz34 m := by
    rw [compl_inter]
    exact (measureReal_union_le _ _).trans (by rw [hnull, add_zero]; exact hf)
  rw [probReal_compl_eq_one_sub hmeas] at hle
  refine ⟨A ∩ S, hmeas, by linarith, ?_⟩
  rintro ω ⟨hω, hs⟩
  refine ⟨hs, hcov ω hω, fun h hh => ?_⟩
  exact cota34_unidimensional_bajo_cobertura μ a b ε₀ dm op Hm m hm _ lr lb α Sf
    hlr hlb hα hsmall hHolder hs (hcov ω hω) h hh

#check teorema34_unidimensional
#print axioms radio34Unidimensional_eq
#print axioms factor_peso34Unidimensional
#print axioms factor34Unidimensional_isBigO
#print axioms cota34_unidimensional_bajo_cobertura
#print axioms teorema34_unidimensional

end TesisPINN
