import TesisPINN.CoercividadCoeficientes326

/-! Existencia y cotas para el funcional normativo de C3.26. -/

noncomputable section

namespace TesisPINN

open Set

theorem funcional326_coercivo {D m : ℕ} (s : Fin m → Plano) (peso : ℝ) (hp : 0 < peso) :
    ∃ c > (0 : ℝ), ∀ a : Coeficientes324 D, c * ‖a‖ ^ 2 ≤ funcional326 s peso a := by
  obtain ⟨c, hc, hdom⟩ := seminorma326_domina_norma D
  refine ⟨peso * c ^ 2, by positivity, fun a => ?_⟩
  have hsq := pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg a)) (hdom a) 2
  have he := perdidaEmpiricaInterior_nonneg s (laplaciano326 D a) fuenteManufacturada
  change _ ≤ perdidaEmpiricaInterior s _ _ + peso * seminorma326 D a ^ 2
  calc
    _ = peso * (c * ‖a‖) ^ 2 := by ring
    _ ≤ peso * seminorma326 D a ^ 2 := mul_le_mul_of_nonneg_left hsq hp.le
    _ ≤ _ := le_add_of_nonneg_left he

theorem subnivel326_compacto {D m : ℕ} (s : Fin m → Plano) (peso : ℝ)
    (hp : 0 < peso) (t : ℝ) :
    IsCompact {a : Coeficientes324 D | funcional326 s peso a ≤ t} := by
  obtain ⟨c, hc, hcoerc⟩ := funcional326_coercivo (D := D) s peso hp
  refine (isCompact_closedBall (0 : Coeficientes324 D) (Real.sqrt (t / c))).of_isClosed_subset
    (isClosed_le (funcional326_continuo s peso) continuous_const) ?_
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  have ha' : c * ‖a‖ ^ 2 ≤ t := (hcoerc a).trans ha
  have hquot := (le_div_iff₀ hc).2 (by simpa [mul_comm] using ha')
  exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg ‖a‖).trans hquot)).2 hquot

theorem existe_minimizador326 {D m : ℕ} (s : Fin m → Plano) (peso : ℝ) (hp : 0 < peso) :
    ∃ a : Coeficientes324 D, IsMinOn (funcional326 s peso) univ a := by
  let F : Coeficientes324 D → ℝ := funcional326 s peso
  let K := {a | F a ≤ F 0}
  obtain ⟨a, ha, hmin⟩ := (subnivel326_compacto s peso hp (F 0)).exists_isMinOn
    (show K.Nonempty from ⟨0, by change F 0 ≤ F 0; exact le_rfl⟩) (funcional326_continuo s peso).continuousOn
  refine ⟨a, fun b _ => ?_⟩
  by_cases hb : b ∈ K
  · exact hmin hb
  · exact (show F a ≤ F 0 from ha).trans
      (le_of_lt (lt_of_not_ge (show ¬ F b ≤ F 0 from hb)))

theorem minimo326_equiv_clase {D m : ℕ} (s : Fin m → Plano) (peso : ℝ)
    (a : Coeficientes324 D) :
    IsMinOn (funcional326 s peso) univ a ↔
      IsMinOn (fun h : Plano → ℝ => funcionalInterior cuadrado (1 / 2) s
        (laplacianoClásico h) fuenteManufacturada peso)
        (range (candidato326 D)) (candidato326 D a) := by
  constructor
  · rintro h b ⟨c, rfl⟩
    exact h (mem_univ c)
  · intro h b _
    exact h (mem_range_self b)

theorem existe_red_minimizadora326 {m : ℕ} (hm : 1 ≤ m) (s : Fin m → Plano)
    (peso : ℝ) (hp : 0 < peso) :
    ∃ a : Coeficientes324 (4 * m - 1),
      IsMinOn (fun h : Plano → ℝ => funcionalInterior cuadrado (1 / 2) s
        (laplacianoClásico h) fuenteManufacturada peso)
        (range (candidato326 (4 * m - 1)))
        (fun x => (red324 (show 2 ≤ 4 * m - 1 by omega)).salida
          (pesoSalida324 a) (fun b => if b then x 0 else x 1)) := by
  obtain ⟨a, ha⟩ := existe_minimizador326 (D := 4 * m - 1) s peso hp
  refine ⟨a, ?_⟩
  simp_rw [red324_salida]
  exact (minimo326_equiv_clase s peso a).mp ha

/-- Las tres cotas de (3.91), con una constante independiente de muestra, peso y tamaño. -/
theorem cotas_minimizador326 :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ {m : ℕ}, 1 ≤ m → ∀ s : Fin m → Plano,
      (∀ i, s i ∈ cuadrado) → ∀ peso > (0 : ℝ), ∀ a : Coeficientes324 (4 * m - 1),
      IsMinOn (funcional326 s peso) univ a →
      funcional326 s peso a ≤ peso * R ∧
      perdidaEmpiricaInterior s (laplaciano326 (4 * m - 1) a) fuenteManufacturada ≤ peso * R ∧
      seminorma326 (4 * m - 1) a ^ 2 ≤ R := by
  obtain ⟨K, hK, hHol⟩ := laplaciano_comparador325_holder_uniforme
  refine ⟨K ^ 2, sq_nonneg _, ?_⟩
  intro m hm s hs peso hp a hmin
  let b := coeficientesHermite325 s
  have he : candidato326 (4 * m - 1) b = comparador325 s := by
    funext x
    rw [candidato326_eq, polinomioPlano326, polinomioHermite325_tensor hm]
    rfl
  have hLap : laplaciano326 (4 * m - 1) b = laplacianoClásico (comparador325 s) := by
    change laplacianoClásico (candidato326 _ b) = _
    rw [he]
  have hzero := comparador325_perdida_empirica_cero s
  rw [← hLap] at hzero
  obtain ⟨hH, hbound⟩ := hHol s (fun i => subset_closure (hs i))
  have hS : seminorma326 (4 * m - 1) b ≤ K := by
    apply csInf_le ⟨0, fun _ h => h.1⟩
    refine ⟨hK, fun x hx y hy => ?_⟩
    rw [hLap]
    exact (seminormaInterior_cota _ _ _ hH (by norm_num) x (subset_closure hx) y
      (subset_closure hy)).trans (mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg dist_nonneg _))
  have hJ : funcional326 s peso a ≤ peso * K ^ 2 := calc
    _ ≤ funcional326 s peso b := hmin (mem_univ b)
    _ = peso * seminorma326 (4 * m - 1) b ^ 2 := by
      change perdidaEmpiricaInterior s _ _ + _ = _
      rw [hzero, zero_add] <;> rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (apply_nonneg _ _) hS 2) hp.le
  have hE := perdidaEmpiricaInterior_nonneg s (laplaciano326 (4 * m - 1) a)
    fuenteManufacturada
  exact ⟨hJ, (le_add_of_nonneg_right (mul_nonneg hp.le (sq_nonneg _))).trans hJ,
    regularidad_controlada peso _ _ _ hp hE hJ⟩

#check existe_red_minimizadora326
#print axioms funcional326_coercivo
#print axioms subnivel326_compacto
#print axioms existe_minimizador326
#print axioms minimo326_equiv_clase
#print axioms existe_red_minimizadora326
#print axioms cotas_minimizador326

end TesisPINN

