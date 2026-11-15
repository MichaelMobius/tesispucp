import TesisPINN.SeleccionBorel326

/-! Corolario 3.26 para la clase polinómica con Dirichlet fuerte. -/

noncomputable section

namespace TesisPINN

open Set

theorem funcional326_eq_infimo {D m : ℕ} (s : Fin m → Plano) (peso : ℝ)
    (a : Coeficientes324 D) (ha : IsMinOn (funcional326 s peso) univ a) :
    funcional326 s peso a = sInf (range (funcional326 (D := D) s peso)) := by
  symm
  exact (show IsLeast (range (funcional326 (D := D) s peso)) (funcional326 s peso a) from
    ⟨mem_range_self a, by rintro _ ⟨b, rfl⟩; exact ha (mem_univ b)⟩).csInf_eq

/-- Para cada peso positivo fijo y cada tamaño positivo, se eligen de manera
boreliana los pesos de salida de una red minimizadora. Las cotas de (3.91)
valen para cualquier minimizador y usan una constante uniforme. -/
theorem corolario326 :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ m : ℕ, ∀ hm : 1 ≤ m, ∀ peso > (0 : ℝ),
      let D := 4 * m - 1
      ∃ a : (Fin m → Plano) → Coeficientes324 D,
        Measurable a ∧ Measurable (fun s => pesoSalida324 (a s)) ∧
        ∀ s : Fin m → Plano, (∀ i, s i ∈ cuadrado) →
          (IsMinOn (fun h : Plano → ℝ => funcionalInterior cuadrado (1 / 2) s
            (laplacianoClásico h) fuenteManufacturada peso)
            (range (candidato326 D))
            (fun x => (red324 (show 2 ≤ D by dsimp [D]; omega)).salida
              (pesoSalida324 (a s)) (fun b => if b then x 0 else x 1))) ∧
          (∀ b : Coeficientes324 D, IsMinOn (funcional326 s peso) univ b →
            funcional326 s peso b ≤ peso * R ∧
            perdidaEmpiricaInterior s (laplaciano326 D b) fuenteManufacturada ≤ peso * R ∧
            seminorma326 D b ^ 2 ≤ R) := by
  obtain ⟨R, hR, hbounds⟩ := cotas_minimizador326
  refine ⟨R, hR, fun m hm peso hp => ?_⟩
  obtain ⟨a, hmeas, hmin⟩ := existe_minimizador_borel326 (4 * m - 1) m peso hp
  refine ⟨a, hmeas, (pesosSalida324_continuos (4 * m - 1)).measurable.comp hmeas,
    fun s hs => ⟨?_, hbounds hm s hs peso hp⟩⟩
  simp_rw [red324_salida]
  exact (minimo326_equiv_clase s peso (a s)).mp (hmin s)

#check corolario326
#print axioms funcional326_eq_infimo
#print axioms corolario326

end TesisPINN

