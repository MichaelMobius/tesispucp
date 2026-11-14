import TesisPINN.HermiteSeleccionBorel
import TesisPINN.ProblemaInterior

/-! Parte de interpolación exacta de la Proposición 3.25. -/

noncomputable section

namespace TesisPINN

theorem comparador325_perdida_empirica_cero {m : ℕ} (s : Fin m → Plano) :
    perdidaEmpiricaInterior s (laplacianoClásico (comparador325 s)) fuenteManufacturada = 0 := by
  simp [perdidaEmpiricaInterior, comparador325_laplaciano_nodo]

/-- La misma red sirve para todas las muestras de tamaño `m`. La parte
empírica del funcional se anula por la interpolación de los jets. -/
theorem proposicion325_interpolacion_exacta (m : ℕ) (hm : 1 ≤ m) :
    let D := 4 * m - 1
    ∃ red : CapasCuadraticas Bool (IndiceMonomio D × Bool),
      ∀ s : Fin m → Plano,
        let h : Plano → ℝ := fun x =>
          red.salida (pesoSalida324 (coeficientesHermite325 s)) (fun b => if b then x 0 else x 1)
        h = comparador325 s ∧
        (∀ x ∈ frontier cuadrado, h x = 0) ∧
        (∀ i, laplacianoClásico h (s i) = fuenteManufacturada (s i)) ∧
        perdidaEmpiricaInterior s (laplacianoClásico h) fuenteManufacturada = 0 := by
  dsimp only
  have hD : 2 ≤ 4 * m - 1 := by omega
  refine ⟨red324 hD, fun s => ?_⟩
  let h : Plano → ℝ := fun x =>
    (red324 hD).salida (pesoSalida324 (coeficientesHermite325 s))
      (fun b => if b then x 0 else x 1)
  have he : h = comparador325 s := funext (fun x => comparador325_realizacion hm s x hD)
  change h = comparador325 s ∧ (∀ x ∈ frontier cuadrado, h x = 0) ∧
    (∀ i, laplacianoClásico h (s i) = fuenteManufacturada (s i)) ∧
    perdidaEmpiricaInterior s (laplacianoClásico h) fuenteManufacturada = 0
  simpa only [he] using
    (show comparador325 s = comparador325 s ∧
      (∀ x ∈ frontier cuadrado, comparador325 s x = 0) ∧
      (∀ i, laplacianoClásico (comparador325 s) (s i) = fuenteManufacturada (s i)) ∧
      perdidaEmpiricaInterior s (laplacianoClásico (comparador325 s)) fuenteManufacturada = 0 from
      ⟨rfl, comparador325_dirichlet s, comparador325_laplaciano_nodo s,
        comparador325_perdida_empirica_cero s⟩)

#check proposicion325_interpolacion_exacta
#print axioms proposicion325_interpolacion_exacta

end TesisPINN
