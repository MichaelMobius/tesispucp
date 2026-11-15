import TesisPINN.HermiteCoeficientesBorel
import TesisPINN.HermiteRegularidadTensorial
import TesisPINN.ProblemaInterior

/-! Interpolación y regularidad de la Proposición 3.25 en la arquitectura común. -/

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

/-- La arquitectura común se fija antes de observar las muestras. Sus pesos de
salida son borelianos y sus comparadores satisfacen interpolación y regularidad
uniformes en el cuadrado cerrado. -/
theorem proposicion325_arquitectura_comun :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, 1 ≤ m →
      let D := 4 * m - 1
      ∃ red : CapasCuadraticas Bool (IndiceMonomio D × Bool),
        Measurable (fun s : Fin m → Plano => pesoSalida324 (coeficientesHermite325 s)) ∧
        ∀ s : Fin m → Plano, (∀ i, s i ∈ closure cuadrado) →
          let h : Plano → ℝ := fun x =>
            red.salida (pesoSalida324 (coeficientesHermite325 s)) (fun b => if b then x 0 else x 1)
          h = comparador325 s ∧
          (∀ eje : Bool, (polinomioFormal324 (coeficientesHermite325 s)).degreeOf eje ≤ D) ∧
          (∀ x ∈ frontier cuadrado, h x = 0) ∧
          (∀ i, laplacianoClásico h (s i) = fuenteManufacturada (s i)) ∧
          perdidaEmpiricaInterior s (laplacianoClásico h) fuenteManufacturada = 0 ∧
          (∀ (a b : ℕ), a + b ≤ 3 → ∀ x ∈ closure cuadrado,
            ‖iteratedDeriv a (fun u => iteratedDeriv b (fun v =>
              h (WithLp.toLp 2 ![u, v])) (x 1)) (x 0)‖ ≤ K) ∧
          EsHolderInterior (closure cuadrado) (1 / 2) (laplacianoClásico h) ∧
          seminormaInterior (closure cuadrado) (1 / 2) (laplacianoClásico h) ≤ K := by
  obtain ⟨M, hM, hC3⟩ := comparador325_c3_uniforme
  obtain ⟨H, _, hHol⟩ := laplaciano_comparador325_holder_uniforme
  refine ⟨max M H, hM.trans (le_max_left _ _), fun m hm => ?_⟩
  obtain ⟨red, hexact⟩ := proposicion325_interpolacion_exacta m hm
  refine ⟨red, pesosSalidaHermite325_borel m, fun s hs => ?_⟩
  obtain ⟨he, hfront, hjet, hloss⟩ := hexact s
  obtain ⟨hholder, hbound⟩ := hHol s hs
  refine ⟨he, polinomioHermite325_grado_parcial s, hfront, hjet, hloss, ?_, ?_, ?_⟩
  · rw [he]
    exact fun a b hk x hx => ((hC3 s hs a b hk x hx).2).trans (le_max_left _ _)
  · rw [he]
    exact hholder
  · rw [he]
    exact hbound.trans (le_max_right _ _)

#check proposicion325_arquitectura_comun
#print axioms proposicion325_arquitectura_comun


#check proposicion325_interpolacion_exacta
#print axioms proposicion325_interpolacion_exacta

end TesisPINN
