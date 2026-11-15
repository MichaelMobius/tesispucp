import TesisPINN.HermiteSeleccionBorel
import Mathlib.Topology.Instances.Matrix

/-! Coordenadas de la interpolación mediante la matriz confluente de los jets. -/

noncomputable section

namespace TesisPINN

open Polynomial Matrix Set
open scoped Polynomial

private def indiceJetHermite (n : ℕ) : Fin n × Fin 4 ≃ Fin (4 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 4))

private def matrizHermite325 {n : ℕ} (t : Fin n → ℝ) : Matrix (Fin (4 * n)) (Fin (4 * n)) ℝ :=
  Matrix.of fun i j => jetHermite (t ((indiceJetHermite n).symm i).1)
    ((indiceJetHermite n).symm i).2 ((degreeLT.basis ℝ (4 * n) j : PolinomiosHermite n) : ℝ[X])

private theorem matrizHermite325_mulVec {n : ℕ} (t : Fin n → ℝ) (p : PolinomiosHermite n) :
    matrizHermite325 t *ᵥ (fun j : Fin (4 * n) => (p : ℝ[X]).coeff j) =
      fun i => mapaJetsHermite t p ((indiceJetHermite n).symm i) := by
  have he := LinearMap.toMatrix_mulVec_repr (degreeLT.basis ℝ (4 * n))
    (Pi.basisFun ℝ (Fin n × Fin 4)) (mapaJetsHermite t) p
  have hj (p : PolinomiosHermite n) (i : Fin n × Fin 4) :
      mapaJetsHermite t p i = jetHermite (t i.1) i.2 (p : ℝ[X]) := by cases i; rfl
  funext i
  simpa only [matrizHermite325, Matrix.mulVec, dotProduct, Matrix.of_apply,
    LinearMap.toMatrix_apply, degreeLT.basis_repr, Pi.basisFun_repr, hj] using
    congrFun he ((indiceJetHermite n).symm i)

private theorem matrizHermite325_det {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t) :
    IsUnit (matrizHermite325 t).det := by
  have hmat : IsUnit (matrizHermite325 t) := Matrix.mulVec_injective_iff_isUnit.mp (by
    intro v w h
    let e := degreeLTEquiv ℝ (4 * n)
    let p := e.symm v
    let q := e.symm w
    have hv : (fun j : Fin (4 * n) => (p : ℝ[X]).coeff j) = v := e.apply_symm_apply v
    have hw : (fun j : Fin (4 * n) => (q : ℝ[X]).coeff j) = w := e.apply_symm_apply w
    rw [← hv, ← hw, matrizHermite325_mulVec, matrizHermite325_mulVec] at h
    apply e.symm.injective
    apply mapaJetsHermite_inyectivo t ht
    funext i
    simpa using congrFun h (indiceJetHermite n i))
  exact (Matrix.isUnit_iff_isUnit_det _).mp hmat

private def vectorDatosHermite325 {n : ℕ} (t : Fin n → ℝ) (i : Fin (4 * n)) : ℝ :=
  let j := (indiceJetHermite n).symm i
  datosManufacturados (t j.1) j.2

private theorem vectorCoefHermite325_eq {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t) :
    let p := interpolanteHermite t ht (fun j => datosManufacturados (t j.1) j.2)
    (fun j : Fin (4 * n) => (p : ℝ[X]).coeff j) =
      (matrizHermite325 t)⁻¹ *ᵥ vectorDatosHermite325 t := by
  dsimp only
  let p := interpolanteHermite t ht (fun j => datosManufacturados (t j.1) j.2)
  have he : matrizHermite325 t *ᵥ (fun j : Fin (4 * n) => (p : ℝ[X]).coeff j) =
      vectorDatosHermite325 t := by
    rw [matrizHermite325_mulVec]
    funext j
    exact interpolanteHermite_jet _ _ _ _ _
  rw [← he, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (matrizHermite325_det t ht),
    Matrix.one_mulVec]

private theorem matrizHermite325_continua (n : ℕ) :
    Continuous (matrizHermite325 (n := n)) := by
  apply continuous_matrix
  intro i j
  simp only [matrizHermite325, Matrix.of_apply, jetHermite_eval, degreeLT.basis_val]
  exact (eval_polynomial_contDiff _ 0).continuous.comp (continuous_apply _)

private theorem vectorDatosHermite325_continuo (n : ℕ) :
    Continuous (vectorDatosHermite325 (n := n)) := by
  apply continuous_pi
  intro i
  exact ((aManufacturada_suave ⊤).continuous_iteratedDeriv _ (by simp)).comp (continuous_apply _)

private theorem coefHermite325_continuo {X : Type*} [TopologicalSpace X] {n : ℕ}
    (t : X → Fin n → ℝ) (ht : Continuous t) (hi : ∀ x, Function.Injective (t x)) (k : ℕ) :
    Continuous (fun x => ((interpolanteHermite (t x) (hi x)
      (fun j => datosManufacturados (t x j.1) j.2) : PolinomiosHermite n) : ℝ[X]).coeff k) := by
  by_cases hk : k < 4 * n
  · have hinv : Continuous (fun x => (matrizHermite325 (t x))⁻¹) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      refine (continuousAt_matrix_inv _ ?_).comp ((matrizHermite325_continua n).comp ht).continuousAt
      rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
      exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp (matrizHermite325_det (t x) (hi x)))
    have hdata := (vectorDatosHermite325_continuo n).comp ht
    have hvec : Continuous (fun x => ((matrizHermite325 (t x))⁻¹ *ᵥ vectorDatosHermite325 (t x))
        ⟨k, hk⟩) := by
      simp only [Matrix.mulVec, dotProduct]
      exact continuous_finsetSum _ fun i _ => (hinv.matrix_elem _ _).mul
        ((continuous_apply i).comp hdata)
    convert hvec using 1
    funext x
    exact congrFun (vectorCoefHermite325_eq (t x) (hi x)) ⟨k, hk⟩
  · convert (continuous_const : Continuous (fun _ : X => (0 : ℝ))) using 1
    funext x
    apply coeff_eq_zero_of_degree_lt
    exact (mem_degreeLT.mp (interpolanteHermite (t x) (hi x)
      (fun j => datosManufacturados (t x j.1) j.2)).property).trans_le (Nat.cast_le.mpr (le_of_not_gt hk))

private theorem representanteHermite_existe {m : ℕ} (t : Fin m → ℝ)
    (j : Fin (nodosDistintosHermite t).card) :
    (Finset.univ.filter fun i => t i = nodosOrdenadosHermite t j).Nonempty := by
  have hj := (nodosDistintosHermite t).orderEmbOfFin_mem rfl j
  change nodosOrdenadosHermite t j ∈ Finset.univ.image t at hj
  obtain ⟨i, hi, ht⟩ := Finset.mem_image.mp hj
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, ht⟩⟩

private def representanteHermite {m : ℕ} (t : Fin m → ℝ)
    (j : Fin (nodosDistintosHermite t).card) : Fin m :=
  (Finset.univ.filter fun i => t i = nodosOrdenadosHermite t j).min'
    (representanteHermite_existe t j)

private theorem representanteHermite_val {m : ℕ} (t : Fin m → ℝ)
    (j : Fin (nodosDistintosHermite t).card) :
    t (representanteHermite t j) = nodosOrdenadosHermite t j :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (representanteHermite_existe t j))).2

private theorem coefHermite325_continuo_estrato {m : ℕ}
    (p : Fin 2 → Fin m → Fin m → Bool) (a : Fin 2) (k : ℕ) :
    Continuous (fun s : estratoHermite p => (factorHermite325 s.1 a).coeff k) := by
  by_cases h : Nonempty (estratoHermite p)
  · obtain ⟨s₀⟩ := h
    let v₀ (i : Fin m) := s₀.1 i a
    let n := (nodosDistintosHermite v₀).card
    let t (s : estratoHermite p) (j : Fin n) := s.1 (representanteHermite v₀ j) a
    have ht : Continuous t := by
      apply continuous_pi
      intro j
      let r := representanteHermite v₀ j
      have hEval : Continuous (fun s : estratoHermite p => s.1 r) :=
        (continuous_apply r).comp continuous_subtype_val
      exact (EuclideanSpace.proj a : Plano →L[ℝ] ℝ).continuous.comp hEval
    have hi (s : estratoHermite p) : Function.Injective (t s) := by
      intro i j hij
      have hv := (estratoHermite_determina_colisiones s.2 s₀.2 a
        (representanteHermite v₀ i) (representanteHermite v₀ j)).mp hij
      apply (nodosOrdenadosHermite v₀).injective
      exact (representanteHermite_val v₀ i).symm.trans
        (hv.trans (representanteHermite_val v₀ j))
    have hall (s : estratoHermite p) (i : Fin m) : ∃ j, t s j = s.1 i a := by
      obtain ⟨j, hj⟩ := nodo_muestra_en_enumeracion v₀ i
      exact ⟨j, (estratoHermite_determina_colisiones s₀.2 s.2 a
        (representanteHermite v₀ j) i).mp ((representanteHermite_val v₀ j).trans hj)⟩
    have he (s : estratoHermite p) :
        factorHermite325 s.1 a =
          (interpolanteHermite (t s) (hi s)
            (fun j => datosManufacturados (t s j.1) j.2) : PolinomiosHermite n) := by
      have hsets : nodosDistintosHermite (fun i => s.1 i a) = Finset.univ.image (t s) := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨j, hj⟩ := hall s i
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
        · intro hx
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_image.mpr ⟨representanteHermite v₀ j, Finset.mem_univ _, rfl⟩
      have hcard : (nodosDistintosHermite (fun i => s.1 i a)).card = n := by
        rw [hsets, Finset.card_image_of_injective _ (hi s), Finset.card_univ, Fintype.card_fin]
      have hdeg : (factorHermite325 s.1 a).degree < 4 * n := by
        rw [← hcard]
        exact mem_degreeLT.mp (hermiteMuestra (fun i => s.1 i a) datosManufacturados).property
      let J : Fin n × Fin 4 → ℝ := fun j => datosManufacturados (t s j.1) j.2
      obtain ⟨q, hq, huniq⟩ := existe_unico_hermite (t s) (hi s) J
      exact (huniq _ ⟨hdeg, fun j l => factorHermite325_jet s.1 a _ l⟩).trans
        (huniq _ ⟨mem_degreeLT.mp (interpolanteHermite (t s) (hi s) J).property,
          interpolanteHermite_jet _ _ _⟩).symm
    convert coefHermite325_continuo t ht hi k using 1
    funext s
    exact congrArg (fun f : ℝ[X] => f.coeff k) (he s)
  · let : IsEmpty (estratoHermite p) := not_nonempty_iff.mp h
    exact continuous_of_discreteTopology

/-- Continuidad de los coeficientes tensoriales al fijar el patrón de orden. -/
theorem coeficientesHermite325_continuos_estrato {m : ℕ}
    (p : Fin 2 → Fin m → Fin m → Bool) :
    Continuous (fun s : estratoHermite p => coeficientesHermite325 s.1) := by
  apply continuous_pi
  intro j
  exact (coefHermite325_continuo_estrato p 0 j.1).mul (coefHermite325_continuo_estrato p 1 j.2)

/-- Los patrones son mutuamente excluyentes. Todo punto pertenece al
estrato de su propio patrón por `muestra_mem_estratoHermite`. -/
theorem estratosHermite_disjuntos {m : ℕ}
    {p q : Fin 2 → Fin m → Fin m → Bool} (h : p ≠ q) :
    Disjoint (estratoHermite p) (estratoHermite q) := by
  refine Set.disjoint_left.mpr fun s hp hq => h ?_
  exact funext fun a => funext fun i => funext fun j => (hp a i j).symm.trans (hq a i j)

/-- Selección boreliana del vector de coeficientes, incluidas las colisiones. -/
theorem coeficientesHermite325_borel (m : ℕ) :
    Measurable (coeficientesHermite325 (m := m)) := by
  intro V hV
  have he : coeficientesHermite325 (m := m) ⁻¹' V =
      ⋃ p : Fin 2 → Fin m → Fin m → Bool, Subtype.val ''
        ((fun s : estratoHermite p => coeficientesHermite325 s.1) ⁻¹' V) := by
    ext s
    constructor
    · intro hs
      exact mem_iUnion.mpr ⟨patronHermite s,
        ⟨⟨s, muestra_mem_estratoHermite s⟩, hs, rfl⟩⟩
    · intro hs
      obtain ⟨p, u, hu, rfl⟩ := mem_iUnion.mp hs
      exact hu
  rw [he]
  exact MeasurableSet.iUnion fun p => (MeasurableEmbedding.subtype_coe
    (estratoHermite_measurable p)).measurableSet_image'
      ((coeficientesHermite325_continuos_estrato p).measurable hV)

theorem pesosSalidaHermite325_borel (m : ℕ) :
    Measurable (fun s : Fin m → Plano => pesoSalida324 (coeficientesHermite325 s)) :=
  (pesosSalida324_continuos (4 * m - 1)).measurable.comp (coeficientesHermite325_borel m)

#check coeficientesHermite325_borel
#print axioms coeficientesHermite325_continuos_estrato
#print axioms coeficientesHermite325_borel
#print axioms pesosSalidaHermite325_borel


end TesisPINN

