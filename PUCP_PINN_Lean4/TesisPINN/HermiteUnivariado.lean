import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Prod

/-! Interpolación de Hermite de orden cuatro sobre nodos distintos. -/

noncomputable section

namespace TesisPINN

open Polynomial
open scoped Polynomial

abbrev PolinomiosHermite (n : ℕ) := degreeLT ℝ (4 * n)

private def derivadasHermite : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]
  | 0 => LinearMap.id
  | k + 1 => derivative.comp (derivadasHermite k)

theorem derivadasHermite_apply (k : ℕ) (p : ℝ[X]) :
    derivadasHermite k p = (derivative^[k]) p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change derivative (derivadasHermite k p) = _
    rw [ih, Function.iterate_succ_apply']

def jetHermite (t : ℝ) (k : Fin 4) : ℝ[X] →ₗ[ℝ] ℝ :=
  (leval t).comp (derivadasHermite k)

theorem jetHermite_eval (t : ℝ) (k : Fin 4) (p : ℝ[X]) :
    jetHermite t k p = ((derivative^[k.val]) p).eval t := by
  change (derivadasHermite k p).eval t = _
  rw [derivadasHermite_apply]

def mapaJetsHermite {n : ℕ} (t : Fin n → ℝ) :
    PolinomiosHermite n →ₗ[ℝ] (Fin n × Fin 4 → ℝ) :=
  LinearMap.pi (fun j => (jetHermite (t j.1) j.2).comp (degreeLT ℝ (4 * n)).subtype)

@[simp] theorem mapaJetsHermite_apply {n : ℕ} (t : Fin n → ℝ)
    (p : PolinomiosHermite n) (i : Fin n) (k : Fin 4) :
    mapaJetsHermite t p (i, k) = jetHermite (t i) k p := rfl

/-- El producto de los factores con multiplicidad cuatro divide todo
polinomio cuyos cuatro jets se anulan en los nodos. -/
theorem producto_hermite_dvd {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t)
    (p : ℝ[X]) (h : ∀ i k, jetHermite (t i) k p = 0) :
    (∏ i, (X - C (t i)) ^ 4) ∣ p := by
  by_cases hp : p = 0
  · simp [hp]
  apply Fintype.prod_dvd_of_coprime
  · intro i j hij
    exact (pairwise_coprime_X_sub_C ht hij).pow
  · intro i
    apply (le_rootMultiplicity_iff hp).mp
    have hm : 3 < p.rootMultiplicity (t i) :=
      lt_rootMultiplicity_of_isRoot_iterate_derivative hp (n := 3) (fun k hk => by
        exact (jetHermite_eval (t i) ⟨k, Nat.lt_succ_of_le hk⟩ p).symm.trans (h i _))
    exact hm

theorem mapaJetsHermite_inyectivo {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t) :
    Function.Injective (mapaJetsHermite t) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  apply Subtype.ext
  change (p : ℝ[X]) = 0
  by_contra hn
  have hdvd := producto_hermite_dvd t ht (p : ℝ[X]) (fun i k => by
    simpa only [mapaJetsHermite_apply, Pi.zero_apply] using congrFun hp (i, k))
  have hm : (∏ i, (X - C (t i)) ^ 4).Monic :=
    monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _
  have hdeg : (∏ i, (X - C (t i)) ^ 4).natDegree = 4 * n := by
    rw [natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_sub_C _).pow _)]
    simp [natDegree_pow, Nat.mul_comm]
  have hb := hm.natDegree_le_of_dvd hn hdvd
  rw [hdeg] at hb
  exact (not_lt_of_ge hb) ((natDegree_lt_iff_degree_lt hn).mpr (mem_degreeLT.mp p.property))

theorem mapaJetsHermite_biyectivo {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t) :
    Function.Bijective (mapaJetsHermite t) := by
  have hd : Module.finrank ℝ (PolinomiosHermite n) =
      Module.finrank ℝ (Fin n × Fin 4 → ℝ) := by
    rw [Module.finrank_eq_card_basis (degreeLT.basis ℝ (4 * n)), Module.finrank_pi]
    simp [Fintype.card_prod, Nat.mul_comm]
  exact ⟨mapaJetsHermite_inyectivo t ht,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp (mapaJetsHermite_inyectivo t ht)⟩

def interpolanteHermite {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t)
    (datos : Fin n × Fin 4 → ℝ) : PolinomiosHermite n :=
  (LinearEquiv.ofBijective (mapaJetsHermite t) (mapaJetsHermite_biyectivo t ht)).symm datos

theorem interpolanteHermite_jet {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t)
    (datos : Fin n × Fin 4 → ℝ) (i : Fin n) (k : Fin 4) :
    jetHermite (t i) k (interpolanteHermite t ht datos) = datos (i, k) := by
  change mapaJetsHermite t (interpolanteHermite t ht datos) (i, k) = _
  exact congrFun ((LinearEquiv.ofBijective (mapaJetsHermite t)
    (mapaJetsHermite_biyectivo t ht)).apply_symm_apply datos) (i, k)

theorem existe_unico_hermite {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t)
    (datos : Fin n × Fin 4 → ℝ) :
    ∃! p : ℝ[X], p.degree < 4 * n ∧ ∀ i k, jetHermite (t i) k p = datos (i, k) := by
  let p := interpolanteHermite t ht datos
  refine ⟨p, ⟨mem_degreeLT.mp p.property, interpolanteHermite_jet t ht datos⟩, ?_⟩
  intro q hq
  let Q : PolinomiosHermite n := ⟨q, mem_degreeLT.mpr hq.1⟩
  have he : mapaJetsHermite t Q = mapaJetsHermite t p := by
    funext j
    exact (hq.2 j.1 j.2).trans (interpolanteHermite_jet t ht datos j.1 j.2).symm
  exact congrArg Subtype.val (mapaJetsHermite_inyectivo t ht he)

#check existe_unico_hermite
#print axioms producto_hermite_dvd
#print axioms existe_unico_hermite

end TesisPINN
