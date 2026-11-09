import TesisPINN.CoberturaPINN
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Partición medible de Voronoi con desempate por el índice mínimo. -/

noncomputable section

namespace TesisPINN

open MeasureTheory

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {m : ℕ}

/-- La distancia decide primero; en caso de empate decide `Fin m`. -/
def celdaVoronoi (U : Set X) (s : Fin m → X) (i : Fin m) : Set X :=
  {x | x ∈ U ∧ ∀ j : Fin m,
    toLex (dist x (s i), i) ≤
      toLex (dist x (s j), j)}

theorem celdaVoronoi_subset (U : Set X) (s : Fin m → X) (i : Fin m) :
    celdaVoronoi U s i ⊆ U := fun _ hx => hx.1

theorem celdaVoronoi_cover (U : Set X) (s : Fin m → X)
    (hm : 0 < m) : U = ⋃ i : Fin m, celdaVoronoi U s i := by
  classical
  ext x
  constructor
  · intro hx
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    obtain ⟨i, hi⟩ := Finite.exists_min
      (fun i : Fin m => toLex (dist x (s i), i))
    exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hi.1

theorem celdaVoronoi_pairwise (U : Set X) (s : Fin m → X) :
    Pairwise (fun i j => Disjoint (celdaVoronoi U s i) (celdaVoronoi U s j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hle := hxi.2 j
  have hge := hxj.2 i
  have heq := le_antisymm hle hge
  have : i = j := congrArg (fun p : ℝ ×ₗ Fin m => (ofLex p).2) heq
  exact hij this

theorem celdaVoronoi_measurable (U : Set X) (hU : MeasurableSet U)
    (s : Fin m → X) (i : Fin m) : MeasurableSet (celdaVoronoi U s i) := by
  classical
  unfold celdaVoronoi
  rw [show {x : X | x ∈ U ∧ ∀ j : Fin m,
      toLex (dist x (s i), i) ≤ toLex (dist x (s j), j)} =
      U ∩ ⋂ j : Fin m, {x : X | toLex (dist x (s i), i) ≤
        toLex (dist x (s j), j)} by ext x; simp]
  apply hU.inter
  apply MeasurableSet.iInter
  intro j
  change MeasurableSet
    {x : X | toLex (dist x (s i), i) ≤
      toLex (dist x (s j), j)}
  rw [show {x : X | toLex (dist x (s i), i) ≤
      toLex (dist x (s j), j)} =
      {x : X | dist x (s i) < dist x (s j) ∨
        dist x (s i) = dist x (s j) ∧ i ≤ j} by
      ext x; exact Prod.Lex.toLex_le_toLex]
  have hi : Measurable (fun x : X => dist x (s i)) := by fun_prop
  have hj : Measurable (fun x : X => dist x (s j)) := by fun_prop
  by_cases hij : i ≤ j
  · simpa only [hij, and_true, Set.setOf_or] using
      (measurableSet_lt hi hj).union (measurableSet_eq_fun hi hj)
  · simpa only [hij, and_false, or_false] using (measurableSet_lt hi hj)

theorem celdaVoronoi_subset_closedBall
    (U : Set X) (s : Fin m → X) (ε : ℝ)
    (hcover : MuestrasCubren U s ε) (i : Fin m) :
    celdaVoronoi U s i ⊆ Metric.closedBall (s i) ε ∩ U := by
  intro x hx
  obtain ⟨j, hj⟩ := hcover x hx.1
  have hle : dist x (s i) ≤ dist x (s j) :=
    (Prod.Lex.toLex_le_toLex').mp (hx.2 j) |>.1
  exact ⟨Metric.mem_closedBall.mpr (by simpa only [dist_comm (s i) x] using hle.trans hj), hx.1⟩

theorem medida_celdaVoronoi_le
    (μ : Measure X) (U : Set X) (s : Fin m → X)
    (ε ε₀ C d : ℝ) (hε : 0 < ε) (hε₀ : ε ≤ ε₀)
    (hs : ∀ i, s i ∈ U) (hcover : MuestrasCubren U s ε)
    (hmass : MasaBolaSuperior μ U ε₀ C d) (i : Fin m) :
    μ (celdaVoronoi U s i) ≤ ENNReal.ofReal (C * ε ^ d) :=
  (measure_mono (celdaVoronoi_subset_closedBall U s ε hcover i)).trans
    (hmass (s i) (hs i) ε hε hε₀)

#print axioms TesisPINN.celdaVoronoi_cover
#print axioms TesisPINN.celdaVoronoi_pairwise
#print axioms TesisPINN.celdaVoronoi_measurable
#print axioms TesisPINN.medida_celdaVoronoi_le

end TesisPINN
