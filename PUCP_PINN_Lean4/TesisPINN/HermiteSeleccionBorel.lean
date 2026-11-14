import TesisPINN.HermiteTensorial

/-! Partición boreliana por los patrones de orden de las proyecciones. -/

noncomputable section

namespace TesisPINN

def patronHermite {m : ℕ} (s : Fin m → Plano) (a : Fin 2) (i j : Fin m) : Bool :=
  decide (s i a ≤ s j a)

def estratoHermite {m : ℕ} (p : Fin 2 → Fin m → Fin m → Bool) : Set (Fin m → Plano) :=
  {s | ∀ a i j, patronHermite s a i j = p a i j}

theorem estratoHermite_measurable {m : ℕ} (p : Fin 2 → Fin m → Fin m → Bool) :
    MeasurableSet (estratoHermite p) := by
  have h (i : Fin m) (a : Fin 2) : Continuous (fun s : Fin m → Plano => s i a) :=
    (EuclideanSpace.proj a : Plano →L[ℝ] ℝ).continuous.comp (continuous_apply i)
  simp only [estratoHermite, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  cases he : p a i j
  · simpa [patronHermite, he, not_le] using
      (isOpen_lt (h j a) (h i a)).measurableSet
  · simpa [patronHermite, he] using (isClosed_le (h i a) (h j a)).measurableSet

theorem muestra_mem_estratoHermite {m : ℕ} (s : Fin m → Plano) :
    s ∈ estratoHermite (patronHermite s) := fun _ _ _ => rfl

theorem estratoHermite_determina_colisiones {m : ℕ}
    {p : Fin 2 → Fin m → Fin m → Bool} {s t : Fin m → Plano}
    (hs : s ∈ estratoHermite p) (ht : t ∈ estratoHermite p)
    (a : Fin 2) (i j : Fin m) :
    s i a = s j a ↔ t i a = t j a := by
  have h (k l : Fin m) : s k a ≤ s l a ↔ t k a ≤ t l a := by
    have he := (hs a k l).trans (ht a k l).symm
    exact decide_eq_decide.mp he
  rw [le_antisymm_iff, le_antisymm_iff, h i j, h j i]

#check estratoHermite_measurable
#print axioms estratoHermite_measurable

end TesisPINN
