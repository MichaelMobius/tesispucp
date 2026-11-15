import TesisPINN.MedidaFronteraCuadrado
import TesisPINN.TeoremasShin

/-! Cotas de masa y particiones de la frontera en la Hipótesis 3.2. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Set
open scoped ENNReal

private theorem otra_coord (i : Fin 2) : 1 - i ≠ i := by
  fin_cases i <;> decide

theorem masa_superior_frontera_cuadrado :
    MasaBolaSuperior medidaUniformeFrontera (frontier cuadrado) 1 1 1 := by
  intro x _ r hr _
  rw [medidaUniformeFrontera_apply _ (measurableSet_closedBall.inter
    isClosed_frontier.measurableSet), Real.rpow_one, one_mul]
  calc
    _ ≤ ENNReal.ofReal (1 / 8) * ∑ _ : IndiceCaraCuadrado, ENNReal.ofReal (2 * r) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) zero_le
      have hsub : puntoCara k.1 k.2 ⁻¹' (Metric.closedBall x r ∩ frontier cuadrado) ∩ Icc (-1 : ℝ) 1
          ⊆ Icc (x (1 - k.1) - r) (x (1 - k.1) + r) := by
        intro t ht
        have hcoord := PiLp.norm_apply_le (puntoCara k.1 k.2 t - x) (1 - k.1)
        have hdist : ‖puntoCara k.1 k.2 t - x‖ ≤ r := by
          rw [← dist_eq_norm]
          exact ht.1.1
        have h := hcoord.trans hdist
        simp only [PiLp.sub_apply, Real.norm_eq_abs, puntoCara, parCara_symm_coord,
          if_neg (otra_coord k.1), abs_le] at h
        exact ⟨by linarith [h.1], by linarith [h.2]⟩
      refine (measure_mono hsub).trans_eq ?_
      rw [Real.volume_Icc]
      congr 1
      ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_bool, nsmul_eq_mul]
      rw [show (2 : ℕ) * 2 = 4 by decide, show ((4 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      congr 1
      ring

/-- Para cualquier centro, incluido un vértice, una cara contiene un
segmento de longitud `r` dentro de la bola abierta. -/
theorem masa_inferior_frontera_cuadrado (x : Plano) (hx : x ∈ frontier cuadrado)
    (r : ℝ) (hr : 0 < r) (hr₁ : r ≤ 1) :
    r / 8 ≤ medidaUniformeFrontera.real (Metric.ball x r ∩ frontier cuadrado) := by
  rw [frontera_eq_union_caras, mem_iUnion] at hx
  obtain ⟨k, t, ht, rfl⟩ := hx
  let a := if 0 ≤ t then t - r else t
  let b := if 0 ≤ t then t else t + r
  have hab : b - a = r := by dsimp [a,b]; split <;> ring
  have hin : Ioo a b ⊆ Icc (-1 : ℝ) 1 := by
    intro y hy
    have h₁ := ht.1
    have h₂ := ht.2
    dsimp [a,b] at hy
    split at hy <;> exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hsub : puntoCara k.1 k.2 '' Ioo a b ⊆
      Metric.ball (puntoCara k.1 k.2 t) r ∩ frontier cuadrado := by
    rintro _ ⟨y, hy, rfl⟩
    constructor
    · rw [Metric.mem_ball, (puntoCara_isometria k).dist_eq, Real.dist_eq, abs_lt]
      dsimp [a,b] at hy
      split at hy <;> exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
    · rw [frontera_eq_union_caras, mem_iUnion]
      exact ⟨k, y, hin hy, rfl⟩
  refine le_trans ?_ (measureReal_mono hsub)
  rw [measureReal_def, medidaUniformeFrontera_imagen k _ hin measurableSet_Ioo,
    Real.volume_Ioo, hab, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr.le,
    ENNReal.toReal_ofReal (by norm_num)]
  exact le_of_eq (by ring)

private def caraAsignada (k : IndiceCaraCuadrado) : Set ℝ :=
  if k.1 = 0 then Icc (-1) 1 else Ioo (-1) 1

private theorem asignada_sub (k : IndiceCaraCuadrado) :
    caraAsignada k ⊆ Icc (-1 : ℝ) 1 := by
  unfold caraAsignada
  split
  · exact Subset.rfl
  · exact Ioo_subset_Icc_self

private theorem asignada_disjunta :
    Pairwise (fun k j : IndiceCaraCuadrado =>
      Disjoint (puntoCara k.1 k.2 '' caraAsignada k) (puntoCara j.1 j.2 '' caraAsignada j)) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ hne
  apply disjoint_left.mpr
  rintro _ ⟨t, ht, rfl⟩ ⟨u, hu, he⟩
  by_cases hij : j = i
  · subst j
    have hbc : b ≠ c := fun h => hne (by rw [h])
    have h := congrArg (fun x : Plano => x i) he
    change puntoCara i c u i = puntoCara i b t i at h
    cases b <;> cases c <;>
      first | exact (hbc rfl).elim | norm_num [puntoCara, parCara_symm_coord, extremoCara] at h
  · have hi := congrArg (fun x : Plano => x i) he
    have hj := congrArg (fun x : Plano => x j) he
    have hij' : i ≠ j := Ne.symm hij
    simp only [puntoCara, parCara_symm_coord, if_neg hij', if_neg hij, if_pos rfl] at hi hj
    fin_cases i <;> fin_cases j <;> cases b <;> cases c <;>
      norm_num [caraAsignada, extremoCara] at ht hu hi hj hij
    all_goals linarith [ht.1, ht.2, hu.1, hu.2]

private theorem asignada_cubre :
    frontier cuadrado ⊆ ⋃ k : IndiceCaraCuadrado, puntoCara k.1 k.2 '' caraAsignada k := by
  intro x hx
  rw [frontera_eq_union_caras, mem_iUnion] at hx
  obtain ⟨⟨i,b⟩, t, ht, rfl⟩ := hx
  by_cases hi : i = 0
  · exact mem_iUnion.mpr ⟨(i,b), t, by simpa [caraAsignada, hi] using ht, rfl⟩
  · by_cases ht' : t ∈ Ioo (-1 : ℝ) 1
    · exact mem_iUnion.mpr ⟨(i,b), t, by simpa [caraAsignada, hi] using ht', rfl⟩
    · have htex : t = -1 ∨ t = 1 := by
        rcases eq_or_lt_of_le ht.1 with he | he
        · exact Or.inl he.symm
        · rcases eq_or_lt_of_le ht.2 with he' | he'
          · exact Or.inr he'
          · exact False.elim (ht' ⟨he, he'⟩)
      have hi' : i = 1 := by fin_cases i <;> simp_all
      subst i
      rcases htex with rfl | rfl
      · refine mem_iUnion.mpr ⟨(0,false), extremoCara b, ?_, ?_⟩
        · cases b <;> norm_num [caraAsignada, extremoCara]
        · apply PiLp.ext
          intro j
          fin_cases j <;> simp [puntoCara, parCara_symm_coord, extremoCara]
      · refine mem_iUnion.mpr ⟨(0,true), extremoCara b, ?_, ?_⟩
        · cases b <;> norm_num [caraAsignada, extremoCara]
        · apply PiLp.ext
          intro j
          fin_cases j <;> simp [puntoCara, parCara_symm_coord, extremoCara]

private def extremoMalla (l : ℝ) (j : ℕ) : ℝ := -1 + j * l

private def intervaloMalla (N : ℕ) (l : ℝ) (j : Fin N) : Set ℝ :=
  Ico (extremoMalla l j) (extremoMalla l (j.val + 1)) ∪
    (if j.val + 1 = N then {1} else ∅)

/-- Cada cara se divide en `⌈2/η⌉` segmentos. Un único lado recibe
cada vértice y cada punto de la subdivisión se asigna una sola vez. -/
theorem particiones_uniformes_frontera_cuadrado :
    ParticionesMinimas medidaUniformeFrontera (frontier cuadrado) (1 / 12) 1 1 := by
  intro η hη hη₁
  let N := ⌈2 / η⌉₊
  have hN : 0 < N := Nat.one_le_ceil_iff.mpr (by positivity)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let l : ℝ := 2 / N
  have hl : 0 < l := by dsimp [l]; positivity
  have hNl : (N : ℝ) * l = 2 := by dsimp [l]; field_simp
  have hle : l ≤ η := by
    have h := (div_le_iff₀ hη).mp (Nat.le_ceil (2 / η))
    exact (div_le_iff₀ hNr).mpr (by simpa [mul_comm] using h)
  have hlow : 2 * η / 3 ≤ l := by
    have hceil : (N : ℝ) < 2 / η + 1 := Nat.ceil_lt_add_one (by positivity)
    have ht := mul_lt_mul_of_pos_right hceil hη
    rw [add_mul, div_mul_cancel₀ _ hη.ne', one_mul] at ht
    apply (le_div_iff₀ hNr).2
    nlinarith
  have hstart (j : Fin N) : -1 ≤ extremoMalla l j := le_add_of_nonneg_right (by positivity)
  have hend (j : Fin N) : extremoMalla l (j.val + 1) ≤ 1 := by
    have hj : (((j.val + 1 : ℕ) : ℝ)) ≤ N := by exact_mod_cast j.isLt
    unfold extremoMalla
    linarith [mul_le_mul_of_nonneg_right hj hl.le]
  have hstep (j : Fin N) : extremoMalla l (j.val + 1) - extremoMalla l j = l := by
    simp [extremoMalla]; ring
  have hmono : Monotone (extremoMalla l) := fun a b hab =>
    add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hl.le) _
  have hIcc (j : Fin N) : intervaloMalla N l j ⊆ Icc (extremoMalla l j) (extremoMalla l (j.val + 1)) := by
    intro t ht
    rcases ht with ht | ht
    · exact ⟨ht.1, ht.2.le⟩
    · by_cases hj : j.val + 1 = N
      · have he : extremoMalla l (j.val + 1) = 1 := by
          rw [hj]; unfold extremoMalla; linarith
        rw [if_pos hj, mem_singleton_iff] at ht
        exact ⟨by linarith [hstep j], by linarith⟩
      · simp [hj] at ht
  have hcover : Icc (-1 : ℝ) 1 ⊆ ⋃ j : Fin N, intervaloMalla N l j := by
    intro t ht
    by_cases htop : t = 1
    · let j : Fin N := ⟨N-1, by omega⟩
      have hj : j.val + 1 = N := by dsimp [j]; omega
      exact mem_iUnion.mpr ⟨j, Or.inr (by simp [hj, htop])⟩
    · have hnon : 0 ≤ (t + 1) / l := div_nonneg (by linarith [ht.1]) hl.le
      have ht' : t < 1 := lt_of_le_of_ne ht.2 htop
      let j : Fin N := ⟨⌊(t+1)/l⌋₊, (Nat.floor_lt hnon).2 ((div_lt_iff₀ hl).2 (by linarith))⟩
      have hlo := (le_div_iff₀ hl).mp (Nat.floor_le hnon)
      have hhi := (div_lt_iff₀ hl).mp (Nat.lt_floor_add_one ((t + 1) / l))
      refine mem_iUnion.mpr ⟨j, Or.inl ⟨?_, ?_⟩⟩
      · dsimp [extremoMalla, j]; linarith
      · dsimp [extremoMalla, j]; push_cast; linarith
  have hdisj : Pairwise (fun i j : Fin N => Disjoint (intervaloMalla N l i) (intervaloMalla N l j)) := by
    have aux (i j : Fin N) (hij : i.val < j.val) :
        Disjoint (intervaloMalla N l i) (intervaloMalla N l j) := by
      refine disjoint_left.mpr (fun t ht hu => ?_)
      have hi : i.val + 1 ≠ N := by have := j.isLt; omega
      have ht' : t < extremoMalla l (i.val + 1) := by
        have h : t ∈ Ico (extremoMalla l i) (extremoMalla l (i.val + 1)) := by
          simpa [intervaloMalla, hi] using ht
        exact h.2
      exact (not_lt_of_ge ((hmono (show i.val + 1 ≤ j.val by omega)).trans ((hIcc j hu).1))) ht'
    intro i j h
    rcases lt_or_gt_of_ne (fun he : i.val = j.val => h (Fin.ext he)) with hij | hji
    · exact aux i j hij
    · exact (aux j i hji).symm
  let J := IndiceCaraCuadrado × Fin N
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin _
  let S (j : J) := caraAsignada j.1 ∩ intervaloMalla N l j.2
  let cells (k : Fin (Fintype.card J)) :=
    puntoCara (e.symm k).1.1 (e.symm k).1.2 '' S (e.symm k)
  refine ⟨Fintype.card J, cells, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    apply ((puntoCara_isometria _).isClosedEmbedding.measurableEmbedding.measurableSet_image).mpr
    apply MeasurableSet.inter
    · unfold caraAsignada
      split <;> measurability
    · unfold intervaloMalla
      exact measurableSet_Ico.union (by split <;> measurability)
  · intro k j hkj
    apply disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ ⟨u, hu, he⟩
    have hk : e.symm k ≠ e.symm j := fun h => hkj (e.symm.injective h)
    by_cases h : (e.symm k).1 = (e.symm j).1
    · have htU : t = u := (puntoCara_isometria (e.symm k).1).injective (by simpa only [← h] using he.symm)
      subst u
      have hh : (e.symm k).2 ≠ (e.symm j).2 := fun heq => hk (Prod.ext h heq)
      exact disjoint_left.mp (hdisj hh) ht.2 hu.2
    · exact disjoint_left.mp (asignada_disjunta h) ⟨t, ht.1, rfl⟩ ⟨u, hu.1, he⟩
  · intro x hx
    obtain ⟨k, t, ht, rfl⟩ := mem_iUnion.mp (asignada_cubre hx)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover (asignada_sub k ht))
    refine mem_iUnion.mpr ⟨e (k,j), ?_⟩
    simpa only [cells, Equiv.symm_apply_apply] using
      (show puntoCara k.1 k.2 t ∈ puntoCara k.1 k.2 '' S (k,j) from ⟨t, ⟨ht,hj⟩, rfl⟩)
  · intro k
    exact (image_mono fun _ h => asignada_sub _ h.1).trans
      (frontera_eq_union_caras.symm ▸ subset_iUnion caraFrontera (e.symm k).1)
  · intro k
    let j := (e.symm k).2
    let b := (e.symm k).1
    have hsub : Ioo (extremoMalla l j) (extremoMalla l (j.val + 1)) ⊆ S (e.symm k) := by
      intro t ht
      have hin : t ∈ Ioo (-1 : ℝ) 1 := ⟨(hstart j).trans_lt ht.1, ht.2.trans_le (hend j)⟩
      refine ⟨?_, Or.inl ⟨ht.1.le, ht.2⟩⟩
      unfold caraAsignada
      split
      · exact Ioo_subset_Icc_self hin
      · exact hin
    have hmass : medidaUniformeFrontera.real
        (puntoCara b.1 b.2 '' Ioo (extremoMalla l j) (extremoMalla l (j.val + 1))) = l / 8 := by
      rw [measureReal_def, medidaUniformeFrontera_imagen b _ (hsub.trans (fun _ h => asignada_sub _ h.1))
        measurableSet_Ioo, Real.volume_Ioo, hstep, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hl.le, ENNReal.toReal_ofReal (by norm_num)]
      ring
    rw [Real.rpow_one]
    exact (show (1 / 12 : ℝ) * η ≤ l / 8 by linarith).trans
      (hmass.symm ▸ measureReal_mono (image_mono hsub))
  · rintro k _ ⟨t, ht, rfl⟩ _ ⟨u, hu, rfl⟩
    rw [(puntoCara_isometria (e.symm k).1).dist_eq, Real.dist_eq]
    have ht' := hIcc _ ht.2
    have hu' := hIcc _ hu.2
    have habs : |t - u| ≤ l := by
      rw [abs_le]
      constructor <;> linarith [ht'.1, ht'.2, hu'.1, hu'.2, hstep (e.symm k).2]
    exact habs.trans (hle.trans (le_mul_of_one_le_left hη.le (by simp)))

def datosMasa38_frontera_cuadrado :
    DatosMasa38 medidaUniformeFrontera (frontier cuadrado) 1 1 where
  c := 1 / 12
  C := 1
  c_pos := by norm_num
  C_pos := by norm_num
  medible := isClosed_frontier.measurableSet
  acotado := cuadrado_acotado.closure.subset frontier_subset_closure
  concentrada := medidaUniformeFrontera_concentrada
  superior := masa_superior_frontera_cuadrado
  particiones := particiones_uniformes_frontera_cuadrado

#check datosMasa38_frontera_cuadrado
#print axioms masa_superior_frontera_cuadrado
#print axioms masa_inferior_frontera_cuadrado
#print axioms datosMasa38_frontera_cuadrado

end TesisPINN
