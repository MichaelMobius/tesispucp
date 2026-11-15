import TesisPINN.Proposicion321
import TesisPINN.TrazaSobolevCuadrado
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! Longitud de la frontera del cuadrado y su ley uniforme. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Set
open scoped ENNReal

abbrev IndiceCaraCuadrado := Fin 2 × Bool

def caraFrontera (k : IndiceCaraCuadrado) : Set Plano :=
  puntoCara k.1 k.2 '' Icc (-1 : ℝ) 1

theorem puntoCara_isometria (k : IndiceCaraCuadrado) : Isometry (puntoCara k.1 k.2) := by
  apply Isometry.of_dist_eq
  intro t u
  rw [dist_eq_norm, Real.dist_eq]
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, sq_abs]
  rcases k with ⟨i, b⟩
  fin_cases i <;> simp [PiLp.sub_apply, puntoCara, parCara_symm_coord]

theorem caraFrontera_medible (k : IndiceCaraCuadrado) : MeasurableSet (caraFrontera k) :=
  (isCompact_Icc.image (puntoCara_isometria k).continuous).isClosed.measurableSet

theorem frontera_eq_union_caras : frontier cuadrado = ⋃ k, caraFrontera k := by
  ext x
  rw [cuadrado_abierto.frontier_eq, clausura_cuadrado, mem_iUnion]
  constructor
  · intro hx
    have hbd : ∃ i : Fin 2, x i = -1 ∨ x i = 1 := by
      by_contra! hn
      apply hx.2
      intro i
      exact ⟨lt_of_le_of_ne (hx.1 i).1 (Ne.symm (hn i).1),
        lt_of_le_of_ne (hx.1 i).2 (hn i).2⟩
    obtain ⟨i, hi⟩ := hbd
    obtain ⟨b, hb⟩ : ∃ b : Bool, x i = extremoCara b := by
      rcases hi with hi | hi
      · exact ⟨false, hi⟩
      · exact ⟨true, hi⟩
    refine ⟨(i, b), x (1 - i), hx.1 _, ?_⟩
    apply PiLp.ext
    intro j
    fin_cases i <;> fin_cases j <;> simp_all [puntoCara, parCara_symm_coord]
  · rintro ⟨⟨i, b⟩, t, ht, rfl⟩
    refine ⟨fun j => ?_, fun h => ?_⟩
    · simp only [puntoCara, parCara_symm_coord]
      split
      · cases b <;> norm_num [extremoCara]
      · exact ht
    · have hb := h i
      change puntoCara i b t i ∈ Ioo (-1 : ℝ) 1 at hb
      cases b <;> norm_num [puntoCara, parCara_symm_coord, extremoCara] at hb

theorem longitud_imagen_cara (k : IndiceCaraCuadrado) (A : Set ℝ) :
    (μH[1] : Measure Plano) (puntoCara k.1 k.2 '' A) = volume A := by
  rw [(puntoCara_isometria k).hausdorffMeasure_image (Or.inl zero_le_one),
    hausdorffMeasure_real]

private theorem caras_inter_longitud_cero :
    Pairwise (fun k l : IndiceCaraCuadrado => (μH[1] : Measure Plano) (caraFrontera k ∩ caraFrontera l) = 0) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ hne
  have hsub : caraFrontera (i,b) ∩ caraFrontera (j,c) ⊆
      puntoCara i b '' ({-1, 1} : Set ℝ) := by
    rintro _ ⟨⟨t, _, rfl⟩, u, _, hu⟩
    by_cases hij : j = i
    · subst j
      have hc : b ≠ c := fun h => hne (by rw [h])
      have he := congrArg (fun x : Plano => x i) hu
      change puntoCara i c u i = puntoCara i b t i at he
      cases b <;> cases c <;>
        first | exact (hc rfl).elim | norm_num [puntoCara, parCara_symm_coord, extremoCara] at he
    · have ht : t = extremoCara c := by
        have he := congrArg (fun x : Plano => x j) hu
        simpa [puntoCara, parCara_symm_coord, hij] using he.symm
      refine ⟨t, ?_, rfl⟩
      cases c <;> simp [ht, extremoCara]
  apply le_antisymm ((measure_mono hsub).trans_eq ?_) zero_le
  rw [longitud_imagen_cara (i,b)]
  exact (by simp : Set.Countable ({-1, 1} : Set ℝ)).measure_zero volume

/-- Probabilidad uniforme de la frontera, respecto de longitud Hausdorff. -/
def medidaUniformeFrontera : Measure Plano :=
  ENNReal.ofReal (1 / 8) • (μH[1] : Measure Plano).restrict (frontier cuadrado)

theorem medidaUniformeFrontera_apply (A : Set Plano) (hA : MeasurableSet A) :
    medidaUniformeFrontera A = ENNReal.ofReal (1 / 8) *
      ∑ k : IndiceCaraCuadrado, volume (puntoCara k.1 k.2 ⁻¹' A ∩ Icc (-1 : ℝ) 1) := by
  rw [medidaUniformeFrontera, Measure.smul_apply, smul_eq_mul, frontera_eq_union_caras,
    Measure.restrict_iUnion_apply_ae (fun i j hij => caras_inter_longitud_cero hij)
      (fun k => (caraFrontera_medible k).nullMeasurableSet) hA, tsum_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Measure.restrict_apply hA]
  rw [show A ∩ caraFrontera k = puntoCara k.1 k.2 '' (puntoCara k.1 k.2 ⁻¹' A ∩ Icc (-1 : ℝ) 1) by
    rw [inter_comm (puntoCara k.1 k.2 ⁻¹' A), image_inter_preimage, inter_comm A, caraFrontera]]
  exact longitud_imagen_cara k _

instance : IsProbabilityMeasure medidaUniformeFrontera where
  measure_univ := by
    rw [medidaUniformeFrontera_apply _ MeasurableSet.univ]
    simp only [preimage_univ, univ_inter, Real.volume_Icc, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
    norm_num
    rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num

theorem medidaUniformeFrontera_concentrada :
    medidaUniformeFrontera (frontier cuadrado)ᶜ = 0 := by
  rw [medidaUniformeFrontera, Measure.smul_apply, Measure.restrict_apply
    isClosed_frontier.measurableSet.compl, compl_inter_self, measure_empty, smul_zero]

theorem medidaUniformeFrontera_imagen (k : IndiceCaraCuadrado) (A : Set ℝ)
    (hA : A ⊆ Icc (-1 : ℝ) 1) (hm : MeasurableSet A) :
    medidaUniformeFrontera (puntoCara k.1 k.2 '' A) = ENNReal.ofReal (1 / 8) * volume A := by
  have he : MeasurableEmbedding (puntoCara k.1 k.2) :=
    (puntoCara_isometria k).isClosedEmbedding.measurableEmbedding
  rw [medidaUniformeFrontera, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply
    (he.measurableSet_image.mpr hm), inter_eq_left.mpr ?_, longitud_imagen_cara k]
  rw [frontera_eq_union_caras]
  exact (image_mono hA).trans (subset_iUnion caraFrontera k)

theorem medidaUniformeFrontera_cara (k : IndiceCaraCuadrado) :
    medidaUniformeFrontera (caraFrontera k) = ENNReal.ofReal (1 / 4) := by
  rw [caraFrontera, medidaUniformeFrontera_imagen k _ Subset.rfl measurableSet_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem medidaUniformeFrontera_punto (x : Plano) : medidaUniformeFrontera {x} = 0 := by
  letI := Measure.nullSingletonClass_hausdorff Plano (by norm_num : (0 : ℝ) < 1)
  rw [medidaUniformeFrontera, Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton _)]
  have hz : (μH[1] : Measure Plano) ({x} ∩ frontier cuadrado) = 0 :=
    le_antisymm ((measure_mono inter_subset_left).trans_eq (measure_singleton x)) zero_le
  simp [hz]

theorem medidaUniformeFrontera_densidad :
    medidaUniformeFrontera = ((μH[1] : Measure Plano).restrict (frontier cuadrado)).withDensity
      (fun _ => ENNReal.ofReal (1 / 8)) := by
  rw [withDensity_const, medidaUniformeFrontera]

#check medidaUniformeFrontera_densidad
#print axioms medidaUniformeFrontera_densidad
#print axioms medidaUniformeFrontera_cara
#print axioms medidaUniformeFrontera_punto

end TesisPINN
