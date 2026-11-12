import TesisPINN.DirichletCuadrado
import TesisPINN.OcupacionLogaritmica
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Medida uniforme y particiones del cuadrado para el muestreo interior. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Set
open scoped ENNReal

private def cajaAbierta (a b : Fin 2 → ℝ) : Set Plano :=
  WithLp.ofLp ⁻¹' (univ.pi fun i => Ioo (a i) (b i))

private theorem cajaAbierta_medible (a b : Fin 2 → ℝ) :
    MeasurableSet (cajaAbierta a b) :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).preimage
    (PiLp.volume_preserving_ofLp (ι := Fin 2)).measurable

private theorem volumen_cajaAbierta (a b : Fin 2 → ℝ) :
    (volume : Measure Plano) (cajaAbierta a b) =
      ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [cajaAbierta, (PiLp.volume_preserving_ofLp (ι := Fin 2)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, volume_pi_pi]
  simp only [Real.volume_Ioo]

theorem volumen_cuadrado : (volume : Measure Plano) cuadrado = 4 := by
  have h : cuadrado = cajaAbierta (fun _ => -1) (fun _ => 1) := by
    ext x
    simp [cuadrado, EllipticPdes.Poincare.euclBox, cajaAbierta]
  rw [h, volumen_cajaAbierta, Fin.prod_univ_two]
  norm_num

/-- Ley uniforme de probabilidad del cuadrado abierto. -/
def medidaUniformeCuadrado : Measure Plano :=
  (ENNReal.ofReal (1 / 4)) • (volume : Measure Plano).restrict cuadrado

theorem medidaUniformeCuadrado_apply (A : Set Plano) (hA : MeasurableSet A) :
    medidaUniformeCuadrado A = ENNReal.ofReal (1 / 4) * volume (A ∩ cuadrado) := by
  rw [medidaUniformeCuadrado, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]

instance : IsProbabilityMeasure medidaUniformeCuadrado where
  measure_univ := by
    rw [medidaUniformeCuadrado_apply _ MeasurableSet.univ, univ_inter, volumen_cuadrado]
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num

theorem medidaUniformeCuadrado_concentrada : medidaUniformeCuadrado cuadradoᶜ = 0 := by
  rw [medidaUniformeCuadrado_apply _ cuadrado_abierto.measurableSet.compl]
  simp

theorem medidaUniformeCuadrado_densidad :
    medidaUniformeCuadrado = ((volume : Measure Plano).restrict cuadrado).withDensity
      (fun _ => ENNReal.ofReal (1 / 4)) := by
  rw [withDensity_const, medidaUniformeCuadrado]

theorem integral_medidaUniformeCuadrado (g : Plano → ℝ) :
    (∫ x, g x ∂medidaUniformeCuadrado) = (1 / 4) * ∫ x in cuadrado, g x := by
  rw [medidaUniformeCuadrado, integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_ofReal (by norm_num)]

theorem masa_bola_uniforme_cuadrado :
    MasaBolaSuperior medidaUniformeCuadrado cuadrado 1 (Real.pi / 4) 2 := by
  intro x _ ε hε _
  rw [medidaUniformeCuadrado_apply _ (measurableSet_closedBall.inter
    cuadrado_abierto.measurableSet), inter_assoc, inter_self]
  calc
    _ ≤ ENNReal.ofReal (1 / 4) * volume (Metric.closedBall x ε) :=
      mul_le_mul_of_nonneg_left (measure_mono inter_subset_left) zero_le
    _ = _ := by
      rw [EuclideanSpace.volume_closedBall_fin_two, Real.rpow_two,
        ← ENNReal.ofReal_pow hε.le, ← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

private def bordeCelda (l : ℝ) (k : ℕ) : ℝ := -1 + (k : ℝ) * l

private def celdaCuadrado (l : ℝ) {N : ℕ} (k : Fin 2 → Fin N) : Set Plano :=
  cuadrado ∩ WithLp.ofLp ⁻¹' (univ.pi fun i =>
    Ico (bordeCelda l (k i)) (bordeCelda l ((k i).val + 1)))

private theorem celdaCuadrado_medible (l : ℝ) {N : ℕ} (k : Fin 2 → Fin N) :
    MeasurableSet (celdaCuadrado l k) :=
  cuadrado_abierto.measurableSet.inter
    ((MeasurableSet.univ_pi fun _ => measurableSet_Ico).preimage
      (PiLp.volume_preserving_ofLp (ι := Fin 2)).measurable)

/-- La cuadrícula de lado `2/⌈2/η⌉` usa celdas semiabiertas recortadas
al cuadrado. La disjunción es exacta incluso en las líneas de la cuadrícula. -/
theorem particiones_uniformes_cuadrado :
    ParticionesOcupacionLog medidaUniformeCuadrado cuadrado (Real.sqrt 2) (1 / 9) 2 1 := by
  intro η hη hηone
  let N := ⌈2 / η⌉₊
  have hN : 0 < N := Nat.one_le_ceil_iff.mpr (by positivity)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let l : ℝ := 2 / N
  have hl : 0 < l := by dsimp [l]; positivity
  have hNl : (N : ℝ) * l = 2 := by dsimp [l]; field_simp
  have hle : l ≤ η := by
    have h := (div_le_iff₀ hη).mp (Nat.le_ceil (2 / η))
    exact (div_le_iff₀ hN').mpr (by simpa [mul_comm] using h)
  have hlow : 2 * η / 3 ≤ l := by
    have hceil : (N : ℝ) < 2 / η + 1 := Nat.ceil_lt_add_one (by positivity)
    have hmul : (N : ℝ) * η ≤ 3 := by
      have ht := mul_lt_mul_of_pos_right hceil hη
      rw [add_mul, div_mul_cancel₀ _ hη.ne', one_mul] at ht
      linarith
    apply (le_div_iff₀ hN').2
    linarith [show (2 * η / 3) * (N : ℝ) = (2 / 3) * ((N : ℝ) * η) by ring]
  let K := Fintype.card (Fin 2 → Fin N)
  let e : (Fin 2 → Fin N) ≃ Fin K := Fintype.equivFin _
  let cells := fun k : Fin K => celdaCuadrado l (e.symm k)
  refine ⟨K, cells, fun k => celdaCuadrado_medible _ _, ?_, ?_,
    fun _ => inter_subset_left, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    apply hij
    apply e.symm.injective
    funext k
    apply Fin.ext
    have hx (a : Fin K) (ha : x ∈ cells a) :
        bordeCelda l (e.symm a k) ≤ x k ∧
          x k < bordeCelda l ((e.symm a k).val + 1) :=
      ha.2 k (mem_univ k)
    have hi' := hx i hi
    have hj' := hx j hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hc : (((e.symm i k).val + 1 : ℕ) : ℝ) ≤ (e.symm j k).val := by
        exact_mod_cast (show (e.symm i k).val + 1 ≤ (e.symm j k).val by omega)
      unfold bordeCelda at hi' hj'
      nlinarith [mul_le_mul_of_nonneg_right hc hl.le]
    · have hc : (((e.symm j k).val + 1 : ℕ) : ℝ) ≤ (e.symm i k).val := by
        exact_mod_cast (show (e.symm j k).val + 1 ≤ (e.symm i k).val by omega)
      unfold bordeCelda at hi' hj'
      nlinarith [mul_le_mul_of_nonneg_right hc hl.le]
  · intro x hx
    have hpos (i : Fin 2) : 0 ≤ (x i + 1) / l :=
      div_nonneg (by linarith [(hx i).1]) hl.le
    let k : Fin 2 → Fin N := fun i => ⟨⌊(x i + 1) / l⌋₊,
      (Nat.floor_lt (hpos i)).2 ((div_lt_iff₀ hl).2 (by linarith [(hx i).2]))⟩
    apply Set.mem_iUnion.mpr
    refine ⟨e k, hx, ?_⟩
    intro i _
    rw [e.symm_apply_apply]
    have hlo := (le_div_iff₀ hl).mp (Nat.floor_le (hpos i))
    have hhi := (div_lt_iff₀ hl).mp (Nat.lt_floor_add_one ((x i + 1) / l))
    change bordeCelda l (k i).val ≤ x i ∧ x i < bordeCelda l ((k i).val + 1)
    dsimp [bordeCelda, k]
    push_cast
    exact ⟨by linarith, by linarith⟩
  · intro k
    let a : Fin 2 → ℝ := fun i => bordeCelda l (e.symm k i)
    let b : Fin 2 → ℝ := fun i => bordeCelda l ((e.symm k i).val + 1)
    have hab (i : Fin 2) : b i - a i = l := by dsimp [a, b, bordeCelda]; push_cast; ring
    have hsub : cajaAbierta a b ⊆ cells k := by
      intro x hx
      refine ⟨?_, fun i hi => ⟨(hx i hi).1.le, (hx i hi).2⟩⟩
      intro i
      have ha : -1 ≤ a i := by
        dsimp [a, bordeCelda]
        exact le_add_of_nonneg_right (by positivity)
      have hb : b i ≤ 1 := by
        have hk : (((e.symm k i).val + 1 : ℕ) : ℝ) ≤ N := by
          exact_mod_cast (Nat.succ_le_iff.mpr (e.symm k i).isLt)
        dsimp [b, bordeCelda]
        linarith [mul_le_mul_of_nonneg_right hk hl.le]
      exact ⟨ha.trans_lt (hx i (mem_univ i)).1, (hx i (mem_univ i)).2.trans_le hb⟩
    have hmass : medidaUniformeCuadrado.real (cajaAbierta a b) = (1 / 4) * l ^ 2 := by
      rw [measureReal_def, medidaUniformeCuadrado_apply _ (cajaAbierta_medible a b),
        inter_eq_left.mpr (hsub.trans inter_subset_left), volumen_cajaAbierta,
        Fin.prod_univ_two, hab, hab, ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal hl.le, ← pow_two]
    rw [Real.rpow_two]
    calc
      _ ≤ (1 / 4) * l ^ 2 := by nlinarith [sq_le_sq₀ (by positivity : 0 ≤ 2 * η / 3) hl.le |>.2 hlow]
      _ = _ := hmass.symm
      _ ≤ _ := measureReal_mono hsub
  · intro k x hx y hy
    have hdist (i : Fin 2) : |x i - y i| ≤ l := by
      have hx' : x i ∈ Ico (bordeCelda l (e.symm k i))
          (bordeCelda l ((e.symm k i).val + 1)) := hx.2 i (mem_univ i)
      have hy' : y i ∈ Ico (bordeCelda l (e.symm k i))
          (bordeCelda l ((e.symm k i).val + 1)) := hy.2 i (mem_univ i)
      rw [abs_le]
      dsimp [bordeCelda] at hx' hy'
      push_cast at hx' hy'
      constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
    rw [dist_eq_norm]
    have hnorm : ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
      simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq (x - y)
    have h0 : (x 0 - y 0) ^ 2 ≤ l ^ 2 := by
      rw [← sq_abs (x 0 - y 0)]
      exact (sq_le_sq₀ (abs_nonneg _) hl.le).2 (hdist 0)
    have h1 : (x 1 - y 1) ^ 2 ≤ l ^ 2 := by
      rw [← sq_abs (x 1 - y 1)]
      exact (sq_le_sq₀ (abs_nonneg _) hl.le).2 (hdist 1)
    have hs : ‖x - y‖ ≤ Real.sqrt 2 * l := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
      rw [hnorm, mul_pow, Real.sq_sqrt (by norm_num)]
      linarith
    exact hs.trans (mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _))

#check particiones_uniformes_cuadrado
#check masa_bola_uniforme_cuadrado
#print axioms particiones_uniformes_cuadrado
#print axioms masa_bola_uniforme_cuadrado

end TesisPINN
