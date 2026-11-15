import TesisPINN.ExistenciaMinimizador326
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Selección en los mínimos del funcional interior mediante la norma euclidiana. -/

noncomputable section

namespace TesisPINN

open Set MeasureTheory

theorem laplaciano326_continuo_conjunto (D : ℕ) :
    Continuous (fun z : Coeficientes324 D × Plano => laplaciano326 D z.1 z.2) := by
  let b := Pi.basisFun ℝ (IndiceMonomio D)
  have he (a : Coeficientes324 D) (x : Plano) :
      laplaciano326 D a x = ∑ i, a i * laplaciano326 D (b i) x := by
    have hb : a = ∑ i, a i • b i := by
      simpa only [b, Pi.basisFun_repr] using (b.sum_repr a).symm
    conv_lhs => rw [hb, map_sum, Finset.sum_apply]
    simp [smul_eq_mul]
  rw [show (fun z : Coeficientes324 D × Plano => laplaciano326 D z.1 z.2) =
    (fun z => ∑ i, z.1 i * laplaciano326 D (b i) z.2) from funext fun z => he z.1 z.2]
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp continuous_fst).mul
    ((laplacianoClásico_suave _ (candidato326_suave (b i))).continuous.comp continuous_snd)

theorem funcional326_continuo_conjunto (D m : ℕ) (peso : ℝ) :
    Continuous (fun z : (Fin m → Plano) × Coeficientes324 D =>
      funcional326 z.1 peso z.2) := by
  have hf : Continuous fuenteManufacturada :=
    continuous_const.mul datosPoisson325_regulares.1.continuous
  unfold funcional326 funcionalInterior perdidaEmpiricaInterior
  have hc (i : Fin m) :
      Continuous (fun z : (Fin m → Plano) × Coeficientes324 D =>
        laplaciano326 D z.2 (z.1 i) - fuenteManufacturada (z.1 i)) := by
    have hS : Continuous (fun z : (Fin m → Plano) × Coeficientes324 D => z.1 i) :=
      (continuous_apply i).comp continuous_fst
    exact ((laplaciano326_continuo_conjunto D).comp (continuous_snd.prodMk hS)).sub (hf.comp hS)
  exact ((continuous_finsetSum _ (fun i _ => (hc i).pow 2)).div_const _).add
    (continuous_const.mul (((seminorma326_continua D).comp continuous_snd).pow 2))

private theorem funcional326_punto_medio {D m : ℕ} (s : Fin m → Plano)
    (peso : ℝ) (hp : 0 ≤ peso) (a b : Coeficientes324 D) :
    funcional326 s peso ((1 / 2 : ℝ) • (a + b)) ≤
      (funcional326 s peso a + funcional326 s peso b) / 2 := by
  let L := laplaciano326 D
  let p := seminorma326 D
  have hS : p ((1 / 2 : ℝ) • (a + b)) ≤ (p a + p b) / 2 := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith [map_add_le_add p a b]
  have hp2 : p ((1 / 2 : ℝ) • (a + b)) ^ 2 ≤ (p a ^ 2 + p b ^ 2) / 2 := by
    exact (pow_le_pow_left₀ (apply_nonneg p _) hS 2).trans (by nlinarith [sq_nonneg (p a - p b)])
  have hsum : (∑ i, (L ((1 / 2 : ℝ) • (a + b)) (s i) - fuenteManufacturada (s i)) ^ 2) ≤
      ((∑ i, (L a (s i) - fuenteManufacturada (s i)) ^ 2) +
        (∑ i, (L b (s i) - fuenteManufacturada (s i)) ^ 2)) / 2 := by
    rw [← Finset.sum_add_distrib]
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [map_smul, map_add, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    nlinarith [sq_nonneg (L a (s i) - L b (s i))]
  have hE := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg m)
  change _ / (m : ℝ) + peso * p ((1 / 2 : ℝ) • (a + b)) ^ 2 ≤
    ((_ / (m : ℝ) + peso * p a ^ 2) + (_ / (m : ℝ) + peso * p b ^ 2)) / 2
  refine (add_le_add hE (mul_le_mul_of_nonneg_left hp2 hp)).trans_eq ?_
  ring

private def normaEuclideaCuad326 {D : ℕ} (a : Coeficientes324 D) : ℝ := ∑ i, (a i) ^ 2

private theorem normaEuclideaCuad326_continua (D : ℕ) :
    Continuous (normaEuclideaCuad326 (D := D)) :=
  continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2

private def minimos326 {D m : ℕ} (peso : ℝ) :
    Set ((Fin m → Plano) × Coeficientes324 D) :=
  {z | IsMinOn (funcional326 z.1 peso) univ z.2}

private theorem grafo_minimos_cerrado {S A : Type*} [TopologicalSpace S] [TopologicalSpace A]
    (F : S × A → ℝ) (hF : Continuous F) :
    IsClosed {z : S × A | IsMinOn (fun a => F (z.1, a)) univ z.2} := by
  let C (b : A) : Set (S × A) := {z | F z ≤ F (z.1, b)}
  have he : {z : S × A | IsMinOn (fun a => F (z.1, a)) univ z.2} = ⋂ b, C b := by
    ext z
    rw [mem_iInter]
    change IsMinOn (fun a => F (z.1, a)) univ z.2 ↔ ∀ b : A, F z ≤ F (z.1, b)
    exact ⟨fun h b => h (mem_univ b), fun h b _ => h b⟩
  rw [he]
  exact isClosed_iInter fun b => isClosed_le hF (hF.comp (continuous_fst.prodMk continuous_const))

private theorem minimos326_cerrado (D m : ℕ) (peso : ℝ) :
    IsClosed (minimos326 (D := D) (m := m) peso) :=
  grafo_minimos_cerrado (fun z : (Fin m → Plano) × Coeficientes324 D =>
    funcional326 z.1 peso z.2) (funcional326_continuo_conjunto D m peso)


private def menorNorma326 {D m : ℕ} (peso : ℝ) (s : Fin m → Plano) (a : Coeficientes324 D) : Prop :=
  (s, a) ∈ minimos326 peso ∧
    ∀ b : Coeficientes324 D, (s, b) ∈ minimos326 peso → normaEuclideaCuad326 a ≤ normaEuclideaCuad326 b

private theorem unico_menorNorma326 {D m : ℕ} (s : Fin m → Plano) (peso : ℝ)
    (hp : 0 < peso) :
    ∃! a : Coeficientes324 D, menorNorma326 peso s a := by
  obtain ⟨a₀, ha₀⟩ := existe_minimizador326 (D := D) s peso hp
  have hclosed : IsClosed {b : Coeficientes324 D | (s, b) ∈ minimos326 peso} :=
    (minimos326_cerrado D m peso).preimage (continuous_const.prodMk continuous_id)
  have hcompact : IsCompact {b : Coeficientes324 D | (s, b) ∈ minimos326 peso} :=
    (subnivel326_compacto s peso hp (funcional326 s peso a₀)).of_isClosed_subset hclosed
      (fun b hb => hb (mem_univ a₀))
  obtain ⟨a, ha, hmin⟩ := hcompact.exists_isMinOn ⟨a₀, ha₀⟩
    (normaEuclideaCuad326_continua D).continuousOn
  refine ⟨a, ⟨ha, fun _ hb => hmin hb⟩, fun b hb => ?_⟩
  let c := (1 / 2 : ℝ) • (a + b)
  have hma : IsMinOn (funcional326 s peso) univ a := ha
  have hmb : IsMinOn (funcional326 s peso) univ b := hb.1
  have hab : funcional326 s peso a ≤ funcional326 s peso b := hma (mem_univ b)
  have hba : funcional326 s peso b ≤ funcional326 s peso a := hmb (mem_univ a)
  have hc : (s, c) ∈ minimos326 peso := by
    intro v _
    change funcional326 s peso c ≤ funcional326 s peso v
    have hv : funcional326 s peso a ≤ funcional326 s peso v := hma (mem_univ v)
    exact (funcional326_punto_medio s peso hp.le a b).trans (by linarith only [hba, hv])
  have hn : normaEuclideaCuad326 a ≤ normaEuclideaCuad326 c := hmin hc
  have hn' := hb.2 a ha
  have he : normaEuclideaCuad326 c = (normaEuclideaCuad326 a + normaEuclideaCuad326 b) / 2 -
      (∑ i, (a i - b i) ^ 2) / 4 := by
    unfold normaEuclideaCuad326
    rw [← Finset.sum_add_distrib]
    simp only [div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [c, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    ring
  have hsum : (∑ i, (a i - b i) ^ 2) ≤ 0 := by linarith
  funext i
  have hi : (a i - b i) ^ 2 ≤ ∑ j, (a j - b j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (a j - b j)) (Finset.mem_univ i)
  have hz : a i - b i = 0 := (sq_nonpos_iff (a i - b i)).mp (hi.trans hsum)
  linarith

private theorem subnivelNormaEuclidea326_compacto (D : ℕ) (t : ℝ) :
    IsCompact {a : Coeficientes324 D | normaEuclideaCuad326 a ≤ t} := by
  refine (isCompact_closedBall (0 : Coeficientes324 D) (Real.sqrt t)).of_isClosed_subset
    (isClosed_le (normaEuclideaCuad326_continua D) continuous_const) ?_
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  have hi : (a i) ^ 2 ≤ normaEuclideaCuad326 a :=
    Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
  have ht : 0 ≤ t := (sq_nonneg (a i)).trans (hi.trans ha)
  apply (Real.le_sqrt (norm_nonneg _) ht).mpr
  simpa [Real.norm_eq_abs, sq_abs] using hi.trans ha

/-- El minimizador de menor norma euclídea se selecciona mediante un grafo
boreliano. El criterio de desempate se aplica dentro del conjunto de mínimos. -/
theorem existe_minimizador_borel326 (D m : ℕ) (peso : ℝ) (hp : 0 < peso) :
    ∃ a : (Fin m → Plano) → Coeficientes324 D, Measurable a ∧
      ∀ s, IsMinOn (funcional326 s peso) univ (a s) := by
  classical
  have hUnique (s : Fin m → Plano) := unico_menorNorma326 (D := D) s peso hp
  choose a ha huniq using hUnique
  let v (s : Fin m → Plano) := normaEuclideaCuad326 (a s)
  have hvl : LowerSemicontinuous v := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro t
    let C := {a : Coeficientes324 D | normaEuclideaCuad326 a ≤ t}
    let : CompactSpace C := isCompact_iff_compactSpace.mp (subnivelNormaEuclidea326_compacto D t)
    let G : Set ((Fin m → Plano) × C) :=
      (fun z => (z.1, (z.2 : Coeficientes324 D))) ⁻¹' minimos326 peso
    have hG : IsClosed G := (minimos326_cerrado D m peso).preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    have he : v ⁻¹' Iic t = Prod.fst '' G := by
      ext s
      constructor
      · intro hs
        exact ⟨(s, ⟨a s, hs⟩), (ha s).1, rfl⟩
      · rintro ⟨⟨s', b⟩, hb, rfl⟩
        exact ((ha s').2 b hb).trans b.property
    rw [he]
    exact isClosedMap_fst_of_compactSpace _ hG
  let B : Set ((Fin m → Plano) × Coeficientes324 D) :=
    minimos326 peso ∩ {z | normaEuclideaCuad326 z.2 = v z.1}
  have hB : MeasurableSet B := (minimos326_cerrado D m peso).measurableSet.inter
    (measurableSet_eq_fun ((normaEuclideaCuad326_continua D).measurable.comp measurable_snd)
      (hvl.measurable.comp measurable_fst))
  have hmem (s : Fin m → Plano) : (s, a s) ∈ B := ⟨(ha s).1, rfl⟩
  let f (z : B) : Fin m → Plano := z.1.1
  have hcoord (z : B) : z.1.2 = a (f z) := by
    apply huniq (f z)
    exact ⟨z.property.1, fun b hb => z.property.2.le.trans ((ha (f z)).2 b hb)⟩
  let : StandardBorelSpace B := hB.standardBorel
  have hEmbed : MeasurableEmbedding f := by
    apply (measurable_fst.comp measurable_subtype_coe).measurableEmbedding
    intro x y hxy
    apply Subtype.ext
    exact Prod.ext hxy ((hcoord x).trans ((congrArg a (show f x = f y from hxy)).trans (hcoord y).symm))
  let : Nonempty B := ⟨⟨(fun _ => 0, a (fun _ => 0)), hmem _⟩⟩
  have hMeas : Measurable a := by
    have hA (s : Fin m → Plano) : a s = (hEmbed.invFun s).1.2 := by
      exact (congrArg (fun z : B => z.1.2)
        (hEmbed.leftInverse_invFun ⟨(s, a s), hmem s⟩)).symm
    rw [funext hA]
    exact (measurable_snd.comp measurable_subtype_coe).comp hEmbed.measurable_invFun
  exact ⟨a, hMeas, fun s => (ha s).1⟩

#check existe_minimizador_borel326
#print axioms existe_minimizador_borel326


end TesisPINN

