import TesisPINN.BaseSenoCuadrado
import TesisPINN.TrazaCuadrado
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! Traza por caras para la medida de longitud del cuadrado. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Set EllipticPdes EllipticPdes.H1Graph
open scoped Topology ENNReal RealInnerProductSpace

abbrev L2Cara := Lp ℝ 2 volumenIntervaloSeno

abbrev L2Caras := Fin 2 × Bool → L2Cara

private instance : IsFiniteMeasure volumenIntervaloSeno := by
  rw [isFiniteMeasure_restrict]
  simp

private theorem masa_intervalo : volumenIntervaloSeno.real univ = 2 := by
  norm_num [Measure.real, Real.volume_Ioo]

private def parCoordenadas : Plano ≃ᵐ (ℝ × ℝ) :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).toMeasurableEquiv.trans
    (MeasurableEquiv.finTwoArrow (α := ℝ))

private def parCara (i : Fin 2) : Plano ≃ᵐ (ℝ × ℝ) :=
  if i = 0 then parCoordenadas else parCoordenadas.trans MeasurableEquiv.prodComm

@[simp] private theorem parCara_fst (i : Fin 2) (x : Plano) : (parCara i x).1 = x i := by
  fin_cases i <;> rfl

private theorem parCara_medida (i : Fin 2) :
    MeasurePreserving (parCara i) volumenPoisson (volumenIntervaloSeno.prod volumenIntervaloSeno) := by
  have he : MeasurePreserving parCoordenadas volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (ι := Fin 2))
  let I := Ioo (-1 : ℝ) 1
  have hs : parCoordenadas ⁻¹' (I ×ˢ I) = cuadrado := by
    ext x
    change ((x 0, x 1) ∈ I ×ˢ I) ↔ _
    simp [I, cuadrado, EllipticPdes.Poincare.euclBox, Fin.forall_fin_two]
  have hm := he.restrict_preimage (measurableSet_Ioo.prod measurableSet_Ioo :
    MeasurableSet (I ×ˢ I))
  rw [hs] at hm
  change MeasurePreserving parCoordenadas volumenPoisson
    (((volume : Measure ℝ).prod volume).restrict (I ×ˢ I)) at hm
  rw [← Measure.prod_restrict] at hm
  fin_cases i
  · exact hm
  · exact Measure.measurePreserving_swap.comp hm

/-- Pesos afines que seleccionan, respectivamente, el extremo negativo y positivo. -/
def pesoTraza (b : Bool) (t : ℝ) : ℝ := if b then (t + 1) / 2 else (t - 1) / 2

def extremoCara (b : Bool) : ℝ := if b then 1 else -1

def puntoCara (i : Fin 2) (b : Bool) (t : ℝ) : Plano :=
  (parCara i).symm (extremoCara b, t)

private theorem pesoTraza_deriv (b : Bool) (t : ℝ) :
    HasDerivAt (pesoTraza b) (1 / 2) t := by
  cases b
  · change HasDerivAt (fun x : ℝ => (x - 1) / 2) _ _
    exact ((hasDerivAt_id t).sub_const 1).div_const 2
  · change HasDerivAt (fun x : ℝ => (x + 1) / 2) _ _
    exact ((hasDerivAt_id t).add_const 1).div_const 2

/-- Fórmula del valor extremo mediante el teorema fundamental del cálculo. -/
theorem extremo_intervalo_de_integral (b : Bool) (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) :
    v (extremoCara b) =
      ∫ t, ((1 / 2 : ℝ) * v t + pesoTraza b t * deriv v t) ∂volumenIntervaloSeno := by
  have hd (t : ℝ) : HasDerivAt (fun y => pesoTraza b y * v y)
      ((1 / 2 : ℝ) * v t + pesoTraza b t * deriv v t) t := by
    exact (pesoTraza_deriv b t).mul ((hv.differentiable (by norm_num) t).hasDerivAt)
  have hc : Continuous (fun t => (1 / 2 : ℝ) * v t + pesoTraza b t * deriv v t) := by
    apply (continuous_const.mul hv.continuous).add
    apply Continuous.mul
    · exact continuous_iff_continuousAt.mpr fun t => (pesoTraza_deriv b t).continuousAt
    · exact hv.continuous_deriv (by norm_num)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => pesoTraza b t * v t) (a := -1) (b := 1)
    (fun t _ => hd t) (hc.intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at h
  cases b <;> norm_num [extremoCara, pesoTraza] at h ⊢ <;> exact h.symm

private theorem pesoTraza_continuo (b : Bool) : Continuous (pesoTraza b) := by
  exact continuous_iff_continuousAt.mpr fun t => (pesoTraza_deriv b t).continuousAt

private theorem pesoTraza_le (b : Bool) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    |pesoTraza b t| ≤ 1 := by
  obtain ⟨hl, hr⟩ := ht
  cases b <;> simp [pesoTraza, abs_le] <;> constructor <;> linarith

private def prolongacionCara (i : Fin 2) (w : ℝ → ℝ) (a : L2Cara) (x : Plano) : ℝ :=
  w (parCara i x).1 * a (parCara i x).2

private theorem prolongacionCara_memLp (i : Fin 2) {w : ℝ → ℝ} (hw : Continuous w)
    (hbound : ∀ t ∈ Ioo (-1 : ℝ) 1, |w t| ≤ 1) (a : L2Cara) :
    MemLp (prolongacionCara i w a) 2 volumenPoisson := by
  change MemLp ((fun z : ℝ × ℝ => w z.1 * a z.2) ∘ parCara i) 2 volumenPoisson
  apply MemLp.comp_measurePreserving _ (parCara_medida i)
  have ha := (Lp.memLp a).comp_snd volumenIntervaloSeno
  apply ha.of_le ((hw.comp continuous_fst).aestronglyMeasurable.mul ha.aestronglyMeasurable)
  have ht := (Measure.quasiMeasurePreserving_fst (ν := volumenIntervaloSeno)).ae
    (ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioo (a := -1) (b := 1)))
  filter_upwards [ht] with x hx
  change |w x.1 * a x.2| ≤ |a x.2|
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hbound x.1 hx) (abs_nonneg (a x.2))

private def prolongacionCaraLineal (i : Fin 2) {w : ℝ → ℝ} (hw : Continuous w)
    (hbound : ∀ t ∈ Ioo (-1 : ℝ) 1, |w t| ≤ 1) : L2Cara →ₗ[ℝ] Lp ℝ 2 volumenPoisson where
  toFun a := (prolongacionCara_memLp i hw hbound a).toLp _
  map_add' a b := by
    apply Lp.ext
    have hae := ((Measure.quasiMeasurePreserving_snd (μ := volumenIntervaloSeno)).comp
      (parCara_medida i).quasiMeasurePreserving).ae (Lp.coeFn_add a b)
    filter_upwards [(prolongacionCara_memLp i hw hbound (a + b)).coeFn_toLp,
      (prolongacionCara_memLp i hw hbound a).coeFn_toLp,
      (prolongacionCara_memLp i hw hbound b).coeFn_toLp,
      Lp.coeFn_add ((prolongacionCara_memLp i hw hbound a).toLp _)
        ((prolongacionCara_memLp i hw hbound b).toLp _), hae] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₄, Pi.add_apply, h₂, h₃]
    unfold prolongacionCara
    dsimp only [Function.comp_def] at h₅
    rw [h₅, Pi.add_apply, mul_add]
  map_smul' c a := by
    apply Lp.ext
    have hae := ((Measure.quasiMeasurePreserving_snd (μ := volumenIntervaloSeno)).comp
      (parCara_medida i).quasiMeasurePreserving).ae (Lp.coeFn_smul c a)
    filter_upwards [(prolongacionCara_memLp i hw hbound (c • a)).coeFn_toLp,
      (prolongacionCara_memLp i hw hbound a).coeFn_toLp,
      Lp.coeFn_smul c ((prolongacionCara_memLp i hw hbound a).toLp _), hae] with x h₁ h₂ h₃ h₄
    rw [RingHom.id_apply, h₁, h₃, Pi.smul_apply, h₂]
    unfold prolongacionCara
    dsimp only [Function.comp_def] at h₄
    rw [h₄, Pi.smul_apply]
    simp only [smul_eq_mul]
    ring

private theorem integral_cuadrado_par (i : Fin 2) (F : ℝ × ℝ → ℝ) :
    (∫ x : Plano, F (parCara i x) ∂volumenPoisson) =
      ∫ z, F z ∂volumenIntervaloSeno.prod volumenIntervaloSeno :=
  (parCara_medida i).integral_comp (parCara i).measurableEmbedding F

private theorem norma_L2_cuadrada {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (z : Lp ℝ 2 μ) : ‖z‖ ^ 2 = ∫ x, (z x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  simp [pow_two]

theorem desigualdad_traza_intervalo (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) :
    |v 1| ^ 2 + |v (-1)| ^ 2 ≤ 8 *
      (∫ t, v t ^ 2 + deriv v t ^ 2 ∂volumenIntervaloSeno) := by
  have hbound (b : Bool) : |v (extremoCara b)| ^ 2 ≤ 4 *
      (∫ t, v t ^ 2 + deriv v t ^ 2 ∂volumenIntervaloSeno) := by
    let a : ℝ → ℝ := fun t => (1 / 2 : ℝ) * v t + pesoTraza b t * deriv v t
    let ν := volumenIntervaloSeno
    have hc : Continuous a := (continuous_const.mul hv.continuous).add
      ((continuous_iff_continuousAt.mpr fun t => (pesoTraza_deriv b t).continuousAt).mul
        (hv.continuous_deriv (by norm_num)))
    have hm (f : ℝ → ℝ) (hf : Continuous f) : MemLp f 2 ν := by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
        hf.continuousOn
      apply MemLp.of_bound hf.aestronglyMeasurable M
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with t ht
      exact hM t (Ioo_subset_Icc_self ht)
    have hma := hm a hc
    have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 ν := memLp_const _
    let A := hma.toLp a
    let B := h1.toLp (fun _ : ℝ => (1 : ℝ))
    have hi : inner ℝ A B = v (extremoCara b) := by
      rw [MeasureTheory.L2.inner_def, extremo_intervalo_de_integral b v hv]
      apply integral_congr_ae
      filter_upwards [hma.coeFn_toLp, h1.coeFn_toLp] with x hx hy
      change A x = _ at hx
      change B x = _ at hy
      rw [hx, hy]
      simp [a]
    have hC := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg B))).mpr
      (abs_real_inner_le_norm A B)
    rw [hi, mul_pow, norma_L2_cuadrada A, norma_L2_cuadrada B] at hC
    have hA : (∫ t, (A t) ^ 2 ∂ν) = ∫ t, (a t) ^ 2 ∂ν :=
      integral_congr_ae (hma.coeFn_toLp.fun_comp (· ^ 2))
    have hB : (∫ t, (B t) ^ 2 ∂ν) = 2 := by
      have hb : (fun t => (B t) ^ 2) =ᵐ[ν] (fun _ => (1 : ℝ)) :=
        h1.coeFn_toLp.mono fun x hx => by
          change B x = 1 at hx
          simp [hx]
      rw [integral_congr_ae hb, integral_const, smul_eq_mul, mul_one]
      exact masa_intervalo
    rw [hA, hB, mul_comm] at hC
    apply hC.trans
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
    rw [← integral_const_mul]
    apply integral_mono_ae hma.integrable_sq
      ((((hm v hv.continuous).integrable_sq).add ((hm _ (hv.continuous_deriv (by norm_num))).integrable_sq)).const_mul 2)
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with t ht
    have hw := pesoTraza_le b ht
    have hws : (pesoTraza b t) ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hw
    dsimp [a]
    nlinarith [sq_nonneg (v t / 2 - pesoTraza b t * deriv v t),
      mul_nonneg (sub_nonneg.mpr hws) (sq_nonneg (deriv v t))]
  have hp := hbound true
  have hn := hbound false
  change |v 1| ^ 2 ≤ _ at hp
  change |v (-1)| ^ 2 ≤ _ at hn
  linarith

private theorem prolongacionCara_norma (i : Fin 2) {w : ℝ → ℝ} (hw : Continuous w)
    (hbound : ∀ t ∈ Ioo (-1 : ℝ) 1, |w t| ≤ 1) (a : L2Cara) :
    ‖prolongacionCaraLineal i hw hbound a‖ ≤ Real.sqrt 2 * ‖a‖ := by
  let c := (prolongacionCara_memLp i hw hbound a).toLp _
  change ‖c‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num), norma_L2_cuadrada c, norma_L2_cuadrada a]
  have hc : (fun x => (c x) ^ 2) =ᵐ[volumenPoisson]
      (fun x => (w (parCara i x).1 * a (parCara i x).2) ^ 2) :=
    (prolongacionCara_memLp i hw hbound a).coeFn_toLp.fun_comp (· ^ 2)
  rw [integral_congr_ae hc, integral_cuadrado_par i
    (fun z => (w z.1 * a z.2) ^ 2)]
  have hleft : Integrable (fun z : ℝ × ℝ => (w z.1 * a z.2) ^ 2)
      (volumenIntervaloSeno.prod volumenIntervaloSeno) := by
    apply ((parCara_medida i).integrable_comp_emb (parCara i).measurableEmbedding).mp
    exact (prolongacionCara_memLp i hw hbound a).integrable_sq
  have hright : Integrable (fun z : ℝ × ℝ => (a z.2) ^ 2)
      (volumenIntervaloSeno.prod volumenIntervaloSeno) :=
    ((Lp.memLp a).comp_snd volumenIntervaloSeno).integrable_sq
  calc
    _ ≤ ∫ z : ℝ × ℝ, (a z.2) ^ 2 ∂volumenIntervaloSeno.prod volumenIntervaloSeno := by
      apply integral_mono_ae hleft hright
      have ht := (Measure.quasiMeasurePreserving_fst (ν := volumenIntervaloSeno)).ae
        (ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioo (a := -1) (b := 1)))
      filter_upwards [ht] with x hx
      have h := (sq_le_sq₀ (abs_nonneg (w x.1)) zero_le_one).mpr (hbound x.1 hx)
      rw [sq_abs] at h
      rw [mul_pow]
      simpa only [one_pow, one_mul] using mul_le_mul_of_nonneg_right h (sq_nonneg (a x.2))
    _ = _ := by
      rw [integral_prod _ hright]
      change (∫ _ : ℝ, (∫ y, (a y) ^ 2 ∂volumenIntervaloSeno) ∂volumenIntervaloSeno) = _
      rw [integral_const, masa_intervalo, smul_eq_mul]

private def prolongacionCaraL (i : Fin 2) {w : ℝ → ℝ} (hw : Continuous w)
    (hbound : ∀ t ∈ Ioo (-1 : ℝ) 1, |w t| ≤ 1) : L2Cara →L[ℝ] Lp ℝ 2 volumenPoisson :=
  (prolongacionCaraLineal i hw hbound).mkContinuous (Real.sqrt 2)
    (prolongacionCara_norma i hw hbound)

private def pesoConstante : ℝ → ℝ := fun _ => 1 / 2

private theorem pesoConstante_le (t : ℝ) (_ : t ∈ Ioo (-1 : ℝ) 1) : |pesoConstante t| ≤ 1 := by
  norm_num [pesoConstante]

private def constanteCaraL (i : Fin 2) : L2Cara →L[ℝ] Lp ℝ 2 volumenPoisson :=
  prolongacionCaraL i continuous_const pesoConstante_le

private def pesoCaraL (i : Fin 2) (b : Bool) : L2Cara →L[ℝ] Lp ℝ 2 volumenPoisson :=
  prolongacionCaraL i (pesoTraza_continuo b) (fun _ => pesoTraza_le b)

private def trazaCaraAmb (i : Fin 2) (b : Bool) :
    H1Graph (volume : Measure Plano) cuadrado →L[ℝ] L2Cara :=
  (constanteCaraL i).adjoint.comp fnL +
    (pesoCaraL i b).adjoint.comp (partialL (EuclideanSpace.single i (1 : ℝ)))

/-- Operador acotado de las cuatro caras. Cada componente usa Lebesgue
unidimensional y la derivada débil en la coordenada normal. -/
def trazaSobolevCuadrado :
    W12 (volume : Measure Plano) cuadrado →L[ℝ] L2Caras :=
  (ContinuousLinearMap.pi (fun ib : Fin 2 × Bool => trazaCaraAmb ib.1 ib.2)).comp
    (W12 (volume : Measure Plano) cuadrado).subtypeL

theorem trazaSobolevCuadrado_acotada :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : W12 (volume : Measure Plano) cuadrado,
      ‖trazaSobolevCuadrado v‖ ≤ C * ‖v‖ :=
  ⟨‖trazaSobolevCuadrado‖, norm_nonneg trazaSobolevCuadrado, trazaSobolevCuadrado.le_opNorm⟩

theorem trazaSobolevCuadrado_norma (v : W12 (volume : Measure Plano) cuadrado) :
    ‖trazaSobolevCuadrado v‖ ≤ (2 * Real.sqrt 2) * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  rintro ⟨i, b⟩
  let w : H1Graph (volume : Measure Plano) cuadrado := v
  let d : Plano := EuclideanSpace.single i 1
  let A := constanteCaraL i
  let B := pesoCaraL i b
  change ‖A.adjoint (fnL w) + B.adjoint (partialL d w)‖ ≤ (2 * Real.sqrt 2) * ‖w‖
  have hA : ‖A.adjoint‖ ≤ Real.sqrt 2 := by
    rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _)
      (prolongacionCara_norma i continuous_const pesoConstante_le)
  have hB : ‖B.adjoint‖ ≤ Real.sqrt 2 := by
    rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _)
      (prolongacionCara_norma i (pesoTraza_continuo b) (fun _ => pesoTraza_le b))
  have hd : ‖d‖ = 1 := EuclideanSpace.orthonormal_single.norm_eq_one i
  have h₁ : ‖A.adjoint (fnL w)‖ ≤ Real.sqrt 2 * ‖w‖ := (A.adjoint.le_opNorm _).trans
    (mul_le_mul hA (norm_fnL_le w) (norm_nonneg _) (Real.sqrt_nonneg _))
  have h₂ : ‖B.adjoint (partialL d w)‖ ≤ Real.sqrt 2 * ‖w‖ := (B.adjoint.le_opNorm _).trans
    (mul_le_mul hB (by simpa only [hd, one_mul] using norm_partialL_le d w)
      (norm_nonneg _) (Real.sqrt_nonneg _))
  exact (norm_add_le _ _).trans (by linarith)

private theorem trazaCara_emparejamiento (i : Fin 2) (b : Bool)
    (v : H1Graph (volume : Measure Plano) cuadrado) (a : L2Cara) :
    inner ℝ a (trazaCaraAmb i b v) =
      ∫ x, a (parCara i x).2 *
        ((1 / 2 : ℝ) * fnL v x + pesoTraza b (x i) *
          partialL (EuclideanSpace.single i (1 : ℝ)) v x) ∂volumenPoisson := by
  let A := constanteCaraL i
  let B := pesoCaraL i b
  let d := partialL (EuclideanSpace.single i (1 : ℝ)) v
  change inner ℝ a (A.adjoint (fnL v) + B.adjoint d) = _
  rw [inner_add_right, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  have ha : ⇑(A a) =ᵐ[volumenPoisson] prolongacionCara i pesoConstante a :=
    (prolongacionCara_memLp i continuous_const pesoConstante_le a).coeFn_toLp
  have hb : ⇑(B a) =ᵐ[volumenPoisson] prolongacionCara i (pesoTraza b) a :=
    (prolongacionCara_memLp i (pesoTraza_continuo b) (fun _ => pesoTraza_le b) a).coeFn_toLp
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_add
    (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (A a) (fnL v))
    (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (B a) d)]
  apply integral_congr_ae
  filter_upwards [ha, hb] with x hx hy
  change inner ℝ ((A a) x) (fnL v x) + inner ℝ ((B a) x) (d x) = _
  rw [hx, hy]
  simp only [RCLike.inner_apply, conj_trivial, prolongacionCara, pesoConstante, parCara_fst]
  ring

private theorem parCara_symm_coord (i : Fin 2) (z : ℝ × ℝ) (j : Fin 2) :
    (parCara i).symm z j = if j = i then z.1 else z.2 := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem seccion_cara_afin (i : Fin 2) (t s : ℝ) :
    (parCara i).symm (t, s) = t • EuclideanSpace.single i 1 + (parCara i).symm (0, s) := by
  apply PiLp.ext
  intro j
  by_cases h : j = i <;>
    simp [parCara_symm_coord, h, PiLp.add_apply, PiLp.smul_apply]

private theorem seccion_cara_suave (i : Fin 2) (s : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => (parCara i).symm (t, s)) := by
  have h : (fun t : ℝ => (parCara i).symm (t, s)) =
      fun t => t • EuclideanSpace.single i 1 + (parCara i).symm (0, s) :=
    funext fun t => seccion_cara_afin i t s
  rw [h]
  fun_prop

private theorem deriv_seccion_cara (i : Fin 2) (v : Plano → ℝ) (hv : ContDiff ℝ 1 v)
    (s t : ℝ) :
    HasDerivAt (fun y => v ((parCara i).symm (y, s)))
      (fderiv ℝ v ((parCara i).symm (t, s)) (EuclideanSpace.single i 1)) t := by
  have hsec : HasDerivAt (fun y => (parCara i).symm (y, s)) (EuclideanSpace.single i 1) t := by
    have h : (fun y : ℝ => (parCara i).symm (y, s)) =
        fun y => y • EuclideanSpace.single i 1 + (parCara i).symm (0, s) :=
      funext fun y => seccion_cara_afin i y s
    rw [h]
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const
      (EuclideanSpace.single i (1 : ℝ) : Plano)).add_const ((parCara i).symm (0, s))
  exact (hv.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hsec

private theorem trazaCara_clasica (i : Fin 2) (b : Bool)
    (v : H1Graph (volume : Measure Plano) cuadrado) (f : Plano → ℝ) (hf : ContDiff ℝ 1 f)
    (hv : ⇑(fnL v) =ᵐ[volumenPoisson] f)
    (hd : ⇑(partialL (EuclideanSpace.single i (1 : ℝ)) v) =ᵐ[volumenPoisson]
      fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) :
    ⇑(trazaCaraAmb i b v) =ᵐ[volumenIntervaloSeno] fun t => f (puntoCara i b t) := by
  have hcont : Continuous (fun t => f (puntoCara i b t)) := by
    have h : Continuous (parCara i).symm := by
      apply (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).isEmbedding.continuous_iff.mpr
      apply continuous_pi
      intro j
      change Continuous (fun z => (parCara i).symm z j)
      simp only [parCara_symm_coord]
      split_ifs
      · exact continuous_fst
      · exact continuous_snd
    exact hf.continuous.comp (h.comp (continuous_const.prodMk continuous_id))
  have hm : MemLp (fun t => f (puntoCara i b t)) 2 volumenIntervaloSeno := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
    apply MemLp.of_bound hcont.aestronglyMeasurable M
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with t ht
    exact hM t (Ioo_subset_Icc_self ht)
  suffices he : trazaCaraAmb i b v = hm.toLp _ by
    rw [he]
    exact hm.coeFn_toLp
  apply ext_inner_left ℝ
  intro a
  rw [trazaCara_emparejamiento, MeasureTheory.L2.inner_def]
  let F : ℝ × ℝ → ℝ := fun z =>
    a z.2 * ((1 / 2 : ℝ) * f ((parCara i).symm z) +
      pesoTraza b z.1 * fderiv ℝ f ((parCara i).symm z) (EuclideanSpace.single i 1))
  have hae : (fun x => a (parCara i x).2 *
        ((1 / 2 : ℝ) * fnL v x + pesoTraza b (x i) *
          partialL (EuclideanSpace.single i (1 : ℝ)) v x)) =ᵐ[volumenPoisson]
        fun x => F (parCara i x) := by
    filter_upwards [hv, hd] with x hx hy
    simp [F, hx, hy]
  rw [integral_congr_ae hae, integral_cuadrado_par i F]
  have hF : Integrable F (volumenIntervaloSeno.prod volumenIntervaloSeno) := by
    apply ((parCara_medida i).integrable_comp_emb (parCara i).measurableEmbedding).mp
    apply Integrable.congr _ hae
    have ha : ⇑(constanteCaraL i a) =ᵐ[volumenPoisson] prolongacionCara i pesoConstante a :=
      (prolongacionCara_memLp i continuous_const pesoConstante_le a).coeFn_toLp
    have hb : ⇑(pesoCaraL i b a) =ᵐ[volumenPoisson] prolongacionCara i (pesoTraza b) a :=
      (prolongacionCara_memLp i (pesoTraza_continuo b) (fun _ => pesoTraza_le b) a).coeFn_toLp
    apply Integrable.congr ((MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (constanteCaraL i a)
      (fnL v)).add (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (pesoCaraL i b a)
        (partialL (EuclideanSpace.single i (1 : ℝ)) v)))
    filter_upwards [ha, hb] with x hx hy
    simp only [Pi.add_apply, hx, hy, RCLike.inner_apply, conj_trivial, prolongacionCara,
      pesoConstante, parCara_fst]
    ring
  rw [integral_prod_symm F hF]
  apply integral_congr_ae
  filter_upwards [hm.coeFn_toLp] with t ht
  rw [ht]
  simp only [RCLike.inner_apply, conj_trivial]
  let g : ℝ → ℝ := fun x => f ((parCara i).symm (x, t))
  have hg : ContDiff ℝ 1 g := hf.comp (seccion_cara_suave i t)
  have he := extremo_intervalo_de_integral b g hg
  have hdg (x : ℝ) : deriv g x = fderiv ℝ f ((parCara i).symm (x, t))
      (EuclideanSpace.single i 1) := (deriv_seccion_cara i f hf t x).deriv
  simp_rw [hdg] at he
  simp only [F, integral_const_mul, ← he, g, puntoCara, mul_comm]

theorem trazaSobolevCuadrado_clasica
    (v : W12 (volume : Measure Plano) cuadrado) (f : Plano → ℝ) (hf : ContDiff ℝ 1 f)
    (hv : ⇑(fnL (v : H1Graph volume cuadrado)) =ᵐ[volumenPoisson] f)
    (hd : ∀ i : Fin 2,
      ⇑(partialL (EuclideanSpace.single i (1 : ℝ)) (v : H1Graph volume cuadrado)) =ᵐ[volumenPoisson]
        fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
    (i : Fin 2) (b : Bool) :
    ⇑(trazaSobolevCuadrado v (i, b)) =ᵐ[volumenIntervaloSeno] fun t => f (puntoCara i b t) :=
  trazaCara_clasica i b v f hf hv (hd i)

theorem trazaSobolevCuadrado_suave (f : CandidatoPoisson) (i : Fin 2) (b : Bool) :
    ⇑(trazaSobolevCuadrado ⟨grafoSuaveCuadrado f, grafoSuaveCuadrado_mem_W12 f⟩ (i, b))
      =ᵐ[volumenIntervaloSeno] fun t => f.val (puntoCara i b t) := by
  let v : W12 (volume : Measure Plano) cuadrado :=
    ⟨grafoSuaveCuadrado f, grafoSuaveCuadrado_mem_W12 f⟩
  have hf : ContDiff ℝ 1 f.val := f.property.of_le (by simp)
  have hd (j : Fin 2) :
      ⇑(partialL (EuclideanSpace.single j (1 : ℝ)) (grafoSuaveCuadrado f)) =ᵐ[volumenPoisson]
        fun x => fderiv ℝ f.val x (EuclideanSpace.single j 1) := by
    filter_upwards [coeFn_partialL (EuclideanSpace.single j (1 : ℝ)) (grafoSuaveCuadrado f),
      grafoSuaveCuadrado_gradL_ae f] with x hx hy
    rw [hx, hy]
    exact EllipticPdes.inner_gradient_right f.val x (EuclideanSpace.single j 1)
  exact trazaSobolevCuadrado_clasica v f.val hf (grafoSuaveCuadrado_fnL_ae f) hd i b

theorem cara_ignora_vertices (f g : ℝ → ℝ)
    (h : EqOn f g (Ioo (-1 : ℝ) 1)) : f =ᵐ[volumenIntervaloSeno] g :=
  (ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo).mono fun _ hx => h hx

private theorem puntoCara_mem_frontier (i : Fin 2) (b : Bool) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) : puntoCara i b t ∈ frontier cuadrado := by
  rw [cuadrado_abierto.frontier_eq]
  constructor
  · rw [clausura_cuadrado]
    intro j
    by_cases hj : j = i
    · cases b <;> simp [puntoCara, parCara_symm_coord, hj, extremoCara]
    · simpa [puntoCara, parCara_symm_coord, hj] using Ioo_subset_Icc_self ht
  · intro h
    have hi := h i
    have hp : puntoCara i b t i = extremoCara b := by
      have hpair := congrArg Prod.fst ((parCara i).apply_symm_apply (extremoCara b, t))
      simpa only [puntoCara, parCara_fst] using hpair
    change puntoCara i b t i ∈ Ioo (-1 : ℝ) 1 at hi
    rw [hp] at hi
    cases b <;> simp [extremoCara] at hi

private theorem trazaCara_test (i : Fin 2) (b : Bool)
    (φ : testFunctions cuadrado) : trazaCaraAmb i b (testGraphₗ volume cuadrado φ) = 0 := by
  have hd : ⇑(partialL (EuclideanSpace.single i (1 : ℝ)) (testGraphₗ volume cuadrado φ))
      =ᵐ[volumenPoisson] fun x => fderiv ℝ (φ : Plano → ℝ) x (EuclideanSpace.single i 1) := by
    rw [partialL_testGraphₗ]
    exact coeFn_partialCls _ _
  have he := trazaCara_clasica i b (testGraphₗ volume cuadrado φ) φ
    (φ.2.1.of_le (by simp)) (coeFn_fnL_testGraphₗ φ) hd
  apply Lp.ext
  filter_upwards [he, Lp.coeFn_zero ℝ 2 volumenIntervaloSeno,
    ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with t ht hzero hti
  rw [ht, hzero]
  exact image_eq_zero_of_notMem_tsupport fun hm =>
    ((cuadrado_abierto.frontier_eq ▸ puntoCara_mem_frontier i b hti) :
      puntoCara i b t ∈ closure cuadrado \ cuadrado).2 (φ.2.2.2 hm)

theorem trazaSobolevCuadrado_cero_de_H01
    (v : W12 (volume : Measure Plano) cuadrado)
    (hv : (v : H1Graph volume cuadrado) ∈ H01 (volume : Measure Plano) cuadrado) :
    trazaSobolevCuadrado v = 0 := by
  funext ib
  change trazaCaraAmb ib.1 ib.2 (v : H1Graph volume cuadrado) = 0
  let A := trazaCaraAmb ib.1 ib.2
  have hclosed : IsClosed {w : H1Graph volume cuadrado | A w = 0} :=
    isClosed_singleton.preimage A.continuous
  exact H01_subset_of_isClosed hclosed (fun φ => trazaCara_test ib.1 ib.2 φ) hv

/-- La norma cuadrática de las cuatro caras es la suma de las cuatro
integrales unidimensionales. -/
theorem trazaSobolevCuadrado_suma_cuadrados (v : W12 (volume : Measure Plano) cuadrado) :
    ∑ ib : Fin 2 × Bool, ‖trazaSobolevCuadrado v ib‖ ^ 2 ≤ 32 * ‖v‖ ^ 2 := by
  have h := trazaSobolevCuadrado_norma v
  have hb : 0 ≤ (2 * Real.sqrt 2) * ‖v‖ := by positivity
  calc
    _ ≤ ∑ _ib : Fin 2 × Bool, ((2 * Real.sqrt 2) * ‖v‖) ^ 2 :=
      Finset.sum_le_sum fun ib _ => (sq_le_sq₀ (norm_nonneg _) hb).mpr
        ((pi_norm_le_iff_of_nonneg hb).mp h ib)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
      norm_num [Fintype.card_prod]
      ring

theorem trazas_iguales_de_diferencia_H01
    (h u : W12 (volume : Measure Plano) cuadrado)
    (he : (h : H1Graph volume cuadrado) - u ∈ H01 (volume : Measure Plano) cuadrado) :
    trazaSobolevCuadrado h = trazaSobolevCuadrado u := by
  have hh := trazaSobolevCuadrado_cero_de_H01 (h - u) he
  rw [map_sub] at hh
  exact sub_eq_zero.mp hh

theorem trazaSobolevCuadrado_tendsto
    {v : ℕ → W12 (volume : Measure Plano) cuadrado} {u : W12 (volume : Measure Plano) cuadrado}
    (h : Filter.Tendsto v Filter.atTop (𝓝 u)) :
    Filter.Tendsto (fun n => trazaSobolevCuadrado (v n)) Filter.atTop (𝓝 (trazaSobolevCuadrado u)) :=
  (trazaSobolevCuadrado.continuous.tendsto u).comp h

theorem trazas_iguales_de_frontera_puntual
    (h u : W12 (volume : Measure Plano) cuadrado) {hc uc : Plano → ℝ}
    (hcont : ContinuousOn hc (closure cuadrado)) (ucont : ContinuousOn uc (closure cuadrado))
    (hrep : ⇑(fnL (h : H1Graph volume cuadrado)) =ᵐ[volumenPoisson] hc)
    (urep : ⇑(fnL (u : H1Graph volume cuadrado)) =ᵐ[volumenPoisson] uc)
    (hfr : EqOn hc uc (frontier cuadrado)) :
    trazaSobolevCuadrado h = trazaSobolevCuadrado u :=
  trazas_iguales_de_diferencia_H01 h u
    (frontera_puntual_igual_implica_error_H01 h u h.property u.property hcont ucont hrep urep hfr)

#check trazaSobolevCuadrado
#print axioms extremo_intervalo_de_integral
#print axioms desigualdad_traza_intervalo
#print axioms trazaSobolevCuadrado
#print axioms trazaSobolevCuadrado_acotada
#print axioms trazaSobolevCuadrado_norma
#print axioms trazaSobolevCuadrado_clasica
#print axioms trazaSobolevCuadrado_suave
#print axioms cara_ignora_vertices
#print axioms trazaSobolevCuadrado_cero_de_H01
#print axioms trazaSobolevCuadrado_suma_cuadrados
#print axioms trazas_iguales_de_diferencia_H01
#print axioms trazaSobolevCuadrado_tendsto
#print axioms trazas_iguales_de_frontera_puntual

end TesisPINN
