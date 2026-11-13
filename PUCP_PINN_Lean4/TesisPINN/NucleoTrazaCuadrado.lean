import TesisPINN.TrazaSobolevCuadrado
import EllipticPdes.Analysis.Dilation
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Integración por partes para las derivadas débiles en el cuadrado. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Set Filter EllipticPdes EllipticPdes.H1Graph
open scoped Topology ENNReal RealInnerProductSpace

local notation "D[" i "]" => EuclideanSpace.single i (1 : ℝ)

private instance : IsFiniteMeasure volumenPoisson :=
  isFiniteMeasure_restrict.mpr cuadrado_acotado.measure_lt_top.ne

private theorem deriv_perfil_cero {δ t : ℝ} (hδ : 0 < δ)
    (hl : -1 + 2 * δ < t) (hr : t < 1 - 2 * δ) : deriv (perfil δ) t = 0 := by
  have heq : perfil δ =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds hl hr] with s hs
    have hleft : 2 * δ ≤ s + 1 := by linarith [hs.1]
    have hright : 2 * δ ≤ -s + 1 := by linarith [hs.2]
    simp [perfil, lado_uno hδ hleft, lado_uno hδ hright]
  simpa using heq.deriv_eq

private theorem abs_deriv_recorte_normal_le {δ C : ℝ} (hδ : 0 < δ)
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) (i : Fin 2) (x : Plano) :
    |fderiv ℝ (recorte δ) x D[i]| ≤ 2 * C / δ := by
  have h := abs_fderiv_recorte_le hδ hC x D[i]
  fin_cases i <;> simpa [EuclideanSpace.single] using h

private theorem fderiv_recorte_normal_cero {δ : ℝ} (hδ : 0 < δ)
    (i : Fin 2) (x : Plano) (hl : -1 + 2 * δ < x i) (hr : x i < 1 - 2 * δ) :
    fderiv ℝ (recorte δ) x D[i] = 0 := by
  have hz := deriv_perfil_cero hδ hl hr
  fin_cases i <;>
    simp_all [fderiv_recorte_formula, EuclideanSpace.single]

private theorem resto_cota_cara (i : Fin 2) {φ : Plano → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hz : ∀ b t, φ (puntoCara i b t) = 0) {M : ℝ}
    (hM : ∀ x ∈ closure cuadrado, ‖fderiv ℝ φ x D[i]‖ ≤ M)
    (b : Bool) {x : Plano} (hx : x ∈ cuadrado) :
    ‖φ x‖ ≤ M * |x i - extremoCara b| := by
  let s := (parCara i x).2
  let g : ℝ → ℝ := fun t => φ ((parCara i).symm (t, s))
  have hix : x i ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self (hx i)
  have hbx : extremoCara b ∈ Icc (-1 : ℝ) 1 := by cases b <;> norm_num [extremoCara]
  have hs : s ∈ Icc (-1 : ℝ) 1 := by
    fin_cases i
    · exact Ioo_subset_Icc_self (hx 1)
    · exact Ioo_subset_Icc_self (hx 0)
  have hbox (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      (parCara i).symm (t, s) ∈ closure cuadrado := by
    rw [clausura_cuadrado]
    intro j
    by_cases hj : j = i
    · simpa [parCara_symm_coord, hj] using ht
    · simpa [parCara_symm_coord, hj] using hs
  have hg (t : ℝ) := deriv_seccion_cara i φ hφ s t
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hg t).differentiableAt)
    (fun t ht => by rw [(hg t).deriv]; exact hM _ (hbox t ht))
    (convex_Icc (-1 : ℝ) 1) hbx hix
  have hEq : g (x i) = φ x := by
    dsimp [g, s]
    rw [← parCara_fst i x]
    exact congrArg φ ((parCara i).symm_apply_apply x)
  change ‖g (x i) - g (extremoCara b)‖ ≤ M * ‖x i - extremoCara b‖ at h
  rw [hEq, show g (extremoCara b) = 0 from hz b s, sub_zero, Real.norm_eq_abs] at h
  exact h

private theorem corte_resto_cota (i : Fin 2) {φ : Plano → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hz : ∀ b t, φ (puntoCara i b t) = 0) {M C δ : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ closure cuadrado, ‖fderiv ℝ φ x D[i]‖ ≤ M)
    (hC : ∀ t, |deriv Real.smoothTransition t| ≤ C) (hδ : 0 < δ)
    {x : Plano} (hx : x ∈ cuadrado) :
    ‖fderiv ℝ (recorte δ) x D[i] * φ x‖ ≤ 4 * C * M := by
  have hC0 := (abs_nonneg _).trans (hC 0)
  by_cases hl : -1 + 2 * δ < x i
  · by_cases hr : x i < 1 - 2 * δ
    · rw [fderiv_recorte_normal_cero hδ i x hl hr, zero_mul, norm_zero]
      positivity
    · have hb := resto_cota_cara i hφ hz hM true hx
      change ‖φ x‖ ≤ M * |x i - 1| at hb
      rw [abs_of_nonpos (sub_nonpos.mpr (hx i).2.le)] at hb
      rw [norm_mul, Real.norm_eq_abs (fderiv ℝ (recorte δ) x D[i])]
      calc
        _ ≤ (2 * C / δ) * (M * (2 * δ)) := by
          gcongr
          · exact abs_deriv_recorte_normal_le hδ hC i x
          · exact hb.trans (mul_le_mul_of_nonneg_left (by linarith [le_of_not_gt hr]) hM0)
        _ = _ := by field_simp; ring
  · have hb := resto_cota_cara i hφ hz hM false hx
    change ‖φ x‖ ≤ M * |x i - (-1)| at hb
    rw [abs_of_nonneg (sub_nonneg.mpr (hx i).1.le)] at hb
    rw [norm_mul, Real.norm_eq_abs (fderiv ℝ (recorte δ) x D[i])]
    calc
      _ ≤ (2 * C / δ) * (M * (2 * δ)) := by
        gcongr
        · exact abs_deriv_recorte_normal_le hδ hC i x
        · exact hb.trans (mul_le_mul_of_nonneg_left (by linarith [le_of_not_gt hl]) hM0)
      _ = _ := by field_simp; ring

private theorem integral_resto_cero (v : W12 (volume : Measure Plano) cuadrado)
    (i : Fin 2) {φ : Plano → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hz : ∀ b t, φ (puntoCara i b t) = 0) :
    (∫ x, fderiv ℝ φ x D[i] * fnL (v : H1Graph volume cuadrado) x +
      φ x * partialL D[i] (v : H1Graph volume cuadrado) x ∂volumenPoisson) = 0 := by
  let u : H1Graph (volume : Measure Plano) cuadrado := v
  let a : Plano → ℝ := fnL u
  let g : Plano → ℝ := partialL D[i] u
  let φn (n : ℕ) : Plano → ℝ := fun x => recorte (ancho n) x * φ x
  let F (p : Plano → ℝ) (x : Plano) := fderiv ℝ p x D[i] * a x + p x * g x
  have hφn (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (φn n) := (recorte_suave _).mul hφ
  have hnorm (p : Plano → ℝ) (hp : ContDiff ℝ (⊤ : ℕ∞) p) :
      Continuous (fun x => fderiv ℝ p x D[i]) :=
    (hp.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨M, hM⟩ := cuadrado_acotado.isCompact_closure.exists_bound_of_continuousOn
    (hnorm φ hφ).continuousOn
  obtain ⟨B, hB⟩ := cuadrado_acotado.isCompact_closure.exists_bound_of_continuousOn
    hφ.continuous.continuousOn
  obtain ⟨C, hC0, hC⟩ := EllipticPdes.Extension.exists_bound_deriv_smoothTransition
  have hM0 := (norm_nonneg _).trans (hM 0 (subset_closure (by
    intro j
    change (0 : ℝ) ∈ Ioo (-1) 1
    norm_num)))
  have hU := ae_restrict_mem (μ := (volume : Measure Plano)) cuadrado_abierto.measurableSet
  have hweak := ((mem_W12_iff_hasWeakFDerivOn cuadrado_abierto u).mp v.property) D[i]
  have hprod (n : ℕ) (x : Plano) : fderiv ℝ (φn n) x D[i] =
      fderiv ℝ (recorte (ancho n)) x D[i] * φ x +
        recorte (ancho n) x * fderiv ℝ φ x D[i] := by
    change fderiv ℝ (fun y => recorte (ancho n) y * φ y) x D[i] = _
    rw [fderiv_fun_mul ((recorte_suave _).differentiable (by simp) x)
      (hφ.differentiable (by simp) x)]
    simp [mul_comm, add_comm]
  have hc (n : ℕ) (x : Plano) : ‖recorte (ancho n) x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (recorte_no_neg _ _)]
    exact recorte_le_uno _ _
  have hdBound (n : ℕ) (x : Plano) (hx : x ∈ cuadrado) :
      ‖fderiv ℝ (φn n) x D[i]‖ ≤ 4 * C * M + M := by
    rw [hprod]
    refine (norm_add_le _ _).trans (add_le_add
      (corte_resto_cota i (hφ.of_le (by simp)) hz hM0 hM hC (ancho_pos n) hx) ?_)
    rw [norm_mul]
    exact (mul_le_mul (hc n x) (hM x (subset_closure hx)) (norm_nonneg _) zero_le_one).trans
      (by rw [one_mul])
  have hvBound (n : ℕ) (x : Plano) (hx : x ∈ cuadrado) : ‖φn n x‖ ≤ B := by
    rw [show φn n x = recorte (ancho n) x * φ x from rfl, norm_mul]
    simpa only [one_mul] using
      mul_le_mul (hc n x) (hB x (subset_closure hx)) (norm_nonneg _) zero_le_one
  have haI : Integrable a volumenPoisson := (Lp.memLp (fnL u)).integrable (by norm_num)
  have hgI : Integrable g volumenPoisson := (Lp.memLp (partialL D[i] u)).integrable (by norm_num)
  have hzero (n : ℕ) : ∫ x, F (φn n) x ∂volumenPoisson = 0 := by
    have hs : tsupport (φn n) ⊆ cuadrado :=
      (tsupport_mul_subset_left (f := recorte (ancho n)) (g := φ)).trans
        ((recorte_soporte_interior (ancho_pos n)).trans
          (cuadradoInteriorCerrado_sub_cuadrado (ancho_pos n)))
    have hw := hweak.integral_eq (hφn n) (recorte_soporte_compacto (ancho_pos n)).mul_right hs
    have hDa : Integrable (fun x => fderiv ℝ (φn n) x D[i] * a x) volumenPoisson :=
      haI.bdd_mul (hnorm _ (hφn n)).aestronglyMeasurable (hU.mono (hdBound n))
    have hvg : Integrable (fun x => φn n x * g x) volumenPoisson :=
      hgI.bdd_mul (hφn n).continuous.aestronglyMeasurable (hU.mono (hvBound n))
    have hfirst : (∫ x, fderiv ℝ (φn n) x D[i] * a x ∂volumenPoisson) =
        ∫ x, fderiv ℝ (φn n) x D[i] • fnL u x ∂(volume : Measure Plano) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [fderiv_of_notMem_tsupport ℝ (fun hm => hx (hs hm))]
        simp)
    have hsecond : (∫ x, φn n x * g x ∂volumenPoisson) =
        ∫ x, φn n x • innerSL ℝ (gradL u x) D[i] ∂(volume : Measure Plano) := by
      calc
        _ = ∫ x, φn n x • innerSL ℝ (gradL u x) D[i] ∂volumenPoisson := by
          apply integral_congr_ae
          filter_upwards [coeFn_partialL D[i] u] with x hx
          simp [g, hx, real_inner_comm]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hs hm)), zero_smul])
    rw [show F (φn n) = _ from rfl, integral_add hDa hvg, hfirst, hsecond]
    exact add_eq_zero_iff_eq_neg.mpr hw
  have hlim : Tendsto (fun n => ∫ x, F (φn n) x ∂volumenPoisson)
      atTop (𝓝 (∫ x, F φ x ∂volumenPoisson)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => (4 * C * M + M) * ‖a x‖ + B * ‖g x‖)
      (fun n => ((hnorm _ (hφn n)).aestronglyMeasurable.mul haI.aestronglyMeasurable).add
        ((hφn n).continuous.aestronglyMeasurable.mul hgI.aestronglyMeasurable))
      ((haI.norm.const_mul _).add (hgI.norm.const_mul _)) ?_ ?_
    · intro n
      filter_upwards [hU] with x hx
      exact (norm_add_le _ _).trans (add_le_add
        (by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hdBound n x hx) (norm_nonneg _))
        (by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hvBound n x hx) (norm_nonneg _)))
    · filter_upwards [hU] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [eventualmente_recorte_valor_y_derivada hx] with n hn
      simp [F, hprod, φn, hn.1, hn.2]
  exact tendsto_nhds_unique hlim (by simpa only [hzero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

private theorem continuo_acotado_cuadrado {F : Type*} [NormedAddCommGroup F]
    {p : Plano → F} (hp : Continuous p) :
    ∃ M, ∀ᵐ x ∂volumenPoisson, ‖p x‖ ≤ M := by
  obtain ⟨M, hM⟩ := cuadrado_acotado.isCompact_closure.exists_bound_of_continuousOn hp.continuousOn
  exact ⟨M, (ae_restrict_mem cuadrado_abierto.measurableSet).mono
    (fun _ hx => hM _ (subset_closure hx))⟩

private theorem integral_debil_aditivo (v : H1Graph (volume : Measure Plano) cuadrado)
    (i : Fin 2) (p q : Plano → ℝ) (hp : ContDiff ℝ 1 p) (hq : ContDiff ℝ 1 q) :
    (∫ x, fderiv ℝ (fun y => p y + q y) x D[i] * fnL v x +
        (p x + q x) * partialL D[i] v x ∂volumenPoisson) =
      (∫ x, fderiv ℝ p x D[i] * fnL v x + p x * partialL D[i] v x ∂volumenPoisson) +
      (∫ x, fderiv ℝ q x D[i] * fnL v x + q x * partialL D[i] v x ∂volumenPoisson) := by
  have hint (r : Plano → ℝ) (hr : ContDiff ℝ 1 r) : Integrable
      (fun x => fderiv ℝ r x D[i] * fnL v x + r x * partialL D[i] v x) volumenPoisson := by
    have hd : Continuous (fun x => fderiv ℝ r x D[i]) :=
      (hr.continuous_fderiv (by norm_num)).clm_apply continuous_const
    obtain ⟨_, hb⟩ := continuo_acotado_cuadrado hd
    obtain ⟨_, hb'⟩ := continuo_acotado_cuadrado hr.continuous
    exact (((Lp.memLp (fnL v)).integrable (by norm_num)).bdd_mul
      hd.aestronglyMeasurable hb).add
      (((Lp.memLp (partialL D[i] v)).integrable (by norm_num)).bdd_mul
        hr.continuous.aestronglyMeasurable hb')
  rw [← integral_add (hint p hp) (hint q hq)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [fderiv_fun_add (hp.differentiable (by norm_num) x) (hq.differentiable (by norm_num) x)]
  simp only [ContinuousLinearMap.add_apply]
  ring

private theorem parCara_segunda (i : Fin 2) :
    ∃ j : Fin 2, j ≠ i ∧ ∀ x : Plano, (parCara i x).2 = x j := by
  fin_cases i
  · exact ⟨1, by decide, fun _ => rfl⟩
  · exact ⟨0, by decide, fun _ => rfl⟩

private theorem cara_dato_memLp {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp f 2 volumenIntervaloSeno := by
  letI : IsFiniteMeasure volumenIntervaloSeno := isFiniteMeasure_restrict.mpr (by
    simp [volumenIntervaloSeno])
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable M
    ((ae_restrict_mem measurableSet_Ioo).mono (fun t ht => hM t (Ioo_subset_Icc_self ht)))

private theorem cara_mapa_suave (i : Fin 2) (b : Bool) :
    ContDiff ℝ (⊤ : ℕ∞) (puntoCara i b) := by
  have h (j : Fin 2) :
      ContDiff ℝ (⊤ : ℕ∞) (fun t => (puntoCara i b t) j) := by
    simp only [puntoCara, parCara_symm_coord]
    split_ifs
    · exact contDiff_const
    · exact contDiff_id
  exact (contDiff_piLp 2).mpr h

private def afinCara (i : Fin 2) (b : Bool) (f : ℝ → ℝ) (x : Plano) : ℝ :=
  pesoTraza b (x i) * f (parCara i x).2

private theorem afinCara_suave (i : Fin 2) (b : Bool) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (afinCara i b f) := by
  obtain ⟨j, _, hj⟩ := parCara_segunda i
  have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plano => x j) :=
    (EuclideanSpace.proj j : Plano →L[ℝ] ℝ).contDiff
  have he : afinCara i b f = fun x => pesoTraza b (x i) * f (x j) := by
    funext x
    rw [afinCara, hj x]
  rw [he]
  apply ContDiff.mul _ (hf.comp hproj)
  cases b <;> simp only [pesoTraza, Bool.false_eq_true, if_false, if_true] <;> fun_prop

private theorem afinCara_deriv (i : Fin 2) (b : Bool) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Plano) :
    fderiv ℝ (afinCara i b f) x D[i] = (1 / 2 : ℝ) * f (parCara i x).2 := by
  obtain ⟨j, hji, hj⟩ := parCara_segunda i
  let P (j : Fin 2) : Plano →L[ℝ] ℝ := EuclideanSpace.proj j
  have ha (a : ℝ) : HasFDerivAt (fun y : Plano => (y i + a) / 2)
      ((1 / 2 : ℝ) • P i) x := by
    convert (((P i).hasFDerivAt.add_const a).const_smul (1 / 2 : ℝ)) using 1
    funext y
    change (y i + a) / 2 = (1 / 2 : ℝ) * (y i + a)
    ring
  have hp : HasFDerivAt (fun y : Plano => pesoTraza b (y i))
      ((1 / 2 : ℝ) • P i) x := by
    cases b
    · simpa only [pesoTraza, Bool.false_eq_true, if_false, sub_eq_add_neg] using ha (-1)
    · exact ha 1
  have hq := ((hf.differentiable (by simp) (x j)).hasDerivAt).comp_hasFDerivAt x
    (P j).hasFDerivAt
  have he := congrArg (fun A : Plano →L[ℝ] ℝ => A D[i]) (hp.mul hq).fderiv
  have heq : afinCara i b f = fun y => pesoTraza b (y i) * f (P j y) := by
    funext y
    rw [afinCara, hj y]
    rfl
  rw [heq]
  change (fderiv ℝ (fun y => pesoTraza b (y i) * f (P j y)) x) D[i] = _ at he
  simpa [P, hj x, EuclideanSpace.single, PiLp.single_apply, hji, Ne.symm hji, mul_comm] using he

private theorem afinCara_emparejamiento
    (v : W12 (volume : Measure Plano) cuadrado) (i : Fin 2) (b : Bool)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    let u : H1Graph (volume : Measure Plano) cuadrado := v
    (∫ x, fderiv ℝ (afinCara i b f) x D[i] * fnL u x +
      afinCara i b f x * partialL D[i] u x ∂volumenPoisson) =
      ∫ t, trazaSobolevCuadrado v (i, b) t * f t ∂volumenIntervaloSeno := by
  dsimp only
  let a : L2Cara := (cara_dato_memLp hf.continuous).toLp f
  have ha : ⇑a =ᵐ[volumenIntervaloSeno] f := (cara_dato_memLp hf.continuous).coeFn_toLp
  have hμ := (Measure.quasiMeasurePreserving_snd (μ := volumenIntervaloSeno)).comp
    (parCara_medida i).quasiMeasurePreserving
  have hae := hμ.ae_eq_comp ha
  calc
    _ = inner ℝ a (trazaSobolevCuadrado v (i, b)) := by
      rw [trazaSobolevCuadrado_emparejamiento]
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [afinCara_deriv i b hf, afinCara]
      change a (parCara i x).2 = f (parCara i x).2 at hx
      rw [hx]
      ring
    _ = _ := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [ha] with t ht
      simp [ht]

set_option maxHeartbeats 800000 in
/-- Integración por partes con las trazas de las dos caras normales a la dirección `i`. -/
theorem integral_partes_traza_cuadrado
    (v : W12 (volume : Measure Plano) cuadrado) (i : Fin 2) (φ : Plano → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    let u : H1Graph (volume : Measure Plano) cuadrado := v
    (∫ x, fderiv ℝ φ x D[i] * fnL u x + φ x * partialL D[i] u x ∂volumenPoisson) =
      (∫ t, trazaSobolevCuadrado v (i, true) t * φ (puntoCara i true t) ∂volumenIntervaloSeno) -
      (∫ t, trazaSobolevCuadrado v (i, false) t * φ (puntoCara i false t) ∂volumenIntervaloSeno) := by
  dsimp only
  let f (b : Bool) : ℝ → ℝ := fun t => φ (puntoCara i b t)
  have hf (b : Bool) : ContDiff ℝ (⊤ : ℕ∞) (f b) := hφ.comp (cara_mapa_suave i b)
  let p := afinCara i true (f true)
  let q := afinCara i false (fun t => -f false t)
  let R : Plano → ℝ := fun x => φ x - (p x + q x)
  have hp : ContDiff ℝ (⊤ : ℕ∞) p := afinCara_suave i true (hf true)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := afinCara_suave i false (hf false).neg
  have hR := hφ.sub (hp.add hq)
  have hzero (b : Bool) (t : ℝ) : R (puntoCara i b t) = 0 := by
    have ht := (parCara i).apply_symm_apply (extremoCara b, t)
    have hx := (parCara_fst i (puntoCara i b t)).symm.trans (congrArg Prod.fst ht)
    have hs := congrArg Prod.snd ht
    change (parCara i (puntoCara i b t)).2 = t at hs
    cases b <;> simp [R, p, q, afinCara, hx, hs, f, pesoTraza, extremoCara] <;> ring
  have he : φ = fun x => (p x + q x) + R x := by
    funext x
    dsimp [R]
    ring
  conv_lhs => rw [he]
  rw [integral_debil_aditivo _ i _ _ ((hp.add hq).of_le (by simp)) (hR.of_le (by simp)),
    integral_debil_aditivo _ i _ _ (hp.of_le (by simp)) (hq.of_le (by simp)),
    integral_resto_cero v i hR hzero, add_zero,
    afinCara_emparejamiento v i true (hf true)]
  dsimp only [q]
  rw [
    afinCara_emparejamiento v i false (hf false).neg]
  simp only [Pi.neg_apply, mul_neg, integral_neg, sub_eq_add_neg, f]

private theorem extension_memLp {F : Type*} [NormedAddCommGroup F] {f : Plano → F}
    (hf : MemLp f 2 volumenPoisson) :
    MemLp (cuadrado.indicator f) 2 (volume : Measure Plano) :=
  (memLp_indicator_iff_restrict cuadrado_abierto.measurableSet.nullMeasurableSet).mpr hf

set_option maxHeartbeats 800000 in
/-- La prolongación por cero de un elemento de traza nula tiene como
gradiente débil la prolongación por cero de su gradiente. -/
theorem extension_cero_traza_nula
    (v : W12 (volume : Measure Plano) cuadrado) (hv : trazaSobolevCuadrado v = 0) :
    let u : H1Graph (volume : Measure Plano) cuadrado := v
    HasWeakFDerivOn ⊤ (cuadrado.indicator (fnL u))
      (fun x => innerSL ℝ (cuadrado.indicator (gradL u) x)) volume := by
  dsimp only
  let u : H1Graph (volume : Measure Plano) cuadrado := v
  let a := cuadrado.indicator (fnL u : Plano → ℝ)
  let g := cuadrado.indicator (gradL u : Plano → Plano)
  have ha := extension_memLp (Lp.memLp (fnL u))
  have hg := extension_memLp (Lp.memLp (gradL u))
  have hal : LocallyIntegrableOn a univ (volume : Measure Plano) :=
    (ha.locallyIntegrable (by norm_num)).locallyIntegrableOn univ
  apply (hasWeakFDerivOn_iff_basis (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    hal).mpr
  intro i
  have hb : (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i = D[i] := by
    rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  rw [hb, hasWeakLineDerivOn_iff]
  have hg' : MemLp (fun x => innerSL ℝ (g x) D[i]) 2 (volume : Measure Plano) := by
    apply ((innerSL ℝ D[i]).comp_memLp' hg).ae_eq
    exact Eventually.of_forall fun x => by
      change inner ℝ D[i] (g x) = inner ℝ (g x) D[i]
      exact real_inner_comm _ _
  refine ⟨hal, (hg'.locallyIntegrable (by norm_num)).locallyIntegrableOn univ, ?_⟩
  intro φ hφ _ _
  have he := integral_partes_traza_cuadrado v i φ hφ
  simp only [hv, Pi.zero_apply] at he
  have hz := Lp.coeFn_zero ℝ 2 volumenIntervaloSeno
  have hzφ (b : Bool) :
      (∫ t, (0 : L2Cara) t * φ (puntoCara i b t) ∂volumenIntervaloSeno) = 0 := by
    rw [← integral_zero (α := ℝ) (μ := volumenIntervaloSeno) (G := ℝ)]
    exact integral_congr_ae (hz.mono fun t ht => by dsimp only; rw [ht]; simp)
  rw [hzφ, hzφ, sub_self] at he
  have hdf : Continuous (fun x => fderiv ℝ φ x D[i]) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨_, hb⟩ := continuo_acotado_cuadrado hdf
  obtain ⟨_, hb'⟩ := continuo_acotado_cuadrado hφ.continuous
  have hf₁ := ((Lp.memLp (fnL u)).integrable (by norm_num)).bdd_mul
    hdf.aestronglyMeasurable hb
  have hf₂ := ((Lp.memLp (partialL D[i] u)).integrable (by norm_num)).bdd_mul
    hφ.continuous.aestronglyMeasurable hb'
  change (∫ x, _ + _ ∂volumenPoisson) = 0 at he
  rw [integral_add hf₁ hf₂] at he
  have hfirst : (∫ x, fderiv ℝ φ x D[i] • a x ∂(volume : Measure Plano)) =
      ∫ x, fderiv ℝ φ x D[i] * fnL u x ∂volumenPoisson := by
    rw [← integral_indicator cuadrado_abierto.measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ cuadrado <;> simp [a, hx, smul_eq_mul]
  have hsecond : (∫ x, φ x • innerSL ℝ (g x) D[i] ∂(volume : Measure Plano)) =
      ∫ x, φ x * partialL D[i] u x ∂volumenPoisson := by
    calc
      _ = ∫ x, φ x • innerSL ℝ (gradL u x) D[i] ∂volumenPoisson := by
        rw [← integral_indicator cuadrado_abierto.measurableSet]
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        by_cases hx : x ∈ cuadrado <;> simp [g, hx]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [coeFn_partialL D[i] u] with x hx
        simp [hx, real_inner_comm]
  change (∫ x, fderiv ℝ φ x D[i] • a x) = -(∫ x, φ x • innerSL ℝ (g x) D[i])
  rw [hfirst, hsecond]
  exact add_eq_zero_iff_eq_neg.mp he

private theorem memLp_dilatado {F : Type*} [NormedAddCommGroup F]
    {f : Plano → F} (hf : MemLp f 2 (volume : Measure Plano)) {r : ℝ} (hr : r ≠ 0) :
    MemLp (fun x => f (r • x)) 2 (volume : Measure Plano) := by
  let μ : Measure Plano := volume
  have hs := Measure.quasiMeasurePreserving_smul μ hr
  have hm := hf.aestronglyMeasurable
  have he : (fun x => f (r • x)) =ᵐ[μ] (fun x => hm.mk f (r • x)) :=
    hs.ae_eq_comp hm.ae_eq_mk
  have hmk : MemLp (hm.mk f) 2 μ := hf.ae_eq hm.ae_eq_mk
  change MemLp (fun x => f (r • x)) 2 μ
  rw [memLp_iff]
  rw [eLpNorm_congr_ae he, EllipticPdes.Analysis.eLpNorm_comp_smul_eq
    hm.stronglyMeasurable_mk hr two_ne_zero ENNReal.ofNat_ne_top]
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) hmk.eLpNorm_lt_top

private theorem norma_dilatado {F : Type*} [NormedAddCommGroup F]
    {f : Plano → F} (hf : MemLp f 2 (volume : Measure Plano)) {r : ℝ} (hr : 1 ≤ r) :
    eLpNorm (fun x => f (r • x)) 2 (volume : Measure Plano) ≤
      eLpNorm f 2 (volume : Measure Plano) := by
  let μ : Measure Plano := volume
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hm := hf.aestronglyMeasurable
  have hs := Measure.quasiMeasurePreserving_smul μ hr0.ne'
  have he : (fun x => f (r • x)) =ᵐ[μ] (fun x => hm.mk f (r • x)) :=
    hs.ae_eq_comp hm.ae_eq_mk
  rw [eLpNorm_congr_ae he,
    EllipticPdes.Analysis.eLpNorm_comp_smul_eq hm.stronglyMeasurable_mk hr0.ne'
      two_ne_zero ENNReal.ofNat_ne_top, ← eLpNorm_congr_ae hm.ae_eq_mk]
  conv_rhs => rw [← one_mul (eLpNorm f 2 μ)]
  apply mul_le_mul_left
  have hpow : 1 ≤ r ^ Module.finrank ℝ Plano := one_le_pow₀ hr
  have hinv : 0 ≤ (r ^ Module.finrank ℝ Plano)⁻¹ := by positivity
  rw [abs_of_nonneg hinv, ← ENNReal.one_rpow (1 / (2 : ℝ≥0∞).toReal)]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ hpow)

private theorem dilatacion_continua_compacta {F : Type*} [NormedAddCommGroup F]
    {f : Plano → F} (hf : Continuous f) (hcs : HasCompactSupport f)
    (r : ℕ → ℝ) (hr : ∀ n, 1 ≤ r n) (ht : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => eLpNorm ((fun x => f (r n • x)) - f) 2 (volume : Measure Plano))
      atTop (𝓝 0) := by
  let μ : Measure Plano := volume
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_closedBall (0 : Plano)
  let K := Metric.closedBall (0 : Plano) R
  obtain ⟨M, hM⟩ := hcs.isCompact.exists_bound_of_continuousOn hf.continuousOn
  let B := max M 0
  have hglob (x : Plano) : ‖f x‖ ≤ B := by
    by_cases hx : x ∈ tsupport f
    · exact (hM x hx).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact le_max_right _ _
  have hs (n : ℕ) {x : Plano} (hx : x ∉ K) : f (r n • x) = 0 ∧ f x = 0 := by
    refine ⟨image_eq_zero_of_notMem_tsupport (fun hx' => hx ?_),
      image_eq_zero_of_notMem_tsupport (fun hx' => hx (hR hx'))⟩
    have h := hR hx'
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg
      (zero_le_one.trans (hr n))] at h
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (le_mul_of_one_le_left (norm_nonneg _) (hr n)).trans h
  let A (n : ℕ) (x : Plano) : ℝ≥0∞ := ‖f (r n • x) - f x‖ₑ ^ (2 : ℝ)
  let C : Plano → ℝ≥0∞ := K.indicator (fun _ => ENNReal.ofReal (B + B) ^ (2 : ℝ))
  have hA (n : ℕ) : AEMeasurable (A n) μ :=
    ((hf.comp (continuous_const_smul _)).sub hf).enorm.measurable.aemeasurable.pow_const _
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, A n x ≤ C x := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ K
    · change A n x ≤ K.indicator _ x
      rw [indicator_of_mem hx]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (add_le_add (hglob _) (hglob _)))
    · change ‖f (r n • x) - f x‖ₑ ^ (2 : ℝ) ≤ K.indicator _ x
      rw [indicator_of_notMem hx, (hs n hx).1, (hs n hx).2, sub_self, enorm_zero]
      exact (ENNReal.zero_rpow_of_pos (by norm_num)).le
  have hC : ∫⁻ x, C x ∂μ ≠ ∞ := by
    dsimp only [C, K]
    rw [lintegral_indicator measurableSet_closedBall, lintegral_const, Measure.restrict_apply_univ]
    exact (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) ENNReal.ofReal_ne_top)
      ((isCompact_closedBall (0 : Plano) R).measure_lt_top (μ := μ))).ne
  have hpt : ∀ᵐ x ∂μ, Tendsto (fun n => A n x) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro x
    have hfx : Tendsto (fun n => f (r n • x) - f x) atTop (𝓝 (0 : F)) := by
      simpa using ((hf.tendsto x).comp (by simpa using ht.smul_const x)).sub_const (f x)
    have hen : Tendsto (fun n => ‖f (r n • x) - f x‖ₑ) atTop (𝓝 0) := by
      simpa only [Function.comp_def, enorm_zero] using
        (continuous_enorm.tendsto (0 : F)).comp hfx
    simpa [A, Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using
      ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp
        hen
  have hlim := tendsto_lintegral_of_dominated_convergence' C hA hbound hC
    (f := fun _ => (0 : ℝ≥0∞)) hpt
  rw [lintegral_zero] at hlim
  have hp := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hp
  convert hp using 1
  funext n
  have hm : AEStronglyMeasurable ((fun x => f (r n • x)) - f) μ :=
    ((hf.comp (continuous_const_smul _)).sub hf).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm,
    ENNReal.toReal_ofNat]
  rfl

private theorem dilatacion_continua_L2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plano → F} (hf : MemLp f 2 (volume : Measure Plano))
    (r : ℕ → ℝ) (hr : ∀ n, 1 ≤ r n) (ht : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => eLpNorm ((fun x => f (r n • x)) - f) 2 (volume : Measure Plano))
      atTop (𝓝 0) := by
  let μ : Measure Plano := volume
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hd : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by norm_num)).ne'
  obtain ⟨g, hgs, hfg, hgc, hg⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top hd
  have h := ENNReal.tendsto_nhds_zero.mp (dilatacion_continua_compacta hgc hgs r hr ht)
    (ε / 3) (pos_iff_ne_zero.mpr hd)
  filter_upwards [h] with n hn
  let F := fun x : Plano => f (r n • x)
  let G := fun x : Plano => g (r n • x)
  have hr0 := zero_lt_one.trans_le (hr n)
  have he : F - f = (F - G) + ((G - g) + (g - f)) := by abel
  have h1 : eLpNorm (F - G) 2 μ ≤ ε / 3 :=
    (norma_dilatado (hf.sub hg) (hr n)).trans hfg
  have h2 : eLpNorm (g - f) 2 μ ≤ ε / 3 := by rwa [eLpNorm_sub_comm]
  rw [he]
  calc
    _ ≤ eLpNorm (F - G) 2 μ + eLpNorm ((G - g) + (g - f)) 2 μ :=
      eLpNorm_add_le (by norm_num)
    _ ≤ ε / 3 + (ε / 3 + ε / 3) := add_le_add h1 <|
      (eLpNorm_add_le (by norm_num)).trans (add_le_add hn h2)
    _ = ε := by rw [← two_mul, ← one_add_mul]; norm_num; exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)

private theorem derivada_debil_dilatada {u : Plano → ℝ} {g : Plano → Plano}
    (hu : MemLp u 2 (volume : Measure Plano)) (hg : MemLp g 2 (volume : Measure Plano))
    (hw : HasWeakFDerivOn ⊤ u (fun x => innerSL ℝ (g x)) volume)
    {r : ℝ} (hr : 0 < r) :
    HasWeakFDerivOn ⊤ (fun x => u (r • x))
      (fun x => innerSL ℝ (r • g (r • x))) volume := by
  intro w
  have hU := memLp_dilatado hu hr.ne'
  have hG : MemLp (fun x => r • g (r • x)) 2 (volume : Measure Plano) :=
    (memLp_dilatado hg hr.ne').const_smul r
  have hGw : MemLp (fun x => innerSL ℝ (r • g (r • x)) w) 2 (volume : Measure Plano) := by
    apply ((innerSL ℝ w).comp_memLp' hG).ae_eq
    exact Eventually.of_forall fun x => by
      change inner ℝ w (r • g (r • x)) = inner ℝ (r • g (r • x)) w
      exact real_inner_comm _ _
  rw [hasWeakLineDerivOn_iff]
  refine ⟨(hU.locallyIntegrable (by norm_num)).locallyIntegrableOn univ,
    (hGw.locallyIntegrable (by norm_num)).locallyIntegrableOn univ, ?_⟩
  intro φ hφ hcs _
  let ψ := fun x : Plano => φ (r⁻¹ • x)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (contDiff_id.const_smul r⁻¹)
  have hψcs : HasCompactSupport ψ :=
    hcs.comp_homeomorph (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have htest := (hw w).integral_eq hψ hψcs (subset_univ _)
  have hx (x : Plano) : r⁻¹ • (r • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hd (x : Plano) : fderiv ℝ φ x w = r * fderiv ℝ ψ (r • x) w := by
    dsimp only [ψ]
    rw [EllipticPdes.Analysis.fderiv_comp_smul (hφ.differentiable (by simp)), hx]
    simp [hr.ne']
  let A : Plano → ℝ := fun x => fderiv ℝ ψ x w • u x
  let B : Plano → ℝ := fun x => ψ x • innerSL ℝ (g x) w
  have e₁ : (∫ x, fderiv ℝ φ x w • u (r • x)) =
      r * (∫ x, A (r • x)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [A, hd x, mul_assoc])
  have e₂ : (∫ x, φ x • innerSL ℝ (r • g (r • x)) w) =
      r * (∫ x, B (r • x)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      simp [B, ψ, hx, smul_eq_mul, mul_left_comm])
  rw [e₁, e₂, Measure.integral_comp_smul volume A r, Measure.integral_comp_smul volume B r]
  change (∫ x, A x) = -(∫ x, B x) at htest
  rw [htest, smul_neg, mul_neg]

private theorem soporte_dilatado_cuadrado {F : Type*} [NormedAddCommGroup F]
    (f : Plano → F) {r : ℝ} (hr : 1 < r) :
    HasCompactSupport (fun x => cuadrado.indicator f (r • x)) ∧
      tsupport (fun x => cuadrado.indicator f (r • x)) ⊆ cuadrado := by
  let K := (fun x : Plano => r • x) ⁻¹' closure cuadrado
  have hr0 := zero_lt_one.trans hr
  have hK : IsCompact K :=
    (Homeomorph.smulOfNeZero r hr0.ne').isCompact_preimage.mpr cuadrado_acotado.isCompact_closure
  have hsub : tsupport (fun x => cuadrado.indicator f (r • x)) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (indicator_of_notMem (fun h => hn (subset_closure h)) f)
  refine ⟨hK.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans ?_⟩
  intro x hx i
  change r • x ∈ closure cuadrado at hx
  rw [clausura_cuadrado] at hx
  have hi := hx i
  change -1 ≤ r * x i ∧ r * x i ≤ 1 at hi
  change -1 < x i ∧ x i < 1
  constructor
  · by_contra! h
    nlinarith [mul_le_mul_of_nonneg_left h hr0.le, hi.1]
  · by_contra! h
    nlinarith [mul_le_mul_of_nonneg_left h hr0.le, hi.2]

private theorem dilatacion_gradiente_continua {g : Plano → Plano}
    (hg : MemLp g 2 (volume : Measure Plano))
    (r : ℕ → ℝ) (hr : ∀ n, 1 ≤ r n) (ht : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => eLpNorm ((fun x => r n • g (r n • x)) - g) 2 (volume : Measure Plano))
      atTop (𝓝 0) := by
  let μ : Measure Plano := volume
  let G (n : ℕ) : Plano → Plano := fun x => g (r n • x)
  have hA := dilatacion_continua_L2 hg r hr ht
  have hB : Tendsto (fun n => ENNReal.ofReal ‖r n - 1‖) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
      (by simpa using (ht.sub_const 1).norm)
  have hlim := hA.add (ENNReal.Tendsto.mul_const hB
    (Or.inr hg.eLpNorm_ne_top))
  simp only [zero_mul, add_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
  intro n
  have he : (fun x => r n • g (r n • x)) - g =
      (G n - g) + (r n - 1) • G n := by
    funext x
    simp [G, sub_smul]
  dsimp only
  rw [he]
  refine (eLpNorm_add_le (by norm_num)).trans (add_le_add_right ?_ _)
  rw [eLpNorm_const_smul, ← ofReal_norm]
  gcongr
  exact norma_dilatado hg (hr n)

set_option maxHeartbeats 800000 in
/-- Núcleo de la traza. La contracción del soporte de la prolongación por
cero permite aplicar la densidad por molificación dentro del cuadrado. -/
theorem nucleo_trazaSobolevCuadrado_eq_H01 (v : W12 (volume : Measure Plano) cuadrado) :
    (v : H1Graph volume cuadrado) ∈ H01 (volume : Measure Plano) cuadrado ↔
      trazaSobolevCuadrado v = 0 := by
  refine ⟨trazaSobolevCuadrado_cero_de_H01 v, fun hv => ?_⟩
  let u : H1Graph (volume : Measure Plano) cuadrado := v
  let a := cuadrado.indicator (fnL u : Plano → ℝ)
  let g := cuadrado.indicator (gradL u : Plano → Plano)
  have ha := extension_memLp (Lp.memLp (fnL u))
  have hg := extension_memLp (Lp.memLp (gradL u))
  have hw := extension_cero_traza_nula v hv
  let r (n : ℕ) := 1 + ancho n
  have hr (n : ℕ) : 1 < r n := lt_add_of_pos_right _ (ancho_pos n)
  have ht : Tendsto r atTop (𝓝 1) := by simpa [r] using tendsto_const_nhds.add ancho_tendsto_cero
  let A (n : ℕ) (x : Plano) : ℝ := a (r n • x)
  let G (n : ℕ) (x : Plano) : Plano := r n • g (r n • x)
  have hAm (n : ℕ) : MemLp (A n) 2 (volume : Measure Plano) :=
    memLp_dilatado ha (zero_lt_one.trans (hr n)).ne'
  have hGm (n : ℕ) : MemLp (G n) 2 (volume : Measure Plano) :=
    (memLp_dilatado hg (zero_lt_one.trans (hr n)).ne').const_smul (r n)
  let Φ (n : ℕ) : H1Graph (volume : Measure Plano) cuadrado :=
    mk ((hAm n).mono_measure Measure.restrict_le_self).toLp
      ((hGm n).mono_measure Measure.restrict_le_self).toLp
  have hΦ (n : ℕ) : Φ n ∈ H01 (volume : Measure Plano) cuadrado := by
    obtain ⟨hc, hs⟩ := soporte_dilatado_cuadrado (fnL u : Plano → ℝ) (hr n)
    exact mem_H01_of_hasCompactSupport cuadrado_abierto
      (derivada_debil_dilatada ha hg hw (zero_lt_one.trans (hr n))) (hAm n) (hGm n) hc hs
  have hU := ae_restrict_mem (μ := (volume : Measure Plano)) cuadrado_abierto.measurableSet
  have hae : a =ᵐ[volumenPoisson] (fnL u : Plano → ℝ) :=
    hU.mono (fun _ hx => indicator_of_mem hx _)
  have hge : g =ᵐ[volumenPoisson] (gradL u : Plano → Plano) :=
    hU.mono (fun _ hx => indicator_of_mem hx _)
  have hAlim : Tendsto (fun n => eLpNorm (A n - ⇑(fnL u)) 2 volumenPoisson) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (dilatacion_continua_L2 ha r (fun n => (hr n).le) ht) (fun _ => zero_le)
    intro n
    change eLpNorm (A n - ⇑(fnL u)) 2 volumenPoisson ≤
      eLpNorm (A n - a) 2 (volume : Measure Plano)
    exact (eLpNorm_congr_ae ((EventuallyEq.rfl (f := A n)).sub hae.symm)).trans_le
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hGlim : Tendsto (fun n => eLpNorm (G n - ⇑(gradL u)) 2 volumenPoisson) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (dilatacion_gradiente_continua hg r (fun n => (hr n).le) ht) (fun _ => zero_le)
    intro n
    change eLpNorm (G n - ⇑(gradL u)) 2 volumenPoisson ≤
      eLpNorm (G n - g) 2 (volume : Measure Plano)
    exact (eLpNorm_congr_ae ((EventuallyEq.rfl (f := G n)).sub hge.symm)).trans_le
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hlim := tendsto_mk_of_tendsto_eLpNorm (Lp.memLp (fnL u)) (Lp.memLp (gradL u))
    (Φ := Φ) (fun n => ((hAm n).mono_measure Measure.restrict_le_self).coeFn_toLp)
    (fun n => ((hGm n).mono_measure Measure.restrict_le_self).coeFn_toLp) hAlim hGlim
  exact isClosed_H01.mem_of_tendsto (by simpa using hlim) (Eventually.of_forall hΦ)

theorem diferencia_mem_H01_de_trazas_iguales
    (h u : W12 (volume : Measure Plano) cuadrado)
    (he : trazaSobolevCuadrado h = trazaSobolevCuadrado u) :
    (h : H1Graph volume cuadrado) - u ∈ H01 (volume : Measure Plano) cuadrado :=
  (nucleo_trazaSobolevCuadrado_eq_H01 (h - u)).mpr (by rw [map_sub, he, sub_self])

private def perfilTraza (b : Bool) (δ t : ℝ) : ℝ :=
  if b then lado δ (-t) - 1 else 1 - lado δ t

private theorem perfilTraza_suave (b : Bool) (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (perfilTraza b δ) := by
  cases b
  · exact contDiff_const.sub (lado_suave δ)
  · exact ((lado_suave δ).comp contDiff_neg).sub contDiff_const

private theorem perfilTraza_extremos (b : Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    perfilTraza b δ 1 = (if b then -1 else 0) ∧
      perfilTraza b δ (-1) = (if b then 0 else 1) := by
  have hl := lado_cero hδ (show (-1 : ℝ) + 1 ≤ δ by linarith)
  have hr := lado_uno hδ (show 2 * δ ≤ (1 : ℝ) + 1 by linarith)
  cases b <;> simp [perfilTraza, hl, hr]

private theorem perfilTraza_abs_le (b : Bool) (δ t : ℝ) : |perfilTraza b δ t| ≤ 1 := by
  have h (s : ℝ) : 0 ≤ lado δ s ∧ lado δ s ≤ 1 :=
    ⟨lado_no_neg δ s, lado_le_uno δ s⟩
  apply abs_le.mpr
  cases b <;> simp only [perfilTraza, Bool.false_eq_true, if_false, if_true]
  · constructor <;> linarith [(h t).1, (h t).2]
  · constructor <;> linarith [(h (-t)).1, (h (-t)).2]

private theorem perfilTraza_deriv_no_pos (b : Bool) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    deriv (perfilTraza b δ) t ≤ 0 := by
  have hm : Monotone (lado δ) :=
    Real.smoothTransition.monotone.comp (fun _ _ h =>
      sub_le_sub_right (div_le_div_of_nonneg_right (add_le_add_left h _) hδ.le) _)
  apply Antitone.deriv_nonpos
  intro x y hxy
  cases b
  · exact sub_le_sub_left (hm hxy) 1
  · exact sub_le_sub_right (hm (neg_le_neg hxy)) 1

private theorem perfilTraza_eventual_cero (b : Bool) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ∀ᶠ n in atTop, perfilTraza b (ancho n) t = 0 := by
  have h (s : ℝ) (hs : 0 < s + 1) : ∀ᶠ n in atTop, 2 * ancho n < s + 1 :=
    (show Tendsto (fun n => 2 * ancho n) atTop (𝓝 (0 : ℝ)) by
      simpa using tendsto_const_nhds.mul ancho_tendsto_cero).eventually_lt_const hs
  filter_upwards [h t (by linarith [ht.1]), h (-t) (by linarith [ht.2])] with n h₁ h₂
  cases b <;> simp [perfilTraza, lado_uno (ancho_pos n) h₁.le, lado_uno (ancho_pos n) h₂.le]

private theorem perfilTraza_deriv_soporte (b : Bool) {δ t : ℝ} (hδ : 0 < δ)
    (h : 2 * δ < |t - extremoCara b|) (ht : t ∈ Ioo (-1 : ℝ) 1) :
    deriv (perfilTraza b δ) t = 0 := by
  have heq : perfilTraza b δ =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    cases b
    · change 2 * δ < |t - (-1)| at h
      rw [abs_of_nonneg (by linarith [ht.1])] at h
      filter_upwards [Ioi_mem_nhds (show -1 + 2 * δ < t by linarith)] with s hs
      change -1 + 2 * δ < s at hs
      simp [perfilTraza, lado_uno hδ (by linarith [hs] : 2 * δ ≤ s + 1)]
    · change 2 * δ < |t - 1| at h
      rw [abs_of_nonpos (by linarith [ht.2])] at h
      filter_upwards [Iio_mem_nhds (show t < 1 - 2 * δ by linarith)] with s hs
      change s < 1 - 2 * δ at hs
      simp [perfilTraza, lado_uno hδ (by linarith [hs] : 2 * δ ≤ -s + 1)]
  simpa using heq.deriv_eq

private theorem perfilTraza_masa (b : Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    (∫ t, deriv (perfilTraza b δ) t ∂volumenIntervaloSeno) = -1 := by
  have hd : ContDiff ℝ 1 (perfilTraza b δ) := (perfilTraza_suave b δ).of_le (by simp)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -1) (b := 1)
    (fun t _ => (hd.differentiable (by norm_num) t).hasDerivAt)
    ((hd.continuous_deriv (by norm_num)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at h
  rw [show volumenIntervaloSeno = volume.restrict (Ioo (-1 : ℝ) 1) from rfl, h,
    (perfilTraza_extremos b hδ hδ').1, (perfilTraza_extremos b hδ hδ').2]
  cases b <;> norm_num

private theorem parCara_symm_mem_closure (i : Fin 2) {t s : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (hs : s ∈ Icc (-1 : ℝ) 1) :
    (parCara i).symm (t, s) ∈ closure cuadrado := by
  rw [clausura_cuadrado]
  intro j
  by_cases hj : j = i
  · simpa [parCara_symm_coord, hj] using ht
  · simpa [parCara_symm_coord, hj] using hs

private theorem coordenadas_volumen_continuo {f : Plano → ℝ}
    (hf : ContinuousOn f (closure cuadrado)) (i : Fin 2) :
    ContinuousOn (fun z : ℝ × ℝ => f ((parCara i).symm z))
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := by
  have hc : Continuous (parCara i).symm := by
    apply (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).isEmbedding.continuous_iff.mpr
    apply continuous_pi
    intro j
    change Continuous (fun z => (parCara i).symm z j)
    simp only [parCara_symm_coord]
    split_ifs
    · exact continuous_fst
    · exact continuous_snd
  exact hf.comp hc.continuousOn (fun _ hz => parCara_symm_mem_closure i hz.1 hz.2)

private theorem integral_perfil_continuo {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) (b : Bool) :
    Tendsto (fun n => ∫ z : ℝ × ℝ,
      deriv (perfilTraza b (ancho n)) z.1 * f z
        ∂(volumenIntervaloSeno.prod volumenIntervaloSeno)) atTop
      (𝓝 (-(∫ t, f (extremoCara b, t) ∂volumenIntervaloSeno))) := by
  let I := Icc (-1 : ℝ) 1
  let μ := volumenIntervaloSeno
  let K := I ×ˢ I
  let d (n : ℕ) := deriv (perfilTraza b (ancho n))
  have hc (n : ℕ) : Continuous (d n) := by
    have h : ContDiff ℝ 1 (perfilTraza b (ancho n)) := (perfilTraza_suave b _).of_le (by simp)
    exact h.continuous_deriv (by norm_num)
  have hμ : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by simp [μ, volumenIntervaloSeno])
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hU : ∀ᵐ t ∂μ, t ∈ Ioo (-1 : ℝ) 1 :=
    ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo
  have hfiniteI : (volume : Measure ℝ) (Ioo (-1 : ℝ) 1) ≠ ∞ := by simp [Real.volume_Ioo]
  have hfaceI : Integrable (fun t => f (extremoCara b, t)) μ := by
    apply ContinuousOn.integrableOn_of_subset_isCompact _ isCompact_Icc measurableSet_Ioo
      Ioo_subset_Icc_self hfiniteI
    exact hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨by cases b <;> norm_num [I, extremoCara], ht⟩)
  have hb : extremoCara b ∈ I := by cases b <;> norm_num [I, extremoCara]
  have hf₀ : ContinuousOn (fun t => f (extremoCara b, t)) I :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hb, ht⟩)
  have hInt (n : ℕ) : Integrable (fun z : ℝ × ℝ => d n z.1 * f z) (μ.prod μ) := by
    rw [show μ.prod μ = ((volume : Measure ℝ).prod volume).restrict
      (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) from Measure.prod_restrict _ _]
    apply (((hc n).comp continuous_fst).continuousOn.mul hf).integrableOn_of_subset_isCompact
      hK (measurableSet_Ioo.prod measurableSet_Ioo)
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
    rw [Measure.prod_prod]
    exact (ENNReal.mul_lt_top hfiniteI.lt_top hfiniteI.lt_top).ne
  have hεlimit : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      ‖(∫ z : ℝ × ℝ, d n z.1 * f z ∂(μ.prod μ)) +
        ∫ t, f (extremoCara b, t) ∂μ‖ < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδbound⟩ := Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hf)
      (ε / 4) (by positivity)
    have hsmall : ∀ᶠ n in atTop, 2 * ancho n < δ :=
      (show Tendsto (fun n => 2 * ancho n) atTop (𝓝 (0 : ℝ)) by
        simpa using tendsto_const_nhds.mul ancho_tendsto_cero).eventually_lt_const hδ
    filter_upwards [hsmall] with n hn
    have hn1 : ancho n ≤ 1 := by
      unfold ancho
      apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hm := perfilTraza_masa b (ancho_pos n) hn1
    have hdin : Integrable (d n) μ :=
      (hc n).continuousOn.integrableOn_of_subset_isCompact isCompact_Icc
        measurableSet_Ioo Ioo_subset_Icc_self hfiniteI
    have hnorm : (∫ t, ‖d n t‖ ∂μ) = 1 := by
      have hneg : (fun t => ‖d n t‖) = fun t => -d n t := by
        funext t
        rw [Real.norm_eq_abs, abs_of_nonpos (perfilTraza_deriv_no_pos b (ancho_pos n) t)]
      rw [hneg, integral_neg]
      change -(∫ t, deriv (perfilTraza b (ancho n)) t ∂μ) = 1
      rw [hm]
      norm_num
    rw [integral_prod_symm _ (hInt n), ← integral_add]
    · calc
        _ ≤ ∫ t, ‖(∫ s, d n s * f (s, t) ∂μ) + f (extremoCara b, t)‖ ∂μ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ _ : ℝ, ε / 4 ∂μ := by
          apply integral_mono_ae
          · exact ((hInt n).integral_prod_right.add hfaceI).norm
          · exact integrable_const _
          · filter_upwards [hU] with t ht
            have hft : ContinuousOn (fun s => d n s * f (s, t)) I :=
              (hc n).continuousOn.mul (hf.comp
                (continuous_id.prodMk continuous_const).continuousOn
                (fun _ hs => ⟨hs, Ioo_subset_Icc_self ht⟩))
            have hfint := hft.integrableOn_of_subset_isCompact isCompact_Icc
              measurableSet_Ioo Ioo_subset_Icc_self hfiniteI
            have hrewrite : (∫ s, d n s * f (s, t) ∂μ) + f (extremoCara b, t) =
                ∫ s, d n s * (f (s, t) - f (extremoCara b, t)) ∂μ := by
              simp_rw [mul_sub]
              rw [integral_sub hfint (hdin.mul_const _), integral_mul_const]
              change _ = _ - (∫ s, deriv (perfilTraza b (ancho n)) s ∂μ) * _
              rw [hm]
              ring
            rw [hrewrite]
            calc
              _ ≤ ∫ s, (ε / 4) * ‖d n s‖ ∂μ := by
                apply norm_integral_le_of_norm_le (hdin.norm.const_mul _)
                filter_upwards [hU] with s hs
                by_cases hdist : 2 * ancho n < |s - extremoCara b|
                · have hz := perfilTraza_deriv_soporte b (ancho_pos n) hdist hs
                  change d n s = 0 at hz
                  rw [hz]
                  simp
                · rw [norm_mul]
                  have hdist' : dist (s, t) (extremoCara b, t) < δ := by
                    simpa [Prod.dist_eq, Real.dist_eq] using (le_of_not_gt hdist).trans_lt hn
                  have hdiff := hδbound (s, t)
                    (show (s, t) ∈ K from ⟨Ioo_subset_Icc_self hs, Ioo_subset_Icc_self ht⟩)
                    (extremoCara b, t)
                    (show (extremoCara b, t) ∈ K from ⟨hb, Ioo_subset_Icc_self ht⟩) hdist'
                  rw [Real.dist_eq] at hdiff
                  rw [mul_comm (ε / 4), Real.norm_eq_abs]
                  exact mul_le_mul_of_nonneg_left hdiff.le (abs_nonneg _)
              _ = _ := by rw [integral_const_mul, hnorm, mul_one]
        _ < ε := by
          rw [integral_const]
          rw [Measure.real, show μ = volume.restrict (Ioo (-1 : ℝ) 1) from rfl,
            Measure.restrict_apply_univ, Real.volume_Ioo]
          norm_num [smul_eq_mul]
          linarith
    · exact (hInt n).integral_prod_right
    · exact hfaceI
  apply Metric.tendsto_nhds.2
  intro ε hε
  simpa [dist_eq_norm] using hεlimit ε hε

set_option maxHeartbeats 800000 in
/-- La traza Sobolev recupera la restricción a las caras de un representante
continuo en el cuadrado cerrado. -/
theorem trazaSobolevCuadrado_continua
    (v : W12 (volume : Measure Plano) cuadrado) {f : Plano → ℝ}
    (hf : ContinuousOn f (closure cuadrado))
    (hrep : ⇑(fnL (v : H1Graph volume cuadrado)) =ᵐ[volumenPoisson] f)
    (i : Fin 2) (b : Bool) :
    ⇑(trazaSobolevCuadrado v (i, b)) =ᵐ[volumenIntervaloSeno] fun t => f (puntoCara i b t) := by
  let I := Ioo (-1 : ℝ) 1
  let μ := volumenIntervaloSeno
  let U := (v : H1Graph volume cuadrado)
  let T : ℝ → ℝ := trazaSobolevCuadrado v (i, b)
  let F := fun t => f (puntoCara i b t)
  have hFi : Integrable F μ := by
    have hc : ContinuousOn F (Icc (-1 : ℝ) 1) :=
      (coordenadas_volumen_continuo hf i).comp
        (continuous_const.prodMk continuous_id).continuousOn (fun _ ht =>
          ⟨by cases b <;> norm_num [extremoCara], ht⟩)
    exact hc.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Ioo
      Ioo_subset_Icc_self (by simp [Real.volume_Ioo])
  have hTi : Integrable T μ := by
    letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by simp [μ, volumenIntervaloSeno])
    exact (Lp.memLp (trazaSobolevCuadrado v (i, b))).integrable (by norm_num)
  have heq : ∀ p : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) p → HasCompactSupport p → tsupport p ⊆ I →
      ∫ t, p t • (T - F) t = 0 := by
    intro p hp _ hps
    obtain ⟨j, hji, hj⟩ := parCara_segunda i
    let χ (n : ℕ) := perfilTraza b (ancho n)
    let φ (n : ℕ) : Plano → ℝ := fun x => χ n (x i) * p (x j)
    have hχ (n : ℕ) := perfilTraza_suave b (ancho n)
    have hφ (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (φ n) :=
      ((hχ n).comp ((EuclideanSpace.proj i : Plano →L[ℝ] ℝ).contDiff)).mul
        (hp.comp ((EuclideanSpace.proj j : Plano →L[ℝ] ℝ).contDiff))
    have hD (n : ℕ) (x : Plano) : fderiv ℝ (φ n) x D[i] = deriv (χ n) (x i) * p (x j) := by
      let P (k : Fin 2) : Plano →L[ℝ] ℝ := EuclideanSpace.proj k
      have h₁ := ((hχ n).differentiable (by simp) (x i)).hasDerivAt.comp_hasFDerivAt x (P i).hasFDerivAt
      have h₂ := (hp.differentiable (by simp) (x j)).hasDerivAt.comp_hasFDerivAt x (P j).hasFDerivAt
      have h := congrArg (fun A : Plano →L[ℝ] ℝ => A D[i]) (h₁.mul h₂).fderiv
      change fderiv ℝ (φ n) x D[i] = _ at h
      simpa [P, EuclideanSpace.single, PiLp.single_apply, Ne.symm hji, mul_comm] using h
    let a : Plano → ℝ := fnL U
    let g : Plano → ℝ := partialL D[i] U
    have hI (n : ℕ) : (∫ x, fderiv ℝ (φ n) x D[i] * a x + φ n x * g x ∂volumenPoisson) =
        -(∫ t, T t * p t ∂μ) := by
      have hn : ancho n ≤ 1 := by
        unfold ancho
        apply (div_le_one (by positivity)).mpr
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have hend := perfilTraza_extremos b (ancho_pos n) hn
      have hval (b' : Bool) (t : ℝ) :
          φ n (puntoCara i b' t) = χ n (extremoCara b') * p t := by
        simp [φ, puntoCara, parCara_symm_coord, hji]
      have he := integral_partes_traza_cuadrado v i (φ n) (hφ n)
      change (∫ x, _ + _ ∂volumenPoisson) = _ at he
      simp_rw [hval] at he
      cases b <;> simpa [T, μ, χ, extremoCara, hend.1, hend.2, integral_neg] using he
    have hg : Integrable g volumenPoisson := (Lp.memLp (partialL D[i] U)).integrable (by norm_num)
    obtain ⟨B, hB⟩ := continuo_acotado_cuadrado
      (hp.continuous.comp ((EuclideanSpace.proj j : Plano →L[ℝ] ℝ).continuous))
    have hφbound (n : ℕ) : ∀ᵐ x ∂volumenPoisson, ‖φ n x‖ ≤ B := by
      filter_upwards [hB] with x hx
      change ‖χ n (x i) * p (x j)‖ ≤ B
      rw [norm_mul, Real.norm_eq_abs (χ n (x i))]
      exact (mul_le_mul_of_nonneg_right (perfilTraza_abs_le b (ancho n) (x i))
        (norm_nonneg _)).trans (by simpa using hx)
    have hgInt (n : ℕ) : Integrable (fun x => φ n x * g x) volumenPoisson :=
      hg.bdd_mul (hφ n).continuous.aestronglyMeasurable (hφbound n)
    have haInt (n : ℕ) : Integrable (fun x => fderiv ℝ (φ n) x D[i] * a x) volumenPoisson := by
      have hc : Continuous (fun x => fderiv ℝ (φ n) x D[i]) :=
        ((hφ n).continuous_fderiv (by simp)).clm_apply continuous_const
      obtain ⟨_, hB⟩ := continuo_acotado_cuadrado hc
      exact ((Lp.memLp (fnL U)).integrable (by norm_num)).bdd_mul hc.aestronglyMeasurable hB
    have hg0 : Tendsto (fun n => ∫ x, φ n x * g x ∂volumenPoisson) atTop (𝓝 0) := by
      rw [← integral_zero (α := Plano) (μ := volumenPoisson) (G := ℝ)]
      refine tendsto_integral_of_dominated_convergence (fun x => B * ‖g x‖)
        (fun n => (hgInt n).aestronglyMeasurable) (hg.norm.const_mul B) ?_ ?_
      · intro n
        filter_upwards [hφbound n] with x hx
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      · filter_upwards [ae_restrict_mem (μ := (volume : Measure Plano))
          cuadrado_abierto.measurableSet] with x hx
        apply tendsto_const_nhds.congr'
        filter_upwards [perfilTraza_eventual_cero b (hx i)] with n hn
        simp [φ, χ, hn]
    let fp : ℝ × ℝ → ℝ := fun z => f ((parCara i).symm z) * p z.2
    have hfp : ContinuousOn fp (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
      (coordenadas_volumen_continuo hf i).mul (hp.continuous.comp continuous_snd).continuousOn
    have ha0 : Tendsto (fun n => ∫ x, fderiv ℝ (φ n) x D[i] * a x ∂volumenPoisson)
        atTop (𝓝 (-(∫ t, F t * p t ∂μ))) := by
      apply (integral_perfil_continuo hfp b).congr
      intro n
      rw [← (parCara_medida i).integral_comp (parCara i).measurableEmbedding]
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      dsimp [fp, a] at *
      rw [hD, hx, parCara_fst, hj, (parCara i).symm_apply_apply]
      ring
    have ht := ha0.add hg0
    simp only [add_zero] at ht
    have hsum (n : ℕ) :
        (∫ x, fderiv ℝ (φ n) x D[i] * a x ∂volumenPoisson) +
          (∫ x, φ n x * g x ∂volumenPoisson) = -(∫ t, T t * p t ∂μ) := by
      rw [← integral_add (haInt n) (hgInt n), hI n]
    have hcon := neg_injective (tendsto_nhds_unique ht
      (tendsto_const_nhds.congr (fun n => (hsum n).symm)))
    have hpB : ∃ M, ∀ᵐ t ∂μ, ‖p t‖ ≤ M := by
      obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (s := Icc (-1 : ℝ) 1) hp.continuous.continuousOn
      exact ⟨M, (ae_restrict_mem measurableSet_Ioo).mono
        (fun t ht => hM t (Ioo_subset_Icc_self ht))⟩
    obtain ⟨_, hpB⟩ := hpB
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := I) (fun t ht => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hps h)), zero_smul])]
    simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub (hTi.bdd_mul hp.continuous.aestronglyMeasurable hpB)
      (hFi.bdd_mul hp.continuous.aestronglyMeasurable hpB)]
    simp_rw [mul_comm (p _) _]
    exact sub_eq_zero.mpr hcon.symm
  have hloc : LocallyIntegrableOn (T - F) I (volume : Measure ℝ) :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hTi.sub hFi).locallyIntegrable
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc heq
  have hz' := (ae_restrict_iff' measurableSet_Ioo).mpr hz
  exact hz'.mono (fun t ht => sub_eq_zero.mp ht)

#check integral_partes_traza_cuadrado
#check extension_cero_traza_nula
#check nucleo_trazaSobolevCuadrado_eq_H01
#print axioms integral_partes_traza_cuadrado
#print axioms extension_cero_traza_nula
#print axioms nucleo_trazaSobolevCuadrado_eq_H01
#print axioms diferencia_mem_H01_de_trazas_iguales
#print axioms trazaSobolevCuadrado_continua

end TesisPINN
