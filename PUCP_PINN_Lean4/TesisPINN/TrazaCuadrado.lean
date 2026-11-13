import TesisPINN.DirichletLevantamiento
import EllipticPdes.Sobolev.GraphLattice

/-! Condición de Dirichlet puntual para representantes Sobolev continuos. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Filter Set EllipticPdes EllipticPdes.H1Graph
open scoped Topology ENNReal

private theorem convergencia_truncacion_L2 {F : Type*} [NormedAddCommGroup F]
    {a : ℕ → Plano → F} {b M : Plano → F}
    (ha : ∀ n, AEStronglyMeasurable (a n) volumenPoisson)
    (hb : AEStronglyMeasurable b volumenPoisson) (hM : MemLp M 2 volumenPoisson)
    (hbd : ∀ n, ∀ᵐ x ∂volumenPoisson, ‖a n x - b x‖ ≤ ‖M x‖)
    (ht : ∀ᵐ x ∂volumenPoisson, Tendsto (fun n => a n x) atTop (𝓝 (b x))) :
    Tendsto (fun n => eLpNorm (a n - b) 2 volumenPoisson) atTop (𝓝 0) := by
  have hrep (n : ℕ) : eLpNorm (a n - b) 2 volumenPoisson =
      (∫⁻ x, ‖a n x - b x‖ₑ ^ (2 : ℝ) ∂volumenPoisson) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top ((ha n).sub hb),
      ENNReal.toReal_ofNat]
    rfl
  simp_rw [hrep]
  have hlim : Tendsto (fun n => ∫⁻ x, ‖a n x - b x‖ₑ ^ (2 : ℝ) ∂volumenPoisson)
      atTop (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂volumenPoisson)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖M x‖ₑ ^ (2 : ℝ))
      (fun n => ((ha n).sub hb).enorm.pow_const _) (fun n => (hbd n).mono fun x hx => ?_) ?_ ?_
    · apply ENNReal.rpow_le_rpow _ (by norm_num)
      exact enorm_le_iff_norm_le.mpr hx
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        hM.eLpNorm_lt_top).ne
    · filter_upwards [ht] with x hx
      have hn : Tendsto (fun n => ‖a n x - b x‖ₑ) atTop (𝓝 0) := by
        simpa only [enorm_zero, Function.comp_def, sub_self] using
          (continuous_enorm.tendsto (0 : F)).comp (by simpa using hx.sub_const (b x))
      have h := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0 |>.comp hn
      simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using h
  rw [lintegral_zero] at hlim
  have h := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp hlim
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h

private theorem compact_supernivel {v : Plano → ℝ}
    (hv : ContinuousOn v (closure cuadrado)) (hz : EqOn v 0 (frontier cuadrado))
    {k : ℝ} (hk : 0 < k) :
    IsCompact {x ∈ closure cuadrado | k ≤ v x} ∧
      {x ∈ closure cuadrado | k ≤ v x} ⊆ cuadrado := by
  have hc : IsClosed {x ∈ closure cuadrado | k ≤ v x} :=
    hv.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
  refine ⟨cuadrado_acotado.isCompact_closure.of_isClosed_subset hc inter_subset_left, ?_⟩
  intro x hx
  by_contra h
  have hxfr : x ∈ frontier cuadrado := by
    rw [cuadrado_abierto.frontier_eq]
    exact ⟨hx.1, h⟩
  have he : v x = 0 := hz hxfr
  exact (not_le_of_gt hk) (he ▸ hx.2)

private theorem truncacion_positiva_mem_H01
    (e : H1Graph (volume : Measure Plano) cuadrado) (he : e ∈ W12 volume cuadrado)
    {v : Plano → ℝ} (hv : ContinuousOn v (closure cuadrado))
    (hvrep : ⇑(fnL e) =ᵐ[volumenPoisson] v) (hz : EqOn v 0 (frontier cuadrado))
    {k : ℝ} (hk : 0 < k) :
    ∃ w ∈ H01 (volume : Measure Plano) cuadrado,
      ⇑(fnL w) =ᵐ[volumenPoisson] (fun x => max (v x - k) 0) ∧
      ⇑(gradL w) =ᵐ[volumenPoisson] (fun x => if k < v x then gradL e x else 0) := by
  classical
  let a : Plano → ℝ := fun x => max (v x - k) 0
  let b : Plano → Plano := fun x => if k < v x then gradL e x else 0
  let A := cuadrado.indicator a
  let B := cuadrado.indicator b
  let K := {x ∈ closure cuadrado | k ≤ v x}
  obtain ⟨hK, hKU⟩ := compact_supernivel hv hz hk
  have hU := ae_restrict_mem (μ := (volume : Measure Plano)) cuadrado_abierto.measurableSet
  have hvm := (Lp.memLp (fnL e)).ae_eq hvrep
  have ham : MemLp a 2 volumenPoisson := memLp_max_sub_const hvm hk.le
  have hbm : MemLp b 2 volumenPoisson := memLp_ite_lt_vec hvm (Lp.memLp (gradL e)) k
  have hAm : MemLp A 2 (volume : Measure Plano) :=
    (memLp_indicator_iff_restrict cuadrado_abierto.measurableSet.nullMeasurableSet).2 ham
  have hBm : MemLp B 2 (volume : Measure Plano) :=
    (memLp_indicator_iff_restrict cuadrado_abierto.measurableSet.nullMeasurableSet).2 hbm
  have hAae : A =ᵐ[volumenPoisson] a := hU.mono fun _ hx => indicator_of_mem hx _
  have hBae : B =ᵐ[volumenPoisson] b := hU.mono fun _ hx => indicator_of_mem hx _
  have hzero (x : Plano) (hx : x ∉ K) : A x = 0 ∧ B x = 0 := by
    by_cases hxu : x ∈ cuadrado
    · have hvk : ¬k ≤ v x := fun h => hx ⟨subset_closure hxu, h⟩
      simp [A, B, a, b, hxu, max_eq_right (sub_nonpos.mpr (le_of_not_ge hvk)),
        not_lt_of_ge (le_of_not_ge hvk)]
    · simp [A, B, hxu]
  have hcs : HasCompactSupport A := hK.of_isClosed_subset (isClosed_tsupport _) <|
    closure_minimal (fun x hx => by
      by_contra hn
      exact hx (hzero x hn).1) hK.isClosed
  have hts : tsupport A ⊆ cuadrado := (closure_minimal (fun x hx => by
    by_contra hn
    exact hx (hzero x hn).1) hK.isClosed).trans hKU
  have hw := (((mem_W12_iff_hasWeakFDerivOn cuadrado_abierto e).1 he).congr_ae
    hvrep EventuallyEq.rfl).sub_const k |>.posPart
  have hweak : HasWeakFDerivOn cuadradoOpens A (fun x => innerSL ℝ (B x)) volume := by
    refine hw.congr_ae hAae.symm ?_
    filter_upwards [hBae] with x hx
    rw [hx]
    change (if 0 < v x - k then innerSL ℝ (gradL e x) else 0) =
      innerSL ℝ (if k < v x then gradL e x else 0)
    by_cases h : k < v x
    · simp [h, sub_pos.mpr h]
    · simp [h]
  have hglobal := hweak.top_of_forall_notMem_eq_zero hK hKU
    (fun x hx => (hzero x hx).1) (fun x hx => by simp [(hzero x hx).2])
  refine ⟨_, mem_H01_of_hasCompactSupport cuadrado_abierto hglobal hAm hBm hcs hts, ?_, ?_⟩
  · exact ((hAm.mono_measure Measure.restrict_le_self).coeFn_toLp).trans hAae
  · exact ((hBm.mono_measure Measure.restrict_le_self).coeFn_toLp).trans hBae

/-- Un elemento de H¹ con representante continuo hasta la frontera y nulo
allí pertenece a H₀¹. El argumento usa truncaciones de nivel positivo. -/
theorem continuo_cero_frontera_mem_H01
    (e : H1Graph (volume : Measure Plano) cuadrado) (he : e ∈ W12 volume cuadrado)
    {v : Plano → ℝ} (hv : ContinuousOn v (closure cuadrado))
    (hvrep : ⇑(fnL e) =ᵐ[volumenPoisson] v) (hz : EqOn v 0 (frontier cuadrado)) :
    e ∈ H01 (volume : Measure Plano) cuadrado := by
  classical
  let g : Plano → Plano := gradL e
  let a (n : ℕ) (x : Plano) := max (v x - ancho n) 0 - max (-v x - ancho n) 0
  let b (n : ℕ) (x : Plano) :=
    (if ancho n < v x then g x else 0) + (if ancho n < -v x then g x else 0)
  have hvneg : ⇑(fnL (-e)) =ᵐ[volumenPoisson] (-v) := by
    rw [map_neg]
    exact (Lp.coeFn_neg _).trans hvrep.neg
  have hzneg : EqOn (-v) 0 (frontier cuadrado) := fun x hx => by simp [hz hx]
  choose p hp hpv hpg using fun n => truncacion_positiva_mem_H01 e he hv hvrep hz (ancho_pos n)
  choose q hq hqv hqg using fun n => truncacion_positiva_mem_H01 (-e)
    (Submodule.neg_mem _ he) hv.neg hvneg hzneg (ancho_pos n)
  have ha (n : ℕ) : ⇑(fnL (p n - q n)) =ᵐ[volumenPoisson] a n := by
    rw [map_sub]
    exact (Lp.coeFn_sub _ _).trans ((hpv n).sub (hqv n))
  have hb (n : ℕ) : ⇑(gradL (p n - q n)) =ᵐ[volumenPoisson] b n := by
    rw [map_sub]
    have hneg : ⇑(gradL (-e)) =ᵐ[volumenPoisson] (-g) := by
      rw [map_neg]
      exact Lp.coeFn_neg _
    filter_upwards [Lp.coeFn_sub (gradL (p n)) (gradL (q n)), hpg n, hqg n, hneg] with x h hx hy hn
    rw [h, Pi.sub_apply, hx, hy, hn]
    dsimp [b, g]
    split_ifs <;> simp
  have hvL : MemLp v 2 volumenPoisson := (Lp.memLp (fnL e)).ae_eq hvrep
  have hgL : MemLp g 2 volumenPoisson := Lp.memLp _
  have hva : Tendsto (fun n => eLpNorm (a n - v) 2 volumenPoisson) atTop (𝓝 0) := by
    apply convergencia_truncacion_L2
      (fun n => ((Lp.memLp (fnL (p n - q n))).ae_eq (ha n)).aestronglyMeasurable)
      hvL.aestronglyMeasurable hvL
    · intro n
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        have hn := (ancho_pos n).le
        dsimp [a]
        rcases le_total 0 (v x) with hx | hx
        · rw [max_eq_right (by linarith : -v x - ancho n ≤ 0), sub_zero, abs_of_nonneg hx]
          apply abs_le.mpr
          exact ⟨by linarith [le_max_right (v x - ancho n) 0],
            by linarith [max_le (sub_le_self _ hn) hx]⟩
        · rw [max_eq_right (by linarith : v x - ancho n ≤ 0), zero_sub,
            abs_of_nonpos hx]
          apply abs_le.mpr
          exact ⟨by linarith [max_le (sub_le_self (-v x) hn) (neg_nonneg.mpr hx)],
            by linarith [le_max_right (-v x - ancho n) 0]⟩
    · refine Eventually.of_forall fun x => ?_
      have hpos : Tendsto (fun n => max (v x - ancho n) 0) atTop (𝓝 (max (v x - 0) 0)) :=
        (tendsto_const_nhds.sub ancho_tendsto_cero).max tendsto_const_nhds
      have hneg : Tendsto (fun n => max (-v x - ancho n) 0) atTop (𝓝 (max (-v x - 0) 0)) :=
        (tendsto_const_nhds.sub ancho_tendsto_cero).max tendsto_const_nhds
      have hid : max (v x) 0 - max (-v x) 0 = v x := by
        rcases le_total 0 (v x) with hx | hx
        · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
        · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), zero_sub, neg_neg]
      simpa only [a, sub_zero, hid] using
        (hpos.sub hneg : Tendsto (a · x) atTop
          (𝓝 (max (v x - 0) 0 - max (-v x - 0) 0)))
  have hzero : ∀ᵐ x ∂volumenPoisson, v x = 0 → g x = 0 := by
    filter_upwards [ae_gradL_eq_zero_of_fnL_eq cuadrado_abierto he 0, hvrep] with x hx hrep
    exact fun h => hx (hrep.trans h)
  have hvb : Tendsto (fun n => eLpNorm (b n - g) 2 volumenPoisson) atTop (𝓝 0) := by
    apply convergencia_truncacion_L2
      (fun n => ((Lp.memLp (gradL (p n - q n))).ae_eq (hb n)).aestronglyMeasurable)
      hgL.aestronglyMeasurable hgL
    · intro n
      exact Eventually.of_forall fun x => by
        have hk := ancho_pos n
        dsimp [b]
        split_ifs with h₁ h₂ h₂
        · exfalso
          linarith
        · simp
        · simp
        · simp
    · filter_upwards [hzero] with x hx
      apply tendsto_const_nhds.congr'
      rcases lt_trichotomy 0 (v x) with hpv | heq | hnv
      · filter_upwards [ancho_tendsto_cero.eventually (gt_mem_nhds hpv)] with n hn
        simp [b, hn, show ¬ancho n < -v x by linarith [ancho_pos n]]
      · exact Eventually.of_forall fun n => by simp [b, hx heq.symm]
      · have hpv : 0 < -v x := neg_pos.mpr hnv
        filter_upwards [ancho_tendsto_cero.eventually (gt_mem_nhds hpv)] with n hn
        simp [b, hn, show ¬ancho n < v x by linarith [ancho_pos n]]
  have hlim := tendsto_mk_of_tendsto_eLpNorm hvL hgL ha hb hva hvb
  have hval : hvL.toLp v = fnL e := by
    apply Lp.ext
    exact hvL.coeFn_toLp.trans hvrep.symm
  have hgrad : hgL.toLp g = gradL e := Lp.toLp_coeFn _ _
  rw [hval, hgrad, mk_fnL_gradL] at hlim
  exact isClosed_H01.mem_of_tendsto hlim (Eventually.of_forall fun n => Submodule.sub_mem _ (hp n) (hq n))

theorem frontera_puntual_igual_implica_error_H01
    (h u : H1Graph (volume : Measure Plano) cuadrado)
    (hh : h ∈ W12 volume cuadrado) (hu : u ∈ W12 volume cuadrado)
    {hc uc : Plano → ℝ}
    (hcont : ContinuousOn hc (closure cuadrado)) (ucont : ContinuousOn uc (closure cuadrado))
    (hrep : ⇑(fnL h) =ᵐ[volumenPoisson] hc) (urep : ⇑(fnL u) =ᵐ[volumenPoisson] uc)
    (hfr : EqOn hc uc (frontier cuadrado)) : h - u ∈ H01 (volume : Measure Plano) cuadrado := by
  refine continuo_cero_frontera_mem_H01 _ (Submodule.sub_mem _ hh hu) (hcont.sub ucont) ?_ ?_
  · rw [map_sub]
    exact (Lp.coeFn_sub _ _).trans (hrep.sub urep)
  · intro x hx
    exact sub_eq_zero.mpr (hfr hx)

theorem grafoSuaveCuadrado_error_mem_H01 (h u : CandidatoPoisson)
    (hfr : EqOn h.val u.val (frontier cuadrado)) :
    grafoSuaveCuadrado h - grafoSuaveCuadrado u ∈ H01 (volume : Measure Plano) cuadrado :=
  frontera_puntual_igual_implica_error_H01 _ _
    (grafoSuaveCuadrado_mem_W12 h) (grafoSuaveCuadrado_mem_W12 u)
    h.property.continuous.continuousOn u.property.continuous.continuousOn
    (grafoSuaveCuadrado_fnL_ae h) (grafoSuaveCuadrado_fnL_ae u) hfr

#check continuo_cero_frontera_mem_H01
#print axioms continuo_cero_frontera_mem_H01
#print axioms frontera_puntual_igual_implica_error_H01
#print axioms grafoSuaveCuadrado_error_mem_H01

end TesisPINN
