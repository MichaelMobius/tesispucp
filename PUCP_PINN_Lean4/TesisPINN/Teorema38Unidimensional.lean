import TesisPINN.Teorema34Unidimensional
import TesisPINN.Teorema38Dimensional

/-! Pérdida y límites de T3.8 en un intervalo con extremos observados. -/

noncomputable section

namespace TesisPINN

open Set MeasureTheory Filter Asymptotics
open scoped Topology

theorem cotas_minimo_unidimensional {H : Type*} {m : ℕ} (op : OperadoresPINN1D H)
    (a b lr lb w R : ℝ) (xs : Fin m → ℝ) (Hm : Set H) (h v : H)
    (hlr : 0 ≤ lr) (hlb : 0 ≤ lb) (hw : 0 < w)
    (hmin : IsMinOn (op.funcional xs a b lr lb w) Hm h)
    (hv : v ∈ Hm) (hzero : op.perdidaEmpirica xs a b lr lb v = 0)
    (hR : op.seminormaL v ^ 2 ≤ R) :
    op.seminormaL h ^ 2 ≤ R ∧ op.funcional xs a b lr lb w h ≤ w * R := by
  have hJ : op.funcional xs a b lr lb w h ≤ w * R := calc
    _ ≤ op.funcional xs a b lr lb w v := hmin hv
    _ = w * op.seminormaL v ^ 2 := by simp [OperadoresPINN1D.funcional, hzero]
    _ ≤ _ := mul_le_mul_of_nonneg_left hR hw.le
  exact ⟨regularidad_controlada w _ _ _ hw
    (add_nonneg (op.perdidaEmpiricaInterior_nonneg xs hlr h) (op.perdidaFrontera_nonneg hlb h))
    hJ, hJ⟩

theorem perdida_minimo_unidimensional_de_cota34 {H : Type*} {m : ℕ}
    (op : OperadoresPINN1D H) (μ : Measure ℝ) (a b lr lb c C α Sf R : ℝ)
    (xs : Fin m → ℝ) (Hm : Set H) (h v : H)
    (hm : 0 < m) (hc : 0 < c) (hlr : 0 < lr) (hlb : 0 ≤ lb) :
    let r := radio34Unidimensional c m
    let F := factor34Unidimensional m C r
    let w := peso34Unidimensional m C r lr α
    IsMinOn (op.funcional xs a b lr lb w) Hm h →
    v ∈ Hm → op.perdidaEmpirica xs a b lr lb v = 0 → op.seminormaL v ^ 2 ≤ R →
    (op.perdidaPoblacional μ a b lr lb h ≤ F * op.funcional xs a b lr lb w h +
        3 * lr * c ^ (-(2 * α)) * Sf ^ 2 * (m : ℝ) ^ (-α)) →
    op.perdidaPoblacional μ a b lr lb h ≤
      (3 * lr * c ^ (-(2 * α)) * (R + Sf ^ 2)) * (m : ℝ) ^ (-α) := by
  intro r F w hmin hv hz hR hcov
  have hr : 0 < r := radioRaizDimensional_pos _ _ _ _ zero_lt_one hc hm
  have hJ := (cotas_minimo_unidimensional op a b lr lb w R xs Hm h v hlr.le hlb
    (peso34Unidimensional_pos _ _ _ _ _ hr hlr) hmin hv hz hR).2
  have h := mul_le_mul_of_nonneg_left hJ (factor34Unidimensional_pos m C r).le
  have he : F * w = 3 * lr * r ^ (2 * α) := factor_peso34Unidimensional _ _ _ _ _
  rw [← mul_assoc, he] at h
  have hp : r ^ (2 * α) = c ^ (-(2 * α)) * (m : ℝ) ^ (-α) :=
    radio34Unidimensional_potencia _ _ _ hc hm
  rw [hp] at h
  linarith only [h, hcov]

/-- T3.8 en muestra finita sobre el mismo evento que (3.12). -/
theorem teorema38_unidimensional_evento {Ω H : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b ε₀ : ℝ) (hab : a < b) (dm : DatosMasaDimensional μ (Ioo a b) 1 1 ε₀)
    (Z : Muestreo38 P μ) (op : OperadoresPINN1D H) (Hm : Set H)
    (m : ℕ) (hm : 0 < m) (lr lb α Sf : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (hsmall : radio34Unidimensional dm.c m ≤ ε₀) (hHolder : op.CotasHolder Hm a b α Sf) :
    let w := peso34Unidimensional m dm.C (radio34Unidimensional dm.c m) lr α
    ∃ A : Set Ω, MeasurableSet A ∧ 1 - falloRaiz34 m ≤ P.real A ∧
      ∀ ω ∈ A, ∀ (h v : H) (R : ℝ),
        let xs := fun i : Fin m => Z.Z i ω
        h ∈ Hm → IsMinOn (op.funcional xs a b lr lb w) Hm h →
        v ∈ Hm → op.perdidaEmpirica xs a b lr lb v = 0 → op.seminormaL v ^ 2 ≤ R →
        op.perdidaPoblacional μ a b lr lb h ≤
          (3 * lr * dm.c ^ (-(2 * α)) * (R + Sf ^ 2)) * (m : ℝ) ^ (-α) := by
  intro w
  obtain ⟨_, A, hA, hp, hc⟩ := teorema34_unidimensional P μ a b ε₀ hab dm Z op Hm m hm
    lr lb α Sf hlr hlb hα hsmall hHolder
  refine ⟨A, hA, hp, fun ω hω h v R hh hmin hv hz hR => ?_⟩
  exact perdida_minimo_unidimensional_de_cota34 op μ a b lr lb dm.c dm.C α Sf R _ Hm h v
    hm dm.c_pos hlr hlb.le hmin hv hz hR ((hc ω hω).2.2 h hh)

theorem max_residuo_extremos_le_raiz {H : Type*} (op : OperadoresPINN1D H)
    (μ : Measure ℝ) (a b lr lb : ℝ) (hlr : 0 ≤ lr) (hlb : 0 < lb) (h : H) :
    max |op.residuoFrontera h a| |op.residuoFrontera h b| ≤
      Real.sqrt (2 / lb) * Real.sqrt (op.perdidaPoblacional μ a b lr lb h) := by
  have hp : 0 ≤ op.perdidaPoblacional μ a b lr lb h := by
    exact add_nonneg (mul_nonneg hlr (integral_nonneg fun _ => sq_nonneg _))
      (op.perdidaFrontera_nonneg hlb.le h)
  have hcomp : op.perdidaFrontera a b lb h ≤ op.perdidaPoblacional μ a b lr lb h :=
    le_add_of_nonneg_left (mul_nonneg hlr (integral_nonneg fun _ => sq_nonneg _))
  have ht (x : ℝ) (hx : op.residuoFrontera h x ^ 2 ≤
      op.residuoFrontera h a ^ 2 + op.residuoFrontera h b ^ 2) :
      |op.residuoFrontera h x| ≤ Real.sqrt (2 / lb) * Real.sqrt (op.perdidaPoblacional μ a b lr lb h) := by
    rw [← Real.sqrt_mul (div_nonneg (by norm_num) hlb.le)]
    apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg (div_nonneg (by norm_num) hlb.le) hp)).2
    rw [sq_abs]
    calc
      _ ≤ (2 * op.perdidaPoblacional μ a b lr lb h) / lb := by
        apply (le_div_iff₀ hlb).2
        have hm := (mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ lb / 2)).trans hcomp
        unfold OperadoresPINN1D.perdidaFrontera at hm
        linarith only [hm]
      _ = _ := by ring
  exact max_le (ht a (le_add_of_nonneg_right (sq_nonneg _)))
    (ht b (le_add_of_nonneg_left (sq_nonneg _)))

/-- T3.8 unidimensional, con un único evento casi seguro para la pérdida,
el residuo interior y los dos valores de frontera. -/
theorem teorema38_unidimensional {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b ε₀ : ℝ) (hε : 0 < ε₀) (dm : DatosMasaDimensional μ (Ioo a b) 1 1 ε₀)
    (Z : Muestreo38 P μ) (op : OperadoresPINN1D H) (m : ℕ → ℕ) (hm : ∀ n, 0 < m n)
    (hg : ∀ᶠ n in atTop, n ≤ m n) (lr lb α Sf : ℝ)
    (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (Hm : ℕ → Set H) (h v : ∀ n, Ω → Hm n)
    (_hmeas : ∀ n, Measurable (fun ω => (h n ω : H)))
    (_vmeas : ∀ n, Measurable (fun ω => (v n ω : H)))
    (hHolder : ∀ n, op.CotasHolder (Hm n) a b α Sf) :
    let w := fun n => peso34Unidimensional (m n) dm.C (radio34Unidimensional dm.c (m n)) lr α
    (∀ᵐ ω ∂P, ∃ R : ℝ, 0 ≤ R ∧ ∀ n,
      let xs := fun i : Fin (m n) => Z.Z i ω
      IsMinOn (op.funcional xs a b lr lb (w n)) (Hm n) (h n ω : H) ∧
      op.perdidaEmpirica xs a b lr lb (v n ω : H) = 0 ∧ op.seminormaL (v n ω : H) ^ 2 ≤ R) →
    ∀ᵐ ω ∂P,
      let loss := fun n => op.perdidaPoblacional μ a b lr lb (h n ω : H)
      let er := fun n x => op.L (h n ω : H) x - op.f x
      let ea := fun n => op.residuoFrontera (h n ω : H) a
      let eb := fun n => op.residuoFrontera (h n ω : H) b
      let emax := fun n => max |ea n| |eb n|
      (loss =O[atTop] fun n => (m n : ℝ) ^ (-α)) ∧
      (Tendsto (fun n => supResiduo (Ioo a b) (er n)) atTop (𝓝 0) ∧
        ((fun n => supResiduo (Ioo a b) (er n)) =O[atTop]
          fun n => (m n : ℝ) ^ (-(α ^ 2 / (2 * α + 1))))) ∧
      (Tendsto ea atTop (𝓝 0) ∧ Tendsto eb atTop (𝓝 0) ∧ Tendsto emax atTop (𝓝 0)) ∧
      ((ea =O[atTop] fun n => (m n : ℝ) ^ (-(α / 2))) ∧
       (eb =O[atTop] fun n => (m n : ℝ) ^ (-(α / 2))) ∧
       (emax =O[atTop] fun n => (m n : ℝ) ^ (-(α / 2)))) := by
  intro w hvar
  have hTop := tendsto_atTop_mono' atTop hg tendsto_id
  have hsmall := radioRaizDimensional_eventual 1 dm.c 1 ε₀ m zero_lt_one dm.c_pos zero_lt_one hε hm hTop
  have hcov := cobertura_raiz_dimensional_ae P μ Z (Ioo a b) 1 1 ε₀ dm le_rfl zero_lt_one hε m hm hg
  have hsup := muestras_en_soporte_ae P μ Z.Z (Ioo a b) dm.concentrada Z.medible Z.ley
  filter_upwards [hvar, hcov, hsup] with ω hvarω hω hs
  obtain ⟨R, hR, hvarω⟩ := hvarω
  dsimp only
  let loss := fun n => op.perdidaPoblacional μ a b lr lb (h n ω : H)
  let er := fun n x => op.L (h n ω : H) x - op.f x
  let ea := fun n => op.residuoFrontera (h n ω : H) a
  let eb := fun n => op.residuoFrontera (h n ω : H) b
  let emax := fun n => max |ea n| |eb n|
  let escala := fun n => (m n : ℝ) ^ (-α)
  let C := 3 * lr * dm.c ^ (-(2 * α)) * (R + Sf ^ 2)
  have hE₀ (n : ℕ) : 0 ≤ ∫ x, er n x ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hs₀ (n : ℕ) : 0 ≤ escala n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hLos : ∀ᶠ n in atTop, loss n ≤ C * escala n := by
    filter_upwards [hω, hsmall] with n hc hr
    obtain ⟨hmin, hz, hR'⟩ := hvarω n
    have hh := cota34_unidimensional_bajo_cobertura μ a b ε₀ dm op (Hm n) (m n) (hm n)
      (fun i => Z.Z i ω) lr lb α Sf hlr hlb hα hr (hHolder n) (fun i => hs i) hc _ (h n ω).2
    exact perdida_minimo_unidimensional_de_cota34 op μ a b lr lb dm.c dm.C α Sf R _ _
      (h n ω : H) (v n ω : H) (hm n) dm.c_pos hlr hlb.le hmin (v n ω).2 hz hR' hh
  have hf₀ (n : ℕ) : 0 ≤ op.perdidaFrontera a b lb (h n ω : H) := op.perdidaFrontera_nonneg hlb.le _
  have hLossO : loss =O[atTop] escala := isBigO_de_cota_eventual _ _ C
    (hLos.mono fun n hn => ⟨add_nonneg (mul_nonneg hlr.le (hE₀ n)) (hf₀ n), hs₀ n, hn⟩)
  have hE := energia_isBigO_de_perdida μ er lr C hlr loss escala hs₀ hLos
    (fun n => le_add_of_nonneg_right (hf₀ n))
  have hSf := (hHolder 0).1
  have hcr := dm.c_pos
  have hInt := lema39_tasa μ (Ioo a b) dm.medible (Real.sqrt R + Sf) α
    (dm.c * (2 * 1)⁻¹ ^ (1 : ℝ)) 1 (2 * 1 * ε₀) (by positivity) hα
    (by positivity) (by positivity) (masa_bola_inferior_dimensional μ (Ioo a b) 1 dm.c 1 ε₀
      zero_lt_one dm.particiones) zero_lt_one α hα er m hTop
    (Eventually.of_forall fun n => ?_) hE
  swap
  · obtain ⟨hmin, hz, hRv⟩ := hvarω n
    have hr : 0 < radio34Unidimensional dm.c (m n) :=
      radioRaizDimensional_pos _ _ _ _ zero_lt_one hcr (hm n)
    have hreg := (cotas_minimo_unidimensional op a b lr lb (w n) R _ (Hm n) _ _
      hlr.le hlb.le (peso34Unidimensional_pos _ _ _ _ _ hr hlr) hmin (v n ω).2 hz hRv).1
    have hL := (hHolder n).2.2 _ (h n ω).2
    have hS := (Real.le_sqrt hL.1 hR).2 hreg
    refine ⟨op.residuoInterior_integrable μ a b α Sf dm.concentrada hα (Hm n)
      (hHolder n) _ (h n ω).2, fun x hx y hy => ?_⟩
    exact (holder_resta (Ioo a b) _ _ _ _ α hL.2 (hHolder n).2.1 x hx y hy).trans
      (mul_le_mul_of_nonneg_right (add_le_add_left hS _) (Real.rpow_nonneg dist_nonneg _))
  have hI : (fun n => supResiduo (Ioo a b) (er n)) =O[atTop]
      (fun n => (m n : ℝ) ^ (-(α ^ 2 / (2 * α + 1)))) := by
    simpa only [pow_two] using hInt
  have hScale : (fun n => Real.sqrt (escala n)) =
      (fun n => (m n : ℝ) ^ (-(α / 2))) := by
    funext n
    simp only [escala, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg (m n))]
    congr 1
    ring
  have hBR : emax =O[atTop] fun n => (m n : ℝ) ^ (-(α / 2)) := by
    have h := (hLossO.sqrt (Eventually.of_forall hs₀)).const_mul_left (Real.sqrt (2 / lb))
    rw [hScale] at h
    refine (isBigO_de_cota_eventual _ _ 1 (Eventually.of_forall fun n => ?_)).trans h
    exact ⟨(abs_nonneg _).trans (le_max_left _ _), by positivity,
      by rw [one_mul]; exact max_residuo_extremos_le_raiz op μ a b lr lb hlr.le hlb _⟩
  have hBRa : ea =O[atTop] emax := by
    apply isBigO_iff.mpr
    refine ⟨1, Eventually.of_forall fun n => ?_⟩
    have hn : 0 ≤ emax n := (abs_nonneg (ea n)).trans (le_max_left _ _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn, one_mul] using (le_max_left |ea n| |eb n|)
  have hBRb : eb =O[atTop] emax := by
    apply isBigO_iff.mpr
    refine ⟨1, Eventually.of_forall fun n => ?_⟩
    have hn : 0 ≤ emax n := (abs_nonneg (ea n)).trans (le_max_left _ _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn, one_mul] using (le_max_right |ea n| |eb n|)
  have hM : Tendsto (fun n => (m n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hTop
  have hiLim := hI.trans_tendsto ((tendsto_rpow_neg_atTop (by positivity)).comp hM)
  have hbLim := hBR.trans_tendsto ((tendsto_rpow_neg_atTop (by positivity)).comp hM)
  exact ⟨hLossO, ⟨hiLim, hI⟩,
    ⟨hBRa.trans_tendsto hbLim, hBRb.trans_tendsto hbLim, hbLim⟩,
    ⟨hBRa.trans hBR, hBRb.trans hBR, hBR⟩⟩

#check teorema38_unidimensional_evento
#check teorema38_unidimensional
#print axioms teorema38_unidimensional_evento
#print axioms max_residuo_extremos_le_raiz
#print axioms teorema38_unidimensional

end TesisPINN
