import TesisPINN.TasaPoblacional
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Masa local y convergencia uniforme del Teorema 3.8

La hipótesis de particiones se cuantifica sobre **todos** los radios
`0 < η ≤ ε₀`, conforme a la Hipótesis 3.2. Una sucesión discreta de
particiones no basta para obtener la cota local para todo radio.
-/

noncomputable section

namespace TesisPINN

open MeasureTheory Filter Asymptotics

/-- La parte geométrica y de masa mínima de la Hipótesis 3.2 para un
espacio de muestreo. La medibilidad y disjunción se registran aunque la
implicación local solo necesita cobertura, inclusión, diámetro y masa. -/
def ParticionesMinimas
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (U : Set X) (c s ε₀ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ ε₀ →
    ∃ K : ℕ, ∃ cells : Fin K → Set X,
      (∀ k, MeasurableSet (cells k)) ∧
      Pairwise (fun i j => Disjoint (cells i) (cells j)) ∧
      U ⊆ (⋃ k, cells k) ∧
      (∀ k, cells k ⊆ U) ∧
      (∀ k, c * η ^ s ≤ μ.real (cells k)) ∧
      (∀ k, ∀ x ∈ cells k, ∀ y ∈ cells k,
        dist x y ≤ Real.sqrt 2 * η)

/-- Lema 3.3 en su forma cuantitativa para `d=2`. La celda elegida está
en la bola **abierta** porque se usa la partición a escala `r/(2√2)`;
su diámetro es a lo sumo `r/2 < r`. -/
theorem masa_bola_inferior_de_particiones
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set X) (c s ε₀ : ℝ)
    (hε₀ : 0 < ε₀) (hpart : ParticionesMinimas μ U c s ε₀)
    (x : X) (hx : x ∈ U) (r : ℝ)
    (hr : 0 < r) (hr₀ : r ≤ 2 * Real.sqrt 2 * ε₀) :
    c * (r / (2 * Real.sqrt 2)) ^ s ≤
      μ.real (Metric.ball x r ∩ U) := by
  let η := r / (2 * Real.sqrt 2)
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  have hden : 0 < 2 * Real.sqrt 2 := by positivity
  have hη : 0 < η := div_pos hr hden
  have hη₀ : η ≤ ε₀ := (div_le_iff₀ hden).2 (by simpa only [mul_comm ε₀] using hr₀)
  obtain ⟨K, cells, _, _, hcover, hsubset, hmass, hdiam⟩ :=
    hpart η hη hη₀
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcover hx)
  have hcell : cells k ⊆ Metric.ball x r ∩ U := by
    intro y hy
    have hd : dist y x ≤ Real.sqrt 2 * η := hdiam k y hy x hk
    have hhalf : Real.sqrt 2 * η = r / 2 := by
      dsimp [η]
      field_simp [ne_of_gt hsqrt] <;> ring
    have hlt : dist y x < r := by
      rw [hhalf] at hd
      nlinarith
    exact ⟨hlt, hsubset k hy⟩
  exact (hmass k).trans (measureReal_mono hcell)

#print axioms TesisPINN.masa_bola_inferior_de_particiones

/-- Comparación a un radio admisible. El parámetro `A` controla la
raíz de la energía media en la bola mediante una cota de masa inferior. -/
theorem abs_le_holder_add_de_integral
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set X) (hU : MeasurableSet U)
    (f : X → ℝ) (hInt : Integrable (fun y => f y ^ 2) μ)
    (H α r M A : ℝ) (hH : 0 ≤ H) (hα : 0 < α) (hA : 0 ≤ A)
    (x : X) (hx : x ∈ U) (hM : 0 < M)
    (hMass : M ≤ μ.real (Metric.ball x r ∩ U))
    (hHolder : ∀ y ∈ U, ∀ z ∈ U, |f y - f z| ≤ H * dist y z ^ α)
    (hE : (∫ y, f y ^ 2 ∂μ) ≤ M * A ^ 2) :
    |f x| ≤ H * r ^ α + A := by
  by_contra! hn
  let D := |f x| - H * r ^ α
  have hD : A < D := by dsimp [D]; linarith
  have hD0 : 0 ≤ D := hA.trans hD.le
  let S := Metric.ball x r ∩ U
  have hS : MeasurableSet S := Metric.isOpen_ball.measurableSet.inter hU
  have hpt (y : X) (hy : y ∈ S) : D ^ 2 ≤ f y ^ 2 := by
    have hd : dist y x < r := hy.1
    have hinc := (hHolder y hy.2 x hx).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hd.le hα.le) hH)
    have ht := (le_abs_self (|f x| - |f y|)).trans
      (abs_abs_sub_abs_le_abs_sub (f x) (f y))
    rw [abs_sub_comm (f x) (f y)] at ht
    have hb : D ≤ |f y| := by dsimp [D]; linarith
    simpa only [sq_abs] using (sq_le_sq₀ hD0 (abs_nonneg _)).2 hb
  have hmono : (∫ _ in S, D ^ 2 ∂μ) ≤ ∫ y in S, f y ^ 2 ∂μ :=
    setIntegral_mono_on (integrable_const _).integrableOn hInt.integrableOn hS hpt
  have htotal := setIntegral_le_integral (s := S) hInt
    (Eventually.of_forall fun y => sq_nonneg (f y))
  have hconst : (∫ _ in S, D ^ 2 ∂μ) = μ.real S * D ^ 2 := by
    simp [integral_const, measureReal_def, Measure.restrict_apply]
  rw [hconst] at hmono
  have hlow := mul_le_mul_of_nonneg_right hMass (sq_nonneg D)
  have hstrict := mul_lt_mul_of_pos_left ((sq_lt_sq₀ hA hD0).2 hD) hM
  exact (not_lt_of_ge (hlow.trans (hmono.trans (htotal.trans hE)))) hstrict

#print axioms TesisPINN.abs_le_holder_add_de_integral

/-- Suprema puntual de los valores absolutos. Incluir cero permite usar
la misma definición para el conjunto vacío. -/
def supResiduo {X : Type*} (U : Set X) (f : X → ℝ) : ℝ :=
  sSup (insert 0 ((fun x => |f x|) '' U))

theorem supResiduo_le {X : Type*} (U : Set X) (f : X → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (h : ∀ x ∈ U, |f x| ≤ B) :
    0 ≤ supResiduo U f ∧ supResiduo U f ≤ B := by
  have hb : ∀ y ∈ insert (0 : ℝ) ((fun x => |f x|) '' U), y ≤ B := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact hB
    · obtain ⟨x, hx, rfl⟩ := hy
      exact h x hx
  exact ⟨le_csSup ⟨B, hb⟩ (Set.mem_insert _ _),
    csSup_le ⟨0, Set.mem_insert _ _⟩ hb⟩

theorem masa_bola_inferior_potencia
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set X) (c s ε₀ : ℝ)
    (hε₀ : 0 < ε₀) (hpart : ParticionesMinimas μ U c s ε₀)
    (x : X) (hx : x ∈ U) (r : ℝ)
    (hr : 0 < r) (hr₀ : r ≤ 2 * Real.sqrt 2 * ε₀) :
    (c * (2 * Real.sqrt 2)⁻¹ ^ s) * r ^ s ≤
      μ.real (Metric.ball x r ∩ U) := by
  have hm := masa_bola_inferior_de_particiones μ U c s ε₀ hε₀ hpart x hx r hr hr₀
  rw [div_eq_mul_inv, Real.mul_rpow hr.le (by positivity)] at hm
  convert hm using 1 <;> ring

/-- Cota a escala truncada. Si `r ≤ R` usa `r`, y si `R ≤ r` usa
el umbral geométrico `R`. La fórmula también vale con energía cero. -/
theorem supResiduo_le_radio_truncado
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set X) (hU : MeasurableSet U) (f : X → ℝ)
    (hInt : Integrable (fun x => f x ^ 2) μ)
    (H α κ s R r E : ℝ) (hH : 0 ≤ H) (hα : 0 < α)
    (hκ : 0 < κ) (hR : 0 < R) (hr : 0 < r) (hE : 0 ≤ E)
    (hmass : ∀ x ∈ U, ∀ t : ℝ, 0 < t → t ≤ R →
      κ * t ^ s ≤ μ.real (Metric.ball x t ∩ U))
    (hHolder : ∀ x ∈ U, ∀ y ∈ U, |f x - f y| ≤ H * dist x y ^ α)
    (hIntE : (∫ x, f x ^ 2 ∂μ) ≤ E) :
    supResiduo U f ≤ H * (min r R) ^ α +
      Real.sqrt (E / (κ * (min r R) ^ s)) := by
  let t := min r R
  let M := κ * t ^ s
  have ht : 0 < t := lt_min hr hR
  have hM : 0 < M := mul_pos hκ (Real.rpow_pos_of_pos ht s)
  have hE' : (∫ x, f x ^ 2 ∂μ) ≤ M * (Real.sqrt (E / M)) ^ 2 := by
    rw [Real.sq_sqrt (div_nonneg hE hM.le), mul_div_cancel₀ _ hM.ne']
    exact hIntE
  refine (supResiduo_le U f _ (by positivity) ?_).2
  intro x hx
  exact abs_le_holder_add_de_integral μ U hU f hInt H α t M
    (Real.sqrt (E / M)) hH hα (Real.sqrt_nonneg _) x hx hM
    (hmass x hx t ht (min_le_right _ _)) hHolder hE'

/-- Transferencia de una envolvente cuadrática `C m^(-β)`. El radio
se elige en función de la envolvente, incluso si la integral es cero. -/
theorem tasa_supResiduo_de_integral
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set X) (hU : MeasurableSet U) (f : ℕ → X → ℝ)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (α s β H C κ R : ℝ) (hα : 0 < α) (hs : 0 < s) (hβ : 0 < β)
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hκ : 0 < κ) (hR : 0 < R)
    (hmass : ∀ x ∈ U, ∀ r : ℝ, 0 < r → r ≤ R →
      κ * r ^ s ≤ μ.real (Metric.ball x r ∩ U))
    (hf : ∀ᶠ n in atTop,
      Integrable (fun x => f n x ^ 2) μ ∧
      (∀ x ∈ U, ∀ y ∈ U, |f n x - f n y| ≤ H * dist x y ^ α) ∧
      (∫ x, f n x ^ 2 ∂μ) ≤ C * (m n : ℝ) ^ (-β)) :
    Tendsto (fun n => supResiduo U (f n)) atTop (nhds 0) ∧
    (fun n => supResiduo U (f n)) =O[atTop]
      (fun n => (m n : ℝ) ^ (-(β * α / (2 * α + s)))) := by
  let d := 2 * α + s
  let q := β / d
  let A := Real.sqrt (C / κ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hq : 0 < q := div_pos hβ hd
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hA2 : A ^ 2 = C / κ := Real.sq_sqrt (div_nonneg hC hκ.le)
  have hmR : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hrad : Tendsto (fun n => (m n : ℝ) ^ (-q)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hq).comp hmR
  have hsmall := hrad.eventually (Iio_mem_nhds hR)
  have hpos := hm.eventually (eventually_ge_atTop (1 : ℕ))
  have heq : -(β * α / (2 * α + s)) = -(q * α) := by dsimp [q, d]; ring
  have hbnd : ∀ᶠ n in atTop,
      0 ≤ supResiduo U (f n) ∧
      supResiduo U (f n) ≤ (H + A) * (m n : ℝ) ^ (-(q * α)) := by
    filter_upwards [hf, hsmall, hpos] with n hn hsmallN hposN
    have hmn : 0 < (m n : ℝ) := Nat.cast_pos.mpr (by omega)
    let r := (m n : ℝ) ^ (-q)
    have hr : 0 < r := Real.rpow_pos_of_pos hmn _
    have hpow (a : ℝ) : r ^ a = (m n : ℝ) ^ (-q * a) :=
      (Real.rpow_mul hmn.le (-q) a).symm
    have hαpow : r ^ α = (m n : ℝ) ^ (-(q * α)) := by
      rw [hpow, neg_mul]
    have hE : (∫ x, f n x ^ 2 ∂μ) ≤ κ * r ^ s * (A * r ^ α) ^ 2 := by
      refine hn.2.2.trans_eq ?_
      have hqD : q * (2 * α + s) = β := by
        dsimp [q, d]
        field_simp [show 2 * α + s ≠ 0 from hd.ne']
      have hexp : -q * s + (-q * α) * 2 = -β := by nlinarith
      calc
        C * (m n : ℝ) ^ (-β) =
            (κ * A ^ 2) * ((m n : ℝ) ^ (-q * s) *
              (m n : ℝ) ^ ((-q * α) * 2)) := by
          rw [← Real.rpow_add hmn, hexp, hA2]
          field_simp [hκ.ne']
        _ = κ * r ^ s * (A * r ^ α) ^ 2 := by
          rw [hpow s, hpow α, Real.rpow_mul hmn.le (-q * α) 2, Real.rpow_two]
          ring
    apply supResiduo_le
    · positivity
    · intro x hx
      have h := abs_le_holder_add_de_integral μ U hU (f n) hn.1
        H α r (κ * r ^ s) (A * r ^ α) hH hα (by positivity)
        x hx (by positivity) (hmass x hx r hr (show r < R from hsmallN).le) hn.2.1 hE
      rw [hαpow] at h
      simpa only [add_mul] using h
  have ht : Tendsto (fun n => (m n : ℝ) ^ (-(q * α))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (mul_pos hq hα)).comp hmR
  constructor
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [mul_zero] using ht.const_mul (H + A))
      (hbnd.mono fun _ h => h.1) (hbnd.mono fun _ h => h.2)
  · rw [heq]
    apply isBigO_de_cota_eventual _ _ (H + A)
    exact hbnd.mono fun _ h => ⟨h.1, by positivity, h.2⟩

#print axioms TesisPINN.masa_bola_inferior_potencia
#print axioms TesisPINN.supResiduo_le_radio_truncado
#print axioms TesisPINN.tasa_supResiduo_de_integral

private theorem holder_resta
    {X : Type*} [PseudoMetricSpace X] (U : Set X) (L f : X → ℝ)
    (A B α : ℝ)
    (hL : ∀ x ∈ U, ∀ y ∈ U, |L x - L y| ≤ A * dist x y ^ α)
    (hf : ∀ x ∈ U, ∀ y ∈ U, |f x - f y| ≤ B * dist x y ^ α) :
    ∀ x ∈ U, ∀ y ∈ U, |(L x - f x) - (L y - f y)| ≤
      (A + B) * dist x y ^ α := by
  intro x hx y hy
  rw [show (L x - f x) - (L y - f y) = (L x - L y) - (f x - f y) by ring]
  exact (abs_sub _ _).trans (by rw [add_mul]; exact add_le_add (hL x hx y hy) (hf x hx y hy))

/-- (3.29) controla los incrementos de los dos residuos del minimizador. -/
theorem holder_residuos_minimizador
    {H X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] {mr mb : ℕ}
    (P : ProblemaPINN H X Y mr mb) (Hm : Set H) (U : Set X) (Γ : Set Y)
    (α Sf Sg R a : ℝ) (hR : 0 ≤ R) (ha : 0 < a)
    (haR : P.regularizadorR = a) (haB : P.regularizadorB = a)
    (hH : CotasHolder P Hm U Γ α Sf Sg)
    (h g : H) (hmin : P.EsMinimizadorGlobal Hm h)
    (hg : P.ComparadorExacto Hm g) (hgR : P.regularidadTotal g ≤ R) :
    (∀ x ∈ U, ∀ y ∈ U, |(P.L h x - P.f x) - (P.L h y - P.f y)| ≤
      (Real.sqrt R + Sf) * dist x y ^ α) ∧
    (∀ x ∈ Γ, ∀ y ∈ Γ, |(P.B h x - P.g x) - (P.B h y - P.g y)| ≤
      (Real.sqrt R + Sg) * dist x y ^ α) := by
  have hreg := (P.regularidad_minimizador_le_comparador Hm h g hmin hg a ha haR haB).trans hgR
  rcases hH with ⟨_, _, hclass, hf, hdataG⟩
  obtain ⟨hL0, hB0, hL, hB⟩ := hclass h hmin.1
  change (P.seminormaL h) ^ 2 + (P.seminormaB h) ^ 2 ≤ R at hreg
  have hsr : P.seminormaL h ≤ Real.sqrt R :=
    (sq_le_sq₀ hL0 (Real.sqrt_nonneg R)).1 (by rw [Real.sq_sqrt hR]; nlinarith)
  have hsb : P.seminormaB h ≤ Real.sqrt R :=
    (sq_le_sq₀ hB0 (Real.sqrt_nonneg R)).1 (by rw [Real.sq_sqrt hR]; nlinarith)
  constructor
  · apply holder_resta U (P.L h) P.f (Real.sqrt R) Sf α _ hf
    intro x hx y hy
    exact (hL x hx y hy).trans (mul_le_mul_of_nonneg_right hsr (by positivity))
  · apply holder_resta Γ (P.B h) P.g (Real.sqrt R) Sg α _ hdataG
    intro x hx y hy
    exact (hB x hx y hy).trans (mul_le_mul_of_nonneg_right hsb (by positivity))

/-- Para un índice fijo, mensurabilidad conjunta de operadores y
mensurabilidad de datos y selección implican mensurabilidad de la pérdida.
Los puntos empíricos se reemplazan en `problemaMuestral`, pero la pérdida
poblacional conserva los operadores, pesos y medidas de la base. -/
theorem measurable_perdidaPoblacional_seleccion
    {H X Y Ω : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Ω] {mr mb : ℕ}
    (P : ProblemaPINN H X Y mr mb) (h : Ω → H)
    (hh : Measurable h)
    (hL : Measurable (fun p : H × X => P.L p.1 p.2))
    (hB : Measurable (fun p : H × Y => P.B p.1 p.2))
    (hf : Measurable P.f) (hg : Measurable P.g) :
    Measurable (fun ω => P.perdidaPoblacional (h ω)) := by
  letI : IsProbabilityMeasure P.μr := ⟨P.μr_prob⟩
  letI : IsProbabilityMeasure P.μb := ⟨P.μb_prob⟩
  have hr : Measurable (fun p : Ω × X => (P.L (h p.1) p.2 - P.f p.2) ^ 2) :=
    ((hL.comp ((hh.comp measurable_fst).prodMk measurable_snd)).sub
      (hf.comp measurable_snd)).pow_const 2
  have hb : Measurable (fun p : Ω × Y => (P.B (h p.1) p.2 - P.g p.2) ^ 2) :=
    ((hB.comp ((hh.comp measurable_fst).prodMk measurable_snd)).sub
      (hg.comp measurable_snd)).pow_const 2
  exact (measurable_const.mul (hr.stronglyMeasurable.integral_prod_right' (ν := P.μr)).measurable).add
    (measurable_const.mul (hb.stronglyMeasurable.integral_prod_right' (ν := P.μb)).measurable)

#print axioms TesisPINN.holder_residuos_minimizador
#print axioms TesisPINN.measurable_perdidaPoblacional_seleccion

/-- Transferencia de (3.26) a (3.27) y (3.28) para los dos residuos.
`Pn` puede ser la familia de prefijos `problemaMuestral`. -/
theorem convergencia_y_tasas_uniformes_ae
    {Ω H X Y : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (P : Measure Ω) (mr mb : ℕ → ℕ) (hmr : Tendsto mr atTop atTop)
    (Pn : Ω → (n : ℕ) → ProblemaPINN H X Y (mr n) (mb n))
    (hm g : ℕ → Ω → H) (Hm : ℕ → Set H)
    (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (U : Set X) (Γ : Set Y) (hU : MeasurableSet U) (hΓ : MeasurableSet Γ)
    (cr cb ε₀ α Sf Sg lambdaR lambdaB : ℝ)
    (hcr : 0 < cr) (hcb : 0 < cb) (hε₀ : 0 < ε₀) (hα : 0 < α)
    (hSf : 0 ≤ Sf) (hSg : 0 ≤ Sg)
    (hlr : 0 < lambdaR) (hlb : 0 < lambdaB)
    (hpartR : ParticionesMinimas μr U cr 2 ε₀)
    (hpartB : ParticionesMinimas μb Γ cb 1 ε₀)
    (hbase : ∀ ω n, (Pn ω n).μr = μr ∧ (Pn ω n).μb = μb ∧
      (Pn ω n).lambdaR = lambdaR ∧ (Pn ω n).lambdaB = lambdaB)
    (hstats : ∀ᵐ ω ∂P, ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n in atTop,
      (Pn ω n).EsMinimizadorGlobal (Hm n) (hm n ω) ∧
      (Pn ω n).ComparadorExacto (Hm n) (g n ω) ∧
      (Pn ω n).regularidadTotal (g n ω) ≤ R ∧
      CotasHolder (Pn ω n) (Hm n) U Γ α Sf Sg ∧
      (Pn ω n).PoblacionIntegrable (hm n ω) ∧
      0 < (Pn ω n).regularizadorR ∧
      (Pn ω n).regularizadorB = (Pn ω n).regularizadorR)
    (h26 : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      (Pn ω n).perdidaPoblacional (hm n ω) ≤ C * (mr n : ℝ) ^ (-(α / 2))) :
    ∀ᵐ ω ∂P,
      let er := fun n x => (Pn ω n).L (hm n ω) x - (Pn ω n).f x
      let eb := fun n y => (Pn ω n).B (hm n ω) y - (Pn ω n).g y
      (Tendsto (fun n => supResiduo U (er n)) atTop (nhds 0) ∧
       Tendsto (fun n => supResiduo Γ (eb n)) atTop (nhds 0)) ∧
      ((fun n => supResiduo U (er n)) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α ^ 2 / (2 * (2 * α + 2))))) ∧
       (fun n => supResiduo Γ (eb n)) =O[atTop]
        (fun n => (mr n : ℝ) ^ (-(α ^ 2 / (2 * (2 * α + 1)))))) := by
  filter_upwards [hstats, h26] with ω hstat hrate
  obtain ⟨R, hR, hstat⟩ := hstat
  obtain ⟨C, hC, hrate⟩ := hrate
  let er := fun n x => (Pn ω n).L (hm n ω) x - (Pn ω n).f x
  let eb := fun n y => (Pn ω n).B (hm n ω) y - (Pn ω n).g y
  have hstep : ∀ᶠ n in atTop,
      (Integrable (fun x => er n x ^ 2) μr ∧
       (∀ x ∈ U, ∀ y ∈ U, |er n x - er n y| ≤ (Real.sqrt R + Sf) * dist x y ^ α) ∧
       (∫ x, er n x ^ 2 ∂μr) ≤ (C / lambdaR) * (mr n : ℝ) ^ (-(α / 2))) ∧
      (Integrable (fun y => eb n y ^ 2) μb ∧
       (∀ x ∈ Γ, ∀ y ∈ Γ, |eb n x - eb n y| ≤ (Real.sqrt R + Sg) * dist x y ^ α) ∧
       (∫ y, eb n y ^ 2 ∂μb) ≤ (C / lambdaB) * (mr n : ℝ) ^ (-(α / 2))) := by
    filter_upwards [hstat, hrate] with n hn hrateN
    obtain ⟨hmin, hg, hgR, hH, hInt, ha, haB⟩ := hn
    obtain ⟨hμr, hμb, hLambdaR, hLambdaB⟩ := hbase ω n
    have hHolder := holder_residuos_minimizador (Pn ω n) (Hm n) U Γ α Sf Sg
      R (Pn ω n).regularizadorR hR ha rfl haB hH (hm n ω) (g n ω) hmin hg hgR
    have hIr : Integrable (fun x => er n x ^ 2) μr := hμr ▸ hInt.1
    have hIb : Integrable (fun y => eb n y ^ 2) μb := hμb ▸ hInt.2
    have hEr : 0 ≤ ∫ x, er n x ^ 2 ∂μr := integral_nonneg fun _ => sq_nonneg _
    have hEb : 0 ≤ ∫ y, eb n y ^ 2 ∂μb := integral_nonneg fun _ => sq_nonneg _
    unfold ProblemaPINN.perdidaPoblacional at hrateN
    rw [hμr, hμb, hLambdaR, hLambdaB] at hrateN
    change lambdaR * (∫ x, er n x ^ 2 ∂μr) + lambdaB * (∫ y, eb n y ^ 2 ∂μb) ≤ _ at hrateN
    refine ⟨⟨hIr, hHolder.1, ?_⟩, ⟨hIb, hHolder.2, ?_⟩⟩
    · rw [div_mul_eq_mul_div₀]
      exact (le_div_iff₀ hlr).2 (by nlinarith [mul_nonneg hlb.le hEb])
    · rw [div_mul_eq_mul_div₀]
      exact (le_div_iff₀ hlb).2 (by nlinarith [mul_nonneg hlr.le hEr])
  have hr := tasa_supResiduo_de_integral μr U hU er mr hmr α 2 (α / 2)
    (Real.sqrt R + Sf) (C / lambdaR) (cr * (2 * Real.sqrt 2)⁻¹ ^ (2 : ℝ))
    (2 * Real.sqrt 2 * ε₀) hα (by norm_num) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (masa_bola_inferior_potencia μr U cr 2 ε₀ hε₀ hpartR) (hstep.mono fun _ h => h.1)
  have hb := tasa_supResiduo_de_integral μb Γ hΓ eb mr hmr α 1 (α / 2)
    (Real.sqrt R + Sg) (C / lambdaB) (cb * (2 * Real.sqrt 2)⁻¹ ^ (1 : ℝ))
    (2 * Real.sqrt 2 * ε₀) hα (by norm_num) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (masa_bola_inferior_potencia μb Γ cb 1 ε₀ hε₀ hpartB) (hstep.mono fun _ h => h.2)
  have hexp (s : ℝ) : -(α / 2 * α / (2 * α + s)) =
      -(α ^ 2 / (2 * (2 * α + s))) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hexp] at hr hb
  exact ⟨⟨hr.1, hb.1⟩, ⟨hr.2, hb.2⟩⟩

#print axioms TesisPINN.convergencia_y_tasas_uniformes_ae

end TesisPINN
