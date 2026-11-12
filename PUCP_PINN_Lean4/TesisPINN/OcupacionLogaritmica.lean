import TesisPINN.ConvergenciaUniforme

/-! Cobertura por ocupación en los radios logarítmicos del Lema 3.13. -/

noncomputable section

namespace TesisPINN

open MeasureTheory ProbabilityTheory Filter

/-- Escala auxiliar de (3.57). -/
def escalaAuxiliarLog (c s κ : ℝ) (m : ℕ) : ℝ :=
  (κ * Real.log (m : ℝ) / (c * (m : ℝ))) ^ (1 / s)

/-- Radio final de (3.57) para celdas de diámetro a lo sumo `D * η`. -/
def radioCoberturaLog (D c s κ : ℝ) (m : ℕ) : ℝ :=
  D * escalaAuxiliarLog c s κ m

/-- Mayorante de fallo de (3.58). -/
def mayoranteFalloLog (κ : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) ^ (1 - κ) / (κ * Real.log (m : ℝ))

private theorem log_nat_pos (m : ℕ) (hm : 3 ≤ m) : 0 < Real.log (m : ℝ) :=
  Real.log_pos (by exact_mod_cast (show 1 < m by omega))

theorem escalaAuxiliarLog_masa (c s κ : ℝ) (m : ℕ)
    (hc : 0 < c) (hs : 0 < s) (hκ : 0 < κ) (hm : 3 ≤ m) :
    c * escalaAuxiliarLog c s κ m ^ s = κ * Real.log (m : ℝ) / m := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hlog := log_nat_pos m hm
  unfold escalaAuxiliarLog
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hs.ne', Real.rpow_one]
  field_simp

/-- Los umbrales de partición y de uso del radio pueden ser distintos. -/
def RadioLogAdmisible (D c s κ η₀ r₀ : ℝ) (m : ℕ) : Prop :=
  3 ≤ m ∧ 0 < escalaAuxiliarLog c s κ m ∧ escalaAuxiliarLog c s κ m ≤ η₀ ∧
    κ * Real.log (m : ℝ) ≤ m ∧
    0 < radioCoberturaLog D c s κ m ∧ radioCoberturaLog D c s κ m ≤ r₀

/-- Los umbrales de (3.57) se alcanzan a lo largo de cualquier sucesión
de tamaños que tiende a infinito. -/
theorem radioLog_eventualmente_admisible (D c s κ η₀ r₀ : ℝ)
    (hD : 0 < D) (hc : 0 < c) (hs : 0 < s) (hκ : 0 < κ)
    (hη₀ : 0 < η₀) (hr₀ : 0 < r₀) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    ∀ᶠ n in atTop, RadioLogAdmisible D c s κ η₀ r₀ (m n) := by
  have hcast : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hlogDiv : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hmass : Tendsto (fun n => κ * Real.log (m n : ℝ) / (m n : ℝ)) atTop (nhds 0) := by
    simpa [mul_div_assoc] using (hlogDiv.comp hcast).const_mul κ
  have hbase : Tendsto (fun n => κ * Real.log (m n : ℝ) / (c * (m n : ℝ)))
      atTop (nhds 0) := by
    simpa [div_div, mul_comm c] using hmass.div_const c
  have hη : Tendsto (fun n => escalaAuxiliarLog c s κ (m n)) atTop (nhds 0) := by
    exact hbase.rpow_const_nhds_zero (show 0 < 1 / s by positivity)
  have hρ : Tendsto (fun n => radioCoberturaLog D c s κ (m n)) atTop (nhds 0) := by
    simpa [radioCoberturaLog] using hη.const_mul D
  filter_upwards [hm.eventually (eventually_ge_atTop (3 : ℕ)),
    hmass.eventually (Iio_mem_nhds zero_lt_one),
    hη.eventually (Iio_mem_nhds hη₀), hρ.eventually (Iio_mem_nhds hr₀)]
    with n hn hmassN hηN hρN
  have hmN : (0 : ℝ) < m n := Nat.cast_pos.mpr (by omega)
  have hlog := log_nat_pos (m n) hn
  have hηpos : 0 < escalaAuxiliarLog c s κ (m n) := by
    unfold escalaAuxiliarLog
    positivity
  exact ⟨hn, hηpos, hηN.le, by
    simpa using ((div_lt_iff₀ hmN).mp hmassN).le, mul_pos hD hηpos, hρN.le⟩

/-- Comparación con la p-serie de exponente `κ - 1`, incluso para
prefijos cuyos tamaños solo dominan a su índice eventualmente. -/
theorem sumable_mayoranteFalloLog_de_tamanos (κ : ℝ) (hκ : 2 < κ)
    (m : ℕ → ℕ) (hm : ∀ᶠ n in atTop, n ≤ m n) :
    Summable (fun n => mayoranteFalloLog κ (m n)) := by
  have hκpos : 0 < κ := by linarith
  have hp := (Real.summable_nat_rpow (p := 1 - κ)).2 (by linarith)
  have hmTop : Tendsto m atTop atTop := tendsto_atTop_mono' atTop hm tendsto_id
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  apply (hp.div_const κ).of_norm_bounded_eventually_nat
  filter_upwards [hm, eventually_ge_atTop (1 : ℕ),
    hlog.eventually (eventually_ge_atTop (1 : ℝ))] with n hmn hn hlogN
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hmn' : (n : ℝ) ≤ (m n : ℝ) := by exact_mod_cast hmn
  have hden : κ ≤ κ * Real.log (m n : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left (show 1 ≤ Real.log (m n : ℝ) from hlogN) hκpos.le
  have hnum : (m n : ℝ) ^ (1 - κ) ≤ (n : ℝ) ^ (1 - κ) :=
    Real.rpow_le_rpow_of_nonpos hn' hmn' (by linarith)
  unfold mayoranteFalloLog
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) (hκpos.le.trans hden))]
  exact (div_le_div_of_nonneg_left (by positivity) hκpos hden).trans
    (div_le_div_of_nonneg_right hnum hκpos.le)

section Muestreo

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (μ : Measure X) [IsProbabilityMeasure μ]
  (Z : ℕ → Ω → X)

theorem cardinal_particion_log {K : ℕ} (κ : ℝ) (m : ℕ)
    (hκ : 0 < κ) (hm : 3 ≤ m) (cells : Fin K → Set X)
    (hc : ∀ k, MeasurableSet (cells k))
    (hdisj : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (hmin : ∀ k, κ * Real.log (m : ℝ) / m ≤ μ.real (cells k)) :
    (K : ℝ) ≤ (m : ℝ) / (κ * Real.log (m : ℝ)) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have ht : 0 < κ * Real.log (m : ℝ) := mul_pos hκ (log_nat_pos m hm)
  have hcard := cardinal_por_masa_minima μ cells hc hdisj _ hmin
  apply (le_div_iff₀ ht).2
  rw [← mul_div_assoc] at hcard
  simpa using (div_le_iff₀ hm').1 hcard

/-- Cota de (3.58) para el complemento del evento medible de ocupación. -/
theorem falloOcupacion_le_escala_log {K : ℕ} (κ : ℝ) (m : ℕ)
    (hκ : 0 < κ) (hm : 3 ≤ m) (cells : Fin K → Set X)
    (hc : ∀ k, MeasurableSet (cells k))
    (hdisj : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ)
    (hmin : ∀ k, κ * Real.log (m : ℝ) / m ≤ μ.real (cells k)) :
    P.real (todasCeldasOcupadas Z m cells)ᶜ ≤ mayoranteFalloLog κ m := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have ht : 0 < κ * Real.log (m : ℝ) := mul_pos hκ (log_nat_pos m hm)
  have hexp : -(m : ℝ) * (κ * Real.log (m : ℝ) / m) = Real.log (m : ℝ) * (-κ) := by
    field_simp [hm'.ne']
  have hfail := medidaReal_falloOcupacion_le_exp P μ Z m cells hc
    hZ hIndep hLaw _ (div_nonneg ht.le hm'.le) hmin
  rw [hexp, ← Real.rpow_def_of_pos hm'] at hfail
  calc
    _ ≤ (K : ℝ) * (m : ℝ) ^ (-κ) := hfail
    _ ≤ ((m : ℝ) / (κ * Real.log (m : ℝ))) * (m : ℝ) ^ (-κ) :=
      mul_le_mul_of_nonneg_right (cardinal_particion_log μ κ m hκ hm cells hc hdisj hmin)
        (by positivity)
    _ = mayoranteFalloLog κ m := by
      unfold mayoranteFalloLog
      rw [sub_eq_add_neg, Real.rpow_add hm', Real.rpow_one, div_mul_eq_mul_div₀]

end Muestreo

/-- Particiones de masa mínima en todas las escalas con factor de
diámetro `D`, que en dimensión ambiente `d` puede ser `√d`. -/
def ParticionesOcupacionLog
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (U : Set X) (D c s η₀ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∃ K : ℕ, ∃ cells : Fin K → Set X,
      (∀ k, MeasurableSet (cells k)) ∧
      Pairwise (fun i j => Disjoint (cells i) (cells j)) ∧
      U ⊆ (⋃ k, cells k) ∧
      (∀ k, cells k ⊆ U) ∧
      (∀ k, c * η ^ s ≤ μ.real (cells k)) ∧
      (∀ k, ∀ x ∈ cells k, ∀ y ∈ cells k, dist x y ≤ D * η)

theorem ParticionesMinimas.particionesOcupacionLog
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {μ : Measure X} {U : Set X} {c s η₀ : ℝ}
    (h : ParticionesMinimas μ U c s η₀) :
    ParticionesOcupacionLog μ U (Real.sqrt 2) c s η₀ := h

/-- Lema 3.13. Incluye el evento finito por tamaño admisible y la cobertura
eventual sobre una misma sucesión i.i.d. de la que se toman los prefijos. -/
theorem lema313_cobertura_logaritmica
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [PseudoMetricSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → X) (hZ : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ)
    (U : Set X) (D c s κ η₀ r₀ : ℝ)
    (hD : 0 < D) (hc : 0 < c) (hs : 0 < s) (hκ : 2 < κ)
    (hη₀ : 0 < η₀) (hr₀ : 0 < r₀)
    (hpart : ParticionesOcupacionLog μ U D c s η₀)
    (m : ℕ → ℕ) (hm : ∀ᶠ n in atTop, n ≤ m n) :
    (∀ k : ℕ, RadioLogAdmisible D c s κ η₀ r₀ k →
      ∃ K : ℕ, ∃ cells : Fin K → Set X,
        MeasurableSet (todasCeldasOcupadas Z k cells)ᶜ ∧
        P.real (todasCeldasOcupadas Z k cells)ᶜ ≤ mayoranteFalloLog κ k ∧
        ∀ ω ∈ todasCeldasOcupadas Z k cells,
          MuestrasCubren U (fun i : Fin k => Z i ω) (radioCoberturaLog D c s κ k)) ∧
    (∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      RadioLogAdmisible D c s κ η₀ r₀ (m n) ∧
      MuestrasCubren U (fun i : Fin (m n) => Z i ω) (radioCoberturaLog D c s κ (m n))) := by
  have hκpos : 0 < κ := by linarith
  have hadm := radioLog_eventualmente_admisible D c s κ η₀ r₀ hD hc hs hκpos hη₀ hr₀ m
    (tendsto_atTop_mono' atTop hm tendsto_id)
  have hselect (k : ℕ) (hk : RadioLogAdmisible D c s κ η₀ r₀ k) :
      ∃ K : ℕ, ∃ cells : Fin K → Set X,
        MeasurableSet (todasCeldasOcupadas Z k cells)ᶜ ∧
        P.real (todasCeldasOcupadas Z k cells)ᶜ ≤ mayoranteFalloLog κ k ∧
        U ⊆ (⋃ i, cells i) ∧
        (∀ i, ∀ x ∈ cells i, ∀ y ∈ cells i,
          dist x y ≤ radioCoberturaLog D c s κ k) := by
    obtain ⟨K, cells, hmCells, hdisj, hcover, _, hmass, hdiam⟩ :=
      hpart _ hk.2.1 hk.2.2.1
    have hmassLog (i : Fin K) : κ * Real.log (k : ℝ) / k ≤ μ.real (cells i) := by
      rw [← escalaAuxiliarLog_masa c s κ k hc hs hκpos hk.1]
      exact hmass i
    exact ⟨K, cells, (todasCeldasOcupadas_measurable Z k cells hmCells hZ).compl,
      falloOcupacion_le_escala_log P μ Z κ k hκpos hk.1 cells hmCells hdisj hZ hIndep hLaw
        hmassLog, hcover, hdiam⟩
  constructor
  · intro k hk
    obtain ⟨K, cells, hmeas, hbound, hcover, hdiam⟩ := hselect k hk
    exact ⟨K, cells, hmeas, hbound,
      ocupacion_implica_cobertura Z k U cells _ hcover hdiam⟩
  · obtain ⟨N, hN⟩ := eventually_atTop.mp hadm
    let mt := fun n => m (n + N)
    choose K cells hcells using fun n => hselect (mt n) (hN (n + N) (by omega))
    have hmt : ∀ᶠ n in atTop, n ≤ mt n :=
      ((tendsto_add_atTop_nat N).eventually hm).mono (fun n hn => by dsimp [mt]; omega)
    have hsum := tsum_fallos_ne_top_de_mayorante P Z K mt cells _
      (sumable_mayoranteFalloLog_de_tamanos κ hκ mt hmt) (fun n => (hcells n).2.1)
    have hcov := cobertura_eventual_casi_segura P Z K mt cells
      (fun _ => U) (fun n => radioCoberturaLog D c s κ (mt n))
      (fun n => (hcells n).2.2.1) (fun n => (hcells n).2.2.2) hsum
    filter_upwards [hcov] with ω hω
    refine hadm.and ?_
    rw [← map_add_atTop_eq_nat N]
    exact hω

#check escalaAuxiliarLog_masa
#check radioLog_eventualmente_admisible
#check cardinal_particion_log
#check falloOcupacion_le_escala_log
#check sumable_mayoranteFalloLog_de_tamanos
#check lema313_cobertura_logaritmica
#print axioms escalaAuxiliarLog_masa
#print axioms radioLog_eventualmente_admisible
#print axioms cardinal_particion_log
#print axioms falloOcupacion_le_escala_log
#print axioms sumable_mayoranteFalloLog_de_tamanos
#print axioms lema313_cobertura_logaritmica

end TesisPINN
