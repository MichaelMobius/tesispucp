import TesisPINN.Proposicion315

/-! Proposición 3.11. Pérdida interior de Poisson con radio en escala raíz. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Filter Asymptotics Topology EllipticPdes EllipticPdes.H1Graph
open scoped Distributions

def radioRaizCuadrado (m : ℕ) : ℝ :=
  Real.sqrt 2 * escalaAuxiliarRaiz (1 / 9) 2 m

def factorRaizInterior (m : ℕ) : ℝ := (27 * Real.pi / 2) * Real.sqrt (m : ℝ)

def pesoRaizInterior (α : ℝ) (m : ℕ) : ℝ :=
  3 * radioRaizCuadrado m ^ (2 * α) / factorRaizInterior m

private theorem constanteRaizCuadrado :
    (1 / 9 : ℝ) ^ (-(1 / 2 : ℝ)) = 3 := by
  rw [Real.rpow_neg_eq_inv_rpow, ← Real.sqrt_eq_rpow]
  have h : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [h]

theorem radioRaizCuadrado_eq (m : ℕ) (hm : 0 < m) :
    radioRaizCuadrado m = 3 * Real.sqrt 2 * (m : ℝ) ^ (-(1 / 4 : ℝ)) := by
  rw [radioRaizCuadrado, escalaAuxiliarRaiz_eq_potencias _ _ m (by norm_num) (by norm_num) hm,
    constanteRaizCuadrado, show -(1 / (2 * 2 : ℝ)) = -(1 / 4 : ℝ) by norm_num]
  ring

theorem radioRaizCuadrado_potencia (α : ℝ) (m : ℕ) (hm : 0 < m) :
    radioRaizCuadrado m ^ (2 * α) =
      (3 * Real.sqrt 2) ^ (2 * α) * (m : ℝ) ^ (-(α / 2)) := by
  rw [radioRaizCuadrado, radio_cobertura_potencia _ _ α m (by norm_num) (by norm_num) hm,
    constanteRaizCuadrado, mul_comm (Real.sqrt 2) 3]

theorem radioRaizCuadrado_pos (m : ℕ) (hm : 0 < m) : 0 < radioRaizCuadrado m := by
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [radioRaizCuadrado_eq m hm]
  positivity

private theorem radioRaizCuadrado_sq (m : ℕ) (hm : 0 < m) :
    radioRaizCuadrado m ^ 2 = 18 / Real.sqrt (m : ℝ) := by
  have h := escalaAuxiliarRaiz_masa (1 / 9) 2 m (by norm_num) (by norm_num) hm
  rw [Real.rpow_two] at h
  rw [radioRaizCuadrado, mul_pow, Real.sq_sqrt (by norm_num)]
  linarith only [h]

theorem radioRaizCuadrado_le_uno_iff (m : ℕ) (hm : 0 < m) :
    radioRaizCuadrado m ≤ 1 ↔ 324 ≤ m := by
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hm)
  rw [← sq_le_sq₀ (radioRaizCuadrado_pos m hm).le (by norm_num : (0 : ℝ) ≤ 1),
    radioRaizCuadrado_sq m hm, one_pow, div_le_iff₀ hs, one_mul,
    ← sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 18) hs.le, Real.sq_sqrt (by positivity),
    show (18 : ℝ) ^ 2 = 324 by norm_num]
  exact_mod_cast (Iff.rfl : (324 ≤ m) ↔ 324 ≤ m)

theorem escalaRaizCuadrado_admisible (m : ℕ) (hm : 324 ≤ m) :
    0 < escalaAuxiliarRaiz (1 / 9) 2 m ∧ escalaAuxiliarRaiz (1 / 9) 2 m ≤ 1 ∧
      0 < 1 / Real.sqrt (m : ℝ) ∧ 1 / Real.sqrt (m : ℝ) ≤ 1 := by
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have heta : 0 < escalaAuxiliarRaiz (1 / 9) 2 m := by
    unfold escalaAuxiliarRaiz
    positivity
  have hr : radioRaizCuadrado m ≤ 1 :=
    (radioRaizCuadrado_le_uno_iff m (by omega)).2 hm
  have htwo : 1 ≤ Real.sqrt 2 := by
    simpa using Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
  refine ⟨heta, (le_mul_of_one_le_left heta.le htwo).trans hr, by positivity, ?_⟩
  apply (div_le_iff₀ (Real.sqrt_pos.2 hm')).2
  have h : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  simpa using Real.sqrt_le_sqrt h

theorem factorRaizInterior_eq (m : ℕ) (hm : 0 < m) :
    3 * (Real.pi / 4) * (m : ℝ) * radioRaizCuadrado m ^ 2 = factorRaizInterior m := by
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hm)
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ))
  have hr : (m : ℝ) / Real.sqrt (m : ℝ) = Real.sqrt (m : ℝ) := by
    apply (div_eq_iff hs.ne').2
    nlinarith only [hsq]
  rw [radioRaizCuadrado_sq m hm, factorRaizInterior]
  calc
    _ = (27 * Real.pi / 2) * ((m : ℝ) / Real.sqrt (m : ℝ)) := by ring
    _ = _ := by rw [hr]

theorem factorRaizInterior_pos (m : ℕ) (hm : 0 < m) : 0 < factorRaizInterior m := by
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  unfold factorRaizInterior
  positivity

theorem pesoRaizInterior_pos (α : ℝ) (m : ℕ) (hm : 0 < m) :
    0 < pesoRaizInterior α m :=
  div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (radioRaizCuadrado_pos m hm) _))
    (factorRaizInterior_pos m hm)

theorem producto_pesoRaizInterior (α : ℝ) (m : ℕ) (hm : 0 < m) :
    factorRaizInterior m * pesoRaizInterior α m = 3 * radioRaizCuadrado m ^ (2 * α) := by
  rw [pesoRaizInterior, mul_div_cancel₀ _ (factorRaizInterior_pos m hm).ne']

theorem pesoRaizInterior_eq_potencia (α : ℝ) (m : ℕ) (hm : 0 < m) :
    pesoRaizInterior α m =
      (3 * (3 * Real.sqrt 2) ^ (2 * α) / (27 * Real.pi / 2)) *
        (m : ℝ) ^ (-((α + 1) / 2)) := by
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [pesoRaizInterior, factorRaizInterior, radioRaizCuadrado_potencia α m hm,
    Real.sqrt_eq_rpow (m : ℝ), show -((α + 1) / 2) = -(α / 2) - 1 / 2 by ring,
    Real.rpow_sub hm']
  ring

theorem pesoRaizInterior_medio (m : ℕ) (hm : 0 < m) :
    pesoRaizInterior (1 / 2) m = (2 * Real.sqrt 2 / (3 * Real.pi)) *
      (m : ℝ) ^ (-(3 / 4 : ℝ)) := by
  rw [pesoRaizInterior_eq_potencia _ m hm]
  norm_num
  field_simp [Real.pi_pos.ne'] <;> ring

def falloRaizCuadrado (m : ℕ) : ℝ :=
  Real.sqrt (m : ℝ) * (1 - 1 / Real.sqrt (m : ℝ)) ^ m

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem particiones311 (m : ℕ) (hm : 324 ≤ m) :
    ∃ K : ℕ, ∃ cells : Fin K → Set Plano,
      (∀ k, MeasurableSet (cells k)) ∧
      Pairwise (fun i j => Disjoint (cells i) (cells j)) ∧
      cuadrado ⊆ ⋃ k, cells k ∧
      (∀ k, (1 / 9) * escalaAuxiliarRaiz (1 / 9) 2 m ^ (2 : ℝ) ≤
        medidaUniformeCuadrado.real (cells k)) ∧
      (∀ k, ∀ x ∈ cells k, ∀ y ∈ cells k, dist x y ≤ radioRaizCuadrado m) := by
  obtain ⟨hη, hηle, _, _⟩ := escalaRaizCuadrado_admisible m hm
  obtain ⟨K, cells, hc, hd, hU, _, hp, hdiam⟩ := particiones_uniformes_cuadrado _ hη hηle
  exact ⟨K, cells, hc, hd, hU, hp, hdiam⟩

/-- (3.49) con el mayorante binomial, y cobertura eventual con la
serie exponencial sumable del Lema 3.6. -/
theorem ocupacion311 (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Muestreo38 P medidaUniformeCuadrado) :
    (∀ m : ℕ, 324 ≤ m → ∃ K : ℕ, ∃ cells : Fin K → Set Plano,
      (∀ k, MeasurableSet (cells k)) ∧
      MeasurableSet (todasCeldasOcupadas Z.Z m cells)ᶜ ∧
      P.real (todasCeldasOcupadas Z.Z m cells)ᶜ ≤ falloRaizCuadrado m ∧
      ∀ ω ∈ todasCeldasOcupadas Z.Z m cells,
        MuestrasCubren cuadrado (prefijoPoisson P Z m ω) (radioRaizCuadrado m)) ∧
    (∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop,
      MuestrasCubren cuadrado (prefijoPoisson P Z m ω) (radioRaizCuadrado m)) := by
  constructor
  · intro m hm
    obtain ⟨K, cells, hc, hd, hU, hp, hdiam⟩ := particiones311 m hm
    let p : ℝ := 1 / Real.sqrt (m : ℝ)
    have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr (by omega))
    have hmin (k : Fin K) : p ≤ medidaUniformeCuadrado.real (cells k) := by
      change 1 / Real.sqrt (m : ℝ) ≤ _
      rw [← escalaAuxiliarRaiz_masa (1 / 9) 2 m (by norm_num) (by norm_num) (by omega)]
      exact hp k
    have hcard := cardinal_por_masa_minima medidaUniformeCuadrado cells hc hd p hmin
    have hK : (K : ℝ) ≤ Real.sqrt (m : ℝ) := by
      apply (div_le_iff₀ hs).1
      simpa [p, div_eq_mul_inv] using hcard
    have hle : p ≤ 1 := (escalaRaizCuadrado_admisible m hm).2.2.2
    refine ⟨K, cells, hc, (todasCeldasOcupadas_measurable Z.Z m cells hc Z.medible).compl, ?_, ?_⟩
    · rw [falloOcupacion_eq_union]
      calc
        _ ≤ ∑ k : Fin K, P.real (celdaVacia Z.Z m (cells k)) :=
          measureReal_iUnion_fintype_le _
        _ ≤ ∑ _k : Fin K, (1 - p) ^ m := by
          apply Finset.sum_le_sum
          intro k _
          rw [medidaReal_celdaVacia P medidaUniformeCuadrado Z.Z m (cells k)
            (hc k) Z.medible Z.indep Z.ley]
          have hk : medidaUniformeCuadrado.real (cells k) ≤ 1 :=
            (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
          exact pow_le_pow_left₀ (sub_nonneg.mpr hk) (by linarith [hmin k]) m
        _ = (K : ℝ) * (1 - p) ^ m := by simp
        _ ≤ falloRaizCuadrado m := mul_le_mul_of_nonneg_right hK (pow_nonneg (sub_nonneg.mpr hle) _)
    · exact ocupacion_implica_cobertura Z.Z m cuadrado cells _ hU hdiam
  · let M (n : ℕ) := n + 324
    choose K cells hc hd hU hp hdiam using fun n =>
      particiones311 (M n) (by dsimp [M]; omega)
    have hcov := cobertura_eventual_de_particiones_raiz P medidaUniformeCuadrado Z.Z
      K M cells cuadrado (1 / 9) 2 (by norm_num) (by norm_num) hc hd hU hdiam
      (fun n => by dsimp [M]; omega) (Eventually.of_forall fun n => Nat.le_add_right _ _)
      hp Z.medible Z.indep Z.ley
    filter_upwards [hcov] with ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.mp hω
    apply eventually_atTop.mpr
    refine ⟨M N, fun m hm => ?_⟩
    have hindex : M (m - 324) = m := by dsimp [M] at hm ⊢; omega
    have hn : N ≤ m - 324 := by dsimp [M] at hm; omega
    have h := hN (m - 324) hn
    change MuestrasCubren cuadrado (fun i : Fin (M (m - 324)) => Z.Z i ω)
      (radioRaizCuadrado (M (m - 324))) at h
    rw [hindex] at h
    exact h

def funcional311 {m : ℕ} (α : ℝ) (s : Fin m → Plano) (L f : Plano → ℝ) : ℝ :=
  funcionalInterior cuadrado α s L f (pesoRaizInterior α m)

theorem perdida311_bajo_cobertura {m : ℕ} (hm : 324 ≤ m)
    (α : ℝ) (hα : 0 < α) (s : Fin m → Plano) (hs : ∀ i, s i ∈ cuadrado)
    (hc : MuestrasCubren cuadrado s (radioRaizCuadrado m))
    (L f : Plano → ℝ) (hL : EsHolderInterior cuadrado α L) (hf : EsHolderInterior cuadrado α f) :
    perdidaPoissonInterior L f ≤ factorRaizInterior m * funcional311 α s L f
      + 3 * radioRaizCuadrado m ^ (2 * α) * seminormaInterior cuadrado α f ^ 2 := by
  have hm' : 0 < m := by omega
  have hfC : 3 * (Real.pi / 4) * (m : ℝ) * radioRaizCuadrado m ^ (2 : ℝ) =
      factorRaizInterior m := by rw [Real.rpow_two, factorRaizInterior_eq m hm']
  have ha : (3 * (Real.pi / 4) * (m : ℝ) * radioRaizCuadrado m ^ (2 : ℝ)) *
      pesoRaizInterior α m = 3 * radioRaizCuadrado m ^ (2 * α) := by
    rw [hfC, producto_pesoRaizInterior α m hm']
  have h := perdidaInterior_le_funcional medidaUniformeCuadrado cuadrado
    cuadrado_abierto.measurableSet medidaUniformeCuadrado_concentrada s hm' hs L f α hα
    hL hf (radioRaizCuadrado m) 1 (Real.pi / 4) 2 (pesoRaizInterior α m)
    (radioRaizCuadrado_pos m hm') ((radioRaizCuadrado_le_uno_iff m hm').2 hm)
    (by positivity) hc masa_bola_uniforme_cuadrado
    (perdidaPoissonInterior_integrable L f α hα hL hf) ha
  rw [hfC] at h
  exact h

/-- (3.51) para funciones del mismo prefijo que se usa en la ocupación.
Las tolerancias y la cota de regularidad son deterministas. -/
structure Selecciones311 {H : Type*} [MeasurableSpace H]
    (P : Measure Ω) (Z : Muestreo38 P medidaUniformeCuadrado)
    (α : ℝ) (L : H → Plano → ℝ) (f : Plano → ℝ) (Hm : ℕ → Set H) where
  h : ∀ m, (Fin m → Plano) → H
  v : ∀ m, (Fin m → Plano) → H
  h_medible : ∀ m, Measurable (h m)
  v_medible : ∀ m, Measurable (v m)
  η : ℕ → ℝ
  δ : ℕ → ℝ
  R : ℝ
  η_nonneg : ∀ m, 0 ≤ η m
  δ_nonneg : ∀ m, 0 ≤ δ m
  variacional : ∀ᵐ ω ∂P, ∀ m : ℕ, 324 ≤ m →
    let s := prefijoPoisson P Z m ω
    h m s ∈ Hm m ∧ v m s ∈ Hm m ∧
    perdidaEmpiricaInterior s (L (v m s)) f ≤ η m ∧
    seminormaInterior cuadrado α (L (v m s)) ^ 2 ≤ R ∧
    funcional311 α s (L (h m s)) f ≤
      sInf ((fun w => funcional311 α s (L w) f) '' Hm m) + δ m

theorem cotas311 {m : ℕ} {H : Type*}
    (hm : 324 ≤ m) (α : ℝ) (hα : 0 < α)
    (s : Fin m → Plano) (hs : ∀ i, s i ∈ cuadrado)
    (L : H → Plano → ℝ) (f : Plano → ℝ) (Hm : Set H) (h v : H) (hv : v ∈ Hm)
    (hL : EsHolderInterior cuadrado α (L h)) (hf : EsHolderInterior cuadrado α f)
    (η δ R : ℝ)
    (hη : perdidaEmpiricaInterior s (L v) f ≤ η)
    (hR : seminormaInterior cuadrado α (L v) ^ 2 ≤ R)
    (hδ : funcional311 α s (L h) f ≤ sInf ((fun w => funcional311 α s (L w) f) '' Hm) + δ) :
    let κ := (η + δ) / pesoRaizInterior α m
    seminormaInterior cuadrado α (L h) ^ 2 ≤ R + κ ∧
    funcional311 α s (L h) f ≤ pesoRaizInterior α m * (R + κ) ∧
    (MuestrasCubren cuadrado s (radioRaizCuadrado m) →
      perdidaPoissonInterior (L h) f ≤
        factorRaizInterior m * pesoRaizInterior α m * (R + κ) +
          3 * radioRaizCuadrado m ^ (2 * α) * seminormaInterior cuadrado α f ^ 2) := by
  have hm' : 0 < m := by omega
  obtain ⟨hj, hr⟩ := cotasInterior_de_suboptimalidad cuadrado α s L f
    (pesoRaizInterior α m) (pesoRaizInterior_pos α m hm') Hm h v hv η δ R hδ hη hR
  refine ⟨hr, hj, fun hc => ?_⟩
  rw [mul_assoc (factorRaizInterior m)]
  exact (perdida311_bajo_cobertura hm α hα s hs hc _ _ hL hf).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left hj (factorRaizInterior_pos m hm').le) _)

/-- El evento para (3.49) es la preimagen de un conjunto medible de prefijos. -/
theorem evento311 {H : Type*} (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Muestreo38 P medidaUniformeCuadrado) (α : ℝ) (hα : 0 < α)
    (L : H → Plano → ℝ) (f : Plano → ℝ) (Hm : ℕ → Set H)
    (hf : EsHolderInterior cuadrado α f)
    (hL : ∀ m h, h ∈ Hm m → EsHolderInterior cuadrado α (L h))
    (m : ℕ) (hm : 324 ≤ m) :
    ∃ A : Set (Fin m → Plano), MeasurableSet A ∧
      1 - falloRaizCuadrado m ≤ P.real (prefijoPoisson P Z m ⁻¹' A) ∧
      ∀ ω, prefijoPoisson P Z m ω ∈ A →
        MuestrasCubren cuadrado (prefijoPoisson P Z m ω) (radioRaizCuadrado m) ∧
        ∀ h ∈ Hm m, perdidaPoissonInterior (L h) f ≤
          factorRaizInterior m * funcional311 α (prefijoPoisson P Z m ω) (L h) f
            + 3 * radioRaizCuadrado m ^ (2 * α) * seminormaInterior cuadrado α f ^ 2 := by
  obtain ⟨K, cells, hcell, _, hbound, hcover⟩ := (ocupacion311 P Z).1 m hm
  let A : Set (Fin m → Plano) := {s | (∀ k : Fin K, ∃ i : Fin m, s i ∈ cells k) ∧
    ∀ i : Fin m, s i ∈ cuadrado}
  let S : Set Ω := {ω | ∀ i : Fin m, Z.Z i ω ∈ cuadrado}
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := by
    filter_upwards [muestras_en_soporte_ae P medidaUniformeCuadrado Z.Z cuadrado
      medidaUniformeCuadrado_concentrada Z.medible Z.ley] with ω hω
    exact fun i => hω i
  have hSzero : P.real Sᶜ = 0 := by
    have hzero : P Sᶜ = 0 := mem_ae_iff.mp hSae
    rw [measureReal_def, hzero, ENNReal.toReal_zero]
  have hA : MeasurableSet A := by
    rw [show A = (⋂ k : Fin K, ⋃ i : Fin m, (fun s : Fin m → Plano => s i) ⁻¹' cells k) ∩
        (⋂ i : Fin m, (fun s : Fin m → Plano => s i) ⁻¹' cuadrado) by ext s; simp [A]]
    exact (MeasurableSet.iInter fun k => MeasurableSet.iUnion fun i =>
      (hcell k).preimage (measurable_pi_apply i)).inter
      (MeasurableSet.iInter fun i => cuadrado_abierto.measurableSet.preimage (measurable_pi_apply i))
  have hpre : Measurable (prefijoPoisson P Z m) := measurable_pi_iff.mpr (fun i => Z.medible i)
  have hprob : P.real (prefijoPoisson P Z m ⁻¹' A)ᶜ ≤ falloRaizCuadrado m := by
    change P.real (todasCeldasOcupadas Z.Z m cells ∩ S)ᶜ ≤ _
    rw [Set.compl_inter]
    exact (measureReal_union_le _ _).trans (by rw [hSzero, add_zero]; exact hbound)
  rw [probReal_compl_eq_one_sub (hA.preimage hpre)] at hprob
  refine ⟨A, hA, by linarith, fun ω hω => ?_⟩
  have hc := hcover ω hω.1
  exact ⟨hc, fun h hh => perdida311_bajo_cobertura hm α hα _ hω.2 hc _ _ (hL m h hh) hf⟩

/-- Conclusiones poblacionales, incluidas las cotas anteriores a la condición
eventual de tolerancias. El índice de la sucesión es independiente del tamaño. -/
structure Resultados311 {H : Type*} [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Muestreo38 P medidaUniformeCuadrado)
    (α : ℝ) (L : H → Plano → ℝ) (f : Plano → ℝ) (Hm : ℕ → Set H)
    (sel : Selecciones311 P Z α L f Hm) : Prop where
  constantes : ∀ m : ℕ, 324 ≤ m →
    radioRaizCuadrado m ≤ 1 ∧
    radioRaizCuadrado m = 3 * Real.sqrt 2 * (m : ℝ) ^ (-(1 / 4 : ℝ)) ∧
    factorRaizInterior m = 3 * (Real.pi / 4) * (m : ℝ) * radioRaizCuadrado m ^ 2 ∧
    factorRaizInterior m * pesoRaizInterior α m = 3 * radioRaizCuadrado m ^ (2 * α)
  cobertura : ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop,
    MuestrasCubren cuadrado (prefijoPoisson P Z m ω) (radioRaizCuadrado m)
  evento : ∀ m : ℕ, 324 ≤ m → ∃ A : Set (Fin m → Plano), MeasurableSet A ∧
    1 - falloRaizCuadrado m ≤ P.real (prefijoPoisson P Z m ⁻¹' A) ∧
    ∀ ω, prefijoPoisson P Z m ω ∈ A →
      MuestrasCubren cuadrado (prefijoPoisson P Z m ω) (radioRaizCuadrado m) ∧
      ∀ h ∈ Hm m, perdidaPoissonInterior (L h) f ≤
        factorRaizInterior m * funcional311 α (prefijoPoisson P Z m ω) (L h) f
          + 3 * radioRaizCuadrado m ^ (2 * α) * seminormaInterior cuadrado α f ^ 2
  cotas : ∀ᵐ ω ∂P, ∀ m : ℕ, 324 ≤ m →
    let s := prefijoPoisson P Z m ω
    let h := sel.h m s
    let κ := (sel.η m + sel.δ m) / pesoRaizInterior α m
    seminormaInterior cuadrado α (L h) ^ 2 ≤ sel.R + κ ∧
    funcional311 α s (L h) f ≤ pesoRaizInterior α m * (sel.R + κ) ∧
    (MuestrasCubren cuadrado s (radioRaizCuadrado m) →
      perdidaPoissonInterior (L h) f ≤
        factorRaizInterior m * pesoRaizInterior α m * (sel.R + κ) +
          3 * radioRaizCuadrado m ^ (2 * α) * seminormaInterior cuadrado α f ^ 2)
  tasa : ∀ (ms : ℕ → ℕ), Tendsto ms atTop atTop → ∀ K : ℝ,
    (∀ᶠ n in atTop, sel.η (ms n) + sel.δ (ms n) ≤ K * pesoRaizInterior α (ms n)) →
    ∀ᵐ ω ∂P,
      (fun n => perdidaPoissonInterior (L (sel.h (ms n) (prefijoPoisson P Z (ms n) ω))) f)
        =O[atTop] fun n => (ms n : ℝ) ^ (-(α / 2))

theorem proposicion311_perdida {H : Type*} [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Muestreo38 P medidaUniformeCuadrado)
    (α : ℝ) (hα : 0 < α) (L : H → Plano → ℝ) (f : Plano → ℝ) (Hm : ℕ → Set H)
    (hf : EsHolderInterior cuadrado α f)
    (hL : ∀ m h, h ∈ Hm m → EsHolderInterior cuadrado α (L h))
    (sel : Selecciones311 P Z α L f Hm) :
    Resultados311 P Z α L f Hm sel := by
  have hcov := (ocupacion311 P Z).2
  have hsupp := muestras_en_soporte_ae P medidaUniformeCuadrado Z.Z cuadrado
    medidaUniformeCuadrado_concentrada Z.medible Z.ley
  refine ⟨?_, hcov, evento311 P Z α hα L f Hm hf hL, ?_, ?_⟩
  · intro m hm
    have hm' : 0 < m := by omega
    exact ⟨(radioRaizCuadrado_le_uno_iff m hm').2 hm, radioRaizCuadrado_eq m hm',
      (factorRaizInterior_eq m hm').symm, producto_pesoRaizInterior α m hm'⟩
  · filter_upwards [sel.variacional, hsupp] with ω hvar hs
    intro m hm
    obtain ⟨hh, hv, hη, hR, hδ⟩ := hvar m hm
    exact cotas311 hm α hα _ (fun i => hs i) L f _ _ _ hv (hL m _ hh) hf
      _ _ _ hη hR hδ
  · intro ms hm K htol
    filter_upwards [hcov, sel.variacional, hsupp] with ω hcover hvar hs
    apply isBigO_de_cota_eventual _ _
      (3 * (3 * Real.sqrt 2) ^ (2 * α) * (sel.R + K + seminormaInterior cuadrado α f ^ 2))
    filter_upwards [hm.eventually hcover, hm.eventually (eventually_ge_atTop 324), htol]
      with n hc hn htoln
    let m := ms n
    let s := prefijoPoisson P Z m ω
    have hm' : 0 < m := by dsimp [m]; omega
    obtain ⟨hh, hv, hη, hR, hδ⟩ := hvar m hn
    have hJ := (funcionalInterior_le_de_suboptimalidad cuadrado α s L f (pesoRaizInterior α m)
      (pesoRaizInterior_pos α m hm') (Hm m) (sel.h m s) (sel.v m s) hv _ _ _ _ hδ hη hR htoln).1
    have hp := perdida311_bajo_cobertura hn α hα s (fun i => hs i) hc _ _ (hL m _ hh) hf
    refine ⟨perdidaInterior_nonneg _ _ _, Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_⟩
    calc
      _ ≤ factorRaizInterior m * (pesoRaizInterior α m * (sel.R + K)) +
          3 * radioRaizCuadrado m ^ (2 * α) * seminormaInterior cuadrado α f ^ 2 :=
        hp.trans (add_le_add_left (mul_le_mul_of_nonneg_left hJ (factorRaizInterior_pos m hm').le) _)
      _ = _ := by
        rw [← mul_assoc (factorRaizInterior m), producto_pesoRaizInterior α m hm',
          radioRaizCuadrado_potencia α m hm']
        change _ = _ * (m : ℝ) ^ (-(α / 2))
        ring

theorem escalaEnergia311_eq (α : ℝ) (m : ℕ) :
    Real.sqrt ((m : ℝ) ^ (-(α / 2))) = (m : ℝ) ^ (-(α / 4)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg m)]
  congr 1
  ring

/-- Para la clase de Dirichlet exacto `G + ψq`, la tasa energética se obtiene
de la tasa poblacional de esta misma proposición. -/
theorem proposicion311_poisson
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Muestreo38 P medidaUniformeCuadrado)
    [MeasurableSpace CandidatoPoisson]
    (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1)
    (G : CandidatoPoisson) (f : Plano → ℝ) (Hm : ℕ → Set CandidatoPoisson)
    (hf : EsHolderInterior cuadrado α f)
    (sel : Selecciones311 P Z α (fun q => laplacianoClásico (aproximacionLevantada G q)) f Hm)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (hu : u - grafoSuaveCuadrado G ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens (datoPoissonLp f (datoPoissonInterior_memLp f α hα hf)) volume ⊤) :
    Resultados311 P Z α (fun q => laplacianoClásico (aproximacionLevantada G q)) f Hm sel ∧
    ∀ (ms : ℕ → ℕ), Tendsto ms atTop atTop → ∀ K : ℝ,
      (∀ᶠ n in atTop, sel.η (ms n) + sel.δ (ms n) ≤ K * pesoRaizInterior α (ms n)) →
      ∀ᵐ ω ∂P,
        let x := fun n => grafoLevantado G (sel.h (ms n) (prefijoPoisson P Z (ms n) ω))
        Tendsto x atTop (𝓝 u) ∧
        (fun n => ‖x n - u‖) =O[atTop] fun n => (ms n : ℝ) ^ (-(α / 4)) := by
  have hP := proposicion311_perdida P Z α hα
    (fun q => laplacianoClásico (aproximacionLevantada G q)) f Hm hf
    (fun _ q _ => laplacianoLevantado_holder G q α hα hα₁) sel
  refine ⟨hP, fun ms hm K htol => ?_⟩
  have hlim : Tendsto (fun n => Real.sqrt ((ms n : ℝ) ^ (-(α / 2)))) atTop (𝓝 0) := by
    simp only [escalaEnergia311_eq]
    exact (Real.tendsto_rpow_neg_atTop (show 0 < α / 4 by positivity)).comp
      (tendsto_natCast_atTop_atTop.comp hm)
  filter_upwards [hP.tasa ms hm K htol] with ω hω
  let q (n : ℕ) := sel.h (ms n) (prefijoPoisson P Z (ms n) ω)
  have hE := tasaEnergia_de_perdida (fun n => grafoLevantado G (q n)) u
    (fun n => perdidaPoissonInterior (laplacianoClásico (aproximacionLevantada G (q n))) f)
    (fun n => (ms n : ℝ) ^ (-(α / 2))) (2 * constanteEnergiaCuadrado)
    (mul_nonneg (by norm_num) constanteEnergiaCuadrado_pos.le)
    (fun _ => perdidaInterior_nonneg _ _ _)
    (fun n => energia315_por_perdida G (q n) f (datoPoissonInterior_memLp f α hα hf) u hu hsol)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg (ms n)) _) hlim hω
  simpa only [escalaEnergia311_eq] using hE

#check ocupacion311
#check evento311
#check cotas311
#check proposicion311_perdida
#check proposicion311_poisson
#print axioms radioRaizCuadrado_le_uno_iff
#print axioms factorRaizInterior_eq
#print axioms pesoRaizInterior_eq_potencia
#print axioms pesoRaizInterior_medio
#print axioms ocupacion311
#print axioms evento311
#print axioms cotas311
#print axioms proposicion311_perdida
#print axioms proposicion311_poisson

end TesisPINN
