import TesisPINN.ConvergenciaUniforme

/-!
# Lema 3.6 (Shin–Darbon–Karniadakis, Lemma B.2): cobertura con un parámetro de ocupación

Se enuncian, sobre la maquinaria de `OcupacionAleatoria`, las cuatro afirmaciones
del Lema 3.6 de la tesis:

* `lema36_probabilidad_cobertura`: la cadena (3.18)
  `P(A) ≥ 1 - K (1 - p)^n ≥ 1 - K exp (-n p)`, donde `p` es la masa mínima
  `c ε^s` de las celdas;
* `ocupacion_implica_cobertura` (ya existente) y `lema36_radio_dim2`: en el
  evento de ocupación, toda la región queda a distancia `√d ε` de la muestra;
* `lema36_fallo_parametro`: la cota (3.19), `P(Aᶜ) ≤ (n / t) exp (-t)`, para
  una masa mínima `t / n`;
* `lema36_fallo_shin`, `lema36_shin` y `lema36_radio_shin_dim2`: la elección
  original `t_n = √n`, con probabilidad al menos `1 - √n (1 - 1/√n)^n`.

El evento `A_{n,ε}` de la tesis es `todasCeldasOcupadas Z n cells`: es un
evento **medible** (intersección finita de uniones finitas de preimágenes), a
diferencia del predicado de cobertura sobre el dominio no numerable.

Las tres primeras afirmaciones valen en cualquier espacio medible, sin fijar
la dimensión: la geometría entra solo por la masa mínima de las celdas. Las
versiones `_dim2` usan `ParticionesMinimas`, que fija el factor `√2` del
diámetro.
-/

noncomputable section

namespace TesisPINN

open MeasureTheory ProbabilityTheory

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (μ : Measure X) [IsProbabilityMeasure μ]
  (Z : ℕ → Ω → X)

/-- Comparación elemental `(1 - p)^n ≤ exp (-n p)` para `p ≤ 1`. -/
theorem potencia_le_exp_neg (p : ℝ) (hp : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ Real.exp (-(n : ℝ) * p) := by
  calc
    (1 - p) ^ n ≤ (Real.exp (-p)) ^ n :=
      pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg p) n
    _ = Real.exp (-(n : ℝ) * p) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Primera desigualdad de (3.18) para el fallo: la cota de unión sobre las
`K` celdas y la probabilidad exacta `(1 - μ(celda))^n` de una celda vacía.
No se usa la disjunción de las celdas. -/
theorem lema36_fallo_le_potencia {K : ℕ} (n : ℕ)
    (cells : Fin K → Set X) (hc : ∀ k, MeasurableSet (cells k))
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ)
    (p : ℝ) (hmin : ∀ k, p ≤ μ.real (cells k)) :
    P.real (todasCeldasOcupadas Z n cells)ᶜ ≤ (K : ℝ) * (1 - p) ^ n := by
  rw [falloOcupacion_eq_union]
  calc
    P.real (⋃ k : Fin K, celdaVacia Z n (cells k)) ≤
        ∑ k : Fin K, P.real (celdaVacia Z n (cells k)) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin K, (1 - p) ^ n := by
      apply Finset.sum_le_sum
      intro k _
      have hμle : μ.real (cells k) ≤ 1 := by
        calc
          μ.real (cells k) ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
          _ = 1 := probReal_univ
      rw [medidaReal_celdaVacia P μ Z n (cells k) (hc k) hZ hIndep hLaw]
      exact pow_le_pow_left₀ (by linarith) (by linarith [hmin k]) n
    _ = (K : ℝ) * (1 - p) ^ n := by simp

/-- **Lema 3.6, ecuación (3.18).** Si cada celda tiene masa al menos `p`
(en la tesis, `p = c ε^s`), el evento de ocupación `A_{n,ε}` verifica
`P(A) ≥ 1 - K (1 - p)^n ≥ 1 - K exp (-n p)`. -/
theorem lema36_probabilidad_cobertura {K : ℕ} (n : ℕ)
    (cells : Fin K → Set X) (hc : ∀ k, MeasurableSet (cells k))
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ)
    (p : ℝ) (hmin : ∀ k, p ≤ μ.real (cells k)) :
    1 - (K : ℝ) * (1 - p) ^ n ≤ P.real (todasCeldasOcupadas Z n cells) ∧
    1 - (K : ℝ) * Real.exp (-(n : ℝ) * p) ≤ 1 - (K : ℝ) * (1 - p) ^ n := by
  constructor
  · have hfail := lema36_fallo_le_potencia P μ Z n cells hc hZ hIndep hLaw p hmin
    have hcompl : P.real (todasCeldasOcupadas Z n cells)ᶜ =
        1 - P.real (todasCeldasOcupadas Z n cells) :=
      probReal_compl_eq_one_sub (todasCeldasOcupadas_measurable Z n cells hc hZ)
    linarith
  · rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK
      simp
    · have hμle : μ.real (cells ⟨0, hK⟩) ≤ 1 := by
        calc
          μ.real (cells ⟨0, hK⟩) ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
          _ = 1 := probReal_univ
      have hp1 : p ≤ 1 := (hmin ⟨0, hK⟩).trans hμle
      have hmul := mul_le_mul_of_nonneg_left (potencia_le_exp_neg p hp1 n)
        (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
      linarith

omit [IsProbabilityMeasure μ] in
/-- Celdas disjuntas tienen, en particular, solapamientos de medida nula. -/
theorem solapamiento_nulo_de_disjuntas {K : ℕ} (cells : Fin K → Set X)
    (hdisj : Pairwise (fun i j => Disjoint (cells i) (cells j))) :
    Pairwise (fun i j => μ (cells i ∩ cells j) = 0) := by
  intro i j hij
  rw [Set.disjoint_iff_inter_eq_empty.mp (hdisj hij)]
  exact measure_empty

/-- **Lema 3.6, cota (3.20) del número de celdas**, con la hipótesis (i) de
la tesis: las celdas pueden solaparse en conjuntos de medida nula. Si cada
celda tiene masa al menos `p`, entonces `K p ≤ 1`. -/
theorem cardinal_por_masa_minima_ae {K : ℕ}
    (cells : Fin K → Set X) (hc : ∀ k, MeasurableSet (cells k))
    (hnulo : Pairwise (fun i j => μ (cells i ∩ cells j) = 0))
    (p : ℝ) (hmin : ∀ k, p ≤ μ.real (cells k)) :
    (K : ℝ) * p ≤ 1 := by
  have hae : Pairwise (Function.onFun (AEDisjoint μ) cells) :=
    fun i j hij => hnulo hij
  have hU : μ (⋃ k, cells k) = ∑ k : Fin K, μ (cells k) := by
    rw [measure_iUnion₀ hae (fun k => (hc k).nullMeasurableSet), tsum_fintype]
  have hreal : ∑ k : Fin K, μ.real (cells k) = μ.real (⋃ k, cells k) := by
    simp only [measureReal_def]
    rw [hU, ENNReal.toReal_sum (fun k _ => measure_ne_top μ (cells k))]
  have hsum : ∑ k : Fin K, μ.real (cells k) ≤ 1 := by
    rw [hreal]
    calc
      μ.real (⋃ k, cells k) ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := probReal_univ
  have hsumMin : ∑ _k : Fin K, p ≤ ∑ k : Fin K, μ.real (cells k) :=
    Finset.sum_le_sum fun k _ => hmin k
  simpa using hsumMin.trans hsum

/-- **Lema 3.6, ecuación (3.19).** Con masa mínima `t / n` en cada celda (es
decir, `c η_n^s = t_n / n`), la probabilidad de fallo de cobertura es a lo
sumo `(n / t) exp (-t)`. Las celdas pueden solaparse en conjuntos de medida
nula, como en la hipótesis (i) de la tesis. La condición `t ≤ n` del enunciado
no se necesita para la desigualdad. -/
theorem lema36_fallo_parametro {K : ℕ} (n : ℕ) (hn : 0 < n)
    (cells : Fin K → Set X) (hc : ∀ k, MeasurableSet (cells k))
    (hnulo : Pairwise (fun i j => μ (cells i ∩ cells j) = 0))
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ)
    (t : ℝ) (ht : 0 < t)
    (hmin : ∀ k, t / (n : ℝ) ≤ μ.real (cells k)) :
    P.real (todasCeldasOcupadas Z n cells)ᶜ ≤ (n : ℝ) / t * Real.exp (-t) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp : 0 ≤ t / (n : ℝ) := div_nonneg ht.le hn'.le
  have hcard := cardinal_por_masa_minima_ae μ cells hc hnulo (t / (n : ℝ)) hmin
  have h1 : (K : ℝ) * t / (n : ℝ) ≤ 1 := by
    rw [mul_div_assoc]
    exact hcard
  have h2 : (K : ℝ) * t ≤ (n : ℝ) := (div_le_one hn').mp h1
  have hK : (K : ℝ) ≤ (n : ℝ) / t := (le_div_iff₀ ht).mpr h2
  have hfail := medidaReal_falloOcupacion_le_exp P μ Z n cells hc
    hZ hIndep hLaw (t / (n : ℝ)) hp hmin
  have hmul : (n : ℝ) * (t / (n : ℝ)) = t := mul_div_cancel₀ t hn'.ne'
  have hneg : -(n : ℝ) * (t / (n : ℝ)) = -t := by rw [neg_mul, hmul]
  rw [hneg] at hfail
  exact hfail.trans (mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _))

/-- Escala auxiliar general de (3.19): `η_n = (t_n / (c n))^(1/s)`. -/
def escalaAuxiliarParametro (c s t : ℝ) (n : ℕ) : ℝ :=
  (t / (c * (n : ℝ))) ^ (1 / s)

/-- La escala `η_n` hace que la masa mínima `c η_n^s` de las celdas sea
exactamente `t_n / n`, que es la hipótesis de `lema36_fallo_parametro`. -/
theorem escalaAuxiliarParametro_masa (c s t : ℝ) (n : ℕ)
    (hc : 0 < c) (hs : 0 < s) (ht : 0 ≤ t) :
    c * escalaAuxiliarParametro c s t n ^ s = t / (n : ℝ) := by
  have hbase : 0 ≤ t / (c * (n : ℝ)) :=
    div_nonneg ht (mul_nonneg hc.le (Nat.cast_nonneg n))
  have hpow : escalaAuxiliarParametro c s t n ^ s = t / (c * (n : ℝ)) := by
    unfold escalaAuxiliarParametro
    rw [← Real.rpow_mul hbase, one_div, inv_mul_cancel₀ hs.ne', Real.rpow_one]
  rw [hpow, ← mul_div_assoc, mul_div_mul_left _ _ hc.ne']

/-- **Lema 3.6, elección original de Shin `t_n = √n`.** Con masa mínima
`n^{-1/2}` en cada celda, el número de celdas es a lo sumo `√n` y el fallo de
cobertura tiene probabilidad a lo sumo `√n (1 - 1/√n)^n`. -/
theorem lema36_fallo_shin {K : ℕ} (n : ℕ) (hn : 0 < n)
    (cells : Fin K → Set X) (hc : ∀ k, MeasurableSet (cells k))
    (hnulo : Pairwise (fun i j => μ (cells i ∩ cells j) = 0))
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ)
    (hmin : ∀ k, 1 / Real.sqrt (n : ℝ) ≤ μ.real (cells k)) :
    P.real (todasCeldasOcupadas Z n cells)ᶜ ≤
      Real.sqrt (n : ℝ) * (1 - 1 / Real.sqrt (n : ℝ)) ^ n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn'
  have hcard := cardinal_por_masa_minima_ae μ cells hc hnulo
    (1 / Real.sqrt (n : ℝ)) hmin
  have hK : (K : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hdiv : (K : ℝ) / Real.sqrt (n : ℝ) ≤ 1 := by
      rw [div_eq_mul_one_div]
      exact hcard
    exact (div_le_one hsqrt).mp hdiv
  have hone : 1 ≤ Real.sqrt (n : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hbase : 0 ≤ 1 - 1 / Real.sqrt (n : ℝ) :=
    sub_nonneg.mpr ((div_le_one hsqrt).mpr hone)
  exact (lema36_fallo_le_potencia P μ Z n cells hc hZ hIndep hLaw
    (1 / Real.sqrt (n : ℝ)) hmin).trans
    (mul_le_mul_of_nonneg_right hK (pow_nonneg hbase n))

/-- Forma de probabilidad de éxito de la elección de Shin:
`P(A) ≥ 1 - √n (1 - 1/√n)^n`. -/
theorem lema36_shin {K : ℕ} (n : ℕ) (hn : 0 < n)
    (cells : Fin K → Set X) (hc : ∀ k, MeasurableSet (cells k))
    (hnulo : Pairwise (fun i j => μ (cells i ∩ cells j) = 0))
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ)
    (hmin : ∀ k, 1 / Real.sqrt (n : ℝ) ≤ μ.real (cells k)) :
    1 - Real.sqrt (n : ℝ) * (1 - 1 / Real.sqrt (n : ℝ)) ^ n ≤
      P.real (todasCeldasOcupadas Z n cells) := by
  have hfail := lema36_fallo_shin P μ Z n hn cells hc hnulo hZ hIndep hLaw hmin
  have hcompl : P.real (todasCeldasOcupadas Z n cells)ᶜ =
      1 - P.real (todasCeldasOcupadas Z n cells) :=
    probReal_compl_eq_one_sub (todasCeldasOcupadas_measurable Z n cells hc hZ)
  linarith

/-- La cota de Shin es más fina que la cota exponencial `√n exp (-√n)` que
usa la maquinaria de Borel–Cantelli (`falloOcupacion_le_escala_raiz`). -/
theorem cota_shin_le_exponencial (n : ℕ) (hn : 0 < n) :
    Real.sqrt (n : ℝ) * (1 - 1 / Real.sqrt (n : ℝ)) ^ n ≤
      Real.sqrt (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn'
  have hone : 1 ≤ Real.sqrt (n : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hp1 : 1 / Real.sqrt (n : ℝ) ≤ 1 := (div_le_one hsqrt).mpr hone
  have hpow := potencia_le_exp_neg (1 / Real.sqrt (n : ℝ)) hp1 n
  have hroot : (n : ℝ) * (1 / Real.sqrt (n : ℝ)) = Real.sqrt (n : ℝ) := by
    rw [mul_one_div]
    exact (div_eq_iff hsqrt.ne').mpr (Real.mul_self_sqrt hn'.le).symm
  have hneg : -(n : ℝ) * (1 / Real.sqrt (n : ℝ)) = -Real.sqrt (n : ℝ) := by
    rw [neg_mul, hroot]
  rw [hneg] at hpow
  exact mul_le_mul_of_nonneg_left hpow hsqrt.le

section Radio

variable [PseudoMetricSpace X]

/-- **Lema 3.6, radio de cobertura en dimensión dos.** Para una escala
`0 < ε ≤ ε₀` de la Hipótesis 3.2 existe un evento medible `A`, con
`P(A) ≥ 1 - K (1 - c ε^s)^n ≥ 1 - K exp (-n c ε^s)`, sobre el cual las
primeras `n` muestras son `√2 ε`-densas en `U`. Aquí `K` es el número de
celdas de la partición de escala `ε`, y verifica la cota (3.20),
`K c ε^s ≤ 1`; sin ella la desigualdad de probabilidad sería vacía. -/
theorem lema36_radio_dim2
    (U : Set X) (c s ε₀ : ℝ)
    (hpart : ParticionesMinimas μ U c s ε₀)
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hε₀ : ε ≤ ε₀) :
    ∃ K : ℕ, ∃ A : Set Ω, MeasurableSet A ∧
      (K : ℝ) * (c * ε ^ s) ≤ 1 ∧
      1 - (K : ℝ) * (1 - c * ε ^ s) ^ n ≤ P.real A ∧
      1 - (K : ℝ) * Real.exp (-(n : ℝ) * (c * ε ^ s)) ≤
        1 - (K : ℝ) * (1 - c * ε ^ s) ^ n ∧
      ∀ ω ∈ A, MuestrasCubren U (fun i : Fin n => Z i ω) (Real.sqrt 2 * ε) := by
  obtain ⟨K, cells, hc, hdisj, hcover, _hsub, hmin, hdiam⟩ := hpart ε hε hε₀
  have hprob := lema36_probabilidad_cobertura P μ Z n cells hc hZ hIndep hLaw
    (c * ε ^ s) hmin
  exact ⟨K, todasCeldasOcupadas Z n cells,
    todasCeldasOcupadas_measurable Z n cells hc hZ,
    cardinal_por_masa_minima μ cells hc hdisj (c * ε ^ s) hmin,
    hprob.1, hprob.2,
    fun ω hω => ocupacion_implica_cobertura Z n U cells (Real.sqrt 2 * ε)
      hcover hdiam ω hω⟩

/-- **Lema 3.6, conclusión final (elección de Shin, dimensión dos).** Si la
escala `η = c^{-1/s} n^{-1/(2s)}` no excede `ε₀`, existe un evento medible de
probabilidad al menos `1 - √n (1 - 1/√n)^n` sobre el cual
`sup_{x ∈ U} min_j dist x x_j ≤ √2 c^{-1/s} n^{-1/(2s)}`. -/
theorem lema36_radio_shin_dim2
    (U : Set X) (c s ε₀ : ℝ) (hc : 0 < c) (hs : 0 < s)
    (hpart : ParticionesMinimas μ U c s ε₀)
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ)
    (n : ℕ) (hn : 0 < n)
    (hη : escalaAuxiliarRaiz c s n ≤ ε₀) :
    ∃ A : Set Ω, MeasurableSet A ∧
      1 - Real.sqrt (n : ℝ) * (1 - 1 / Real.sqrt (n : ℝ)) ^ n ≤ P.real A ∧
      ∀ ω ∈ A, MuestrasCubren U (fun i : Fin n => Z i ω)
        (Real.sqrt 2 * escalaAuxiliarRaiz c s n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hη0 : 0 < escalaAuxiliarRaiz c s n := by
    unfold escalaAuxiliarRaiz
    positivity
  obtain ⟨K, cells, hcm, hdisj, hcover, _hsub, hmin, hdiam⟩ :=
    hpart (escalaAuxiliarRaiz c s n) hη0 hη
  have hmin' : ∀ k, 1 / Real.sqrt (n : ℝ) ≤ μ.real (cells k) := by
    intro k
    rw [← escalaAuxiliarRaiz_masa c s n hc hs hn]
    exact hmin k
  exact ⟨todasCeldasOcupadas Z n cells,
    todasCeldasOcupadas_measurable Z n cells hcm hZ,
    lema36_shin P μ Z n hn cells hcm (solapamiento_nulo_de_disjuntas μ cells hdisj)
      hZ hIndep hLaw hmin',
    fun ω hω => ocupacion_implica_cobertura Z n U cells _ hcover hdiam ω hω⟩

end Radio

#print axioms TesisPINN.lema36_probabilidad_cobertura
#print axioms TesisPINN.cardinal_por_masa_minima_ae
#print axioms TesisPINN.lema36_fallo_parametro
#print axioms TesisPINN.escalaAuxiliarParametro_masa
#print axioms TesisPINN.lema36_fallo_shin
#print axioms TesisPINN.lema36_shin
#print axioms TesisPINN.cota_shin_le_exponencial
#print axioms TesisPINN.lema36_radio_dim2
#print axioms TesisPINN.lema36_radio_shin_dim2

end TesisPINN
