import TesisPINN.CoberturaIntegral
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.PSeries

/-!
# Ocupación aleatoria de particiones finitas

La fuente de aleatoriedad es una sucesión infinita de muestras independientes
con ley común. Cada tamaño de muestra utiliza su prefijo finito en el mismo
espacio de probabilidad.
-/

noncomputable section

namespace TesisPINN

open MeasureTheory ProbabilityTheory Filter

private theorem sqrt_mul_exp_neg_sqrt_le (x : ℝ) (hx : 0 < x) :
    Real.sqrt x * Real.exp (-Real.sqrt x) ≤ 120 / x ^ 2 := by
  let t := Real.sqrt x
  have ht : 0 < t := Real.sqrt_pos.2 hx
  have ht2 : t ^ 2 = x := Real.sq_sqrt hx.le
  have ht4 : t ^ 4 = x ^ 2 := by nlinarith [ht2]
  have hexp : t ^ 5 / 120 ≤ Real.exp t := by
    convert Real.pow_div_factorial_le_exp t ht.le 5 using 1 <;> norm_num
  have hExp : t ^ 5 ≤ 120 * Real.exp t := by nlinarith [hexp]
  have hcancel : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hbound : t * Real.exp (-t) * t ^ 4 ≤ 120 := by
    calc
      t * Real.exp (-t) * t ^ 4 = t ^ 5 * Real.exp (-t) := by ring
      _ ≤ (120 * Real.exp t) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right hExp (Real.exp_nonneg _)
      _ = 120 := by rw [mul_assoc, hcancel]; ring
  change t * Real.exp (-t) ≤ 120 / x ^ 2
  rw [← ht4]
  exact (le_div_iff₀ (pow_pos ht 4)).2 (by nlinarith [hbound])

/-- La serie usada en la elección `t_n=√n` de la tesis es sumable.
La traslación por uno evita el caso `n=0`. -/
theorem sumable_sqrt_mul_exp_neg_sqrt :
    Summable (fun n : ℕ =>
      Real.sqrt ((n : ℝ) + 1) * Real.exp (-Real.sqrt ((n : ℝ) + 1))) := by
  have hs : Summable (fun n : ℕ =>
      (120 : ℝ) / (((n : ℝ) + 1) ^ 2)) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    have h' : Summable (fun n : ℕ =>
        1 / (((n : ℝ) + 1) ^ 2)) := by
      convert h using 1
      ext n
      have hn : 0 ≤ (n : ℝ) + 1 := by positivity
      simp [abs_of_nonneg hn, Real.rpow_two]
    simpa [div_eq_mul_inv] using h'.mul_left 120
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  exact sqrt_mul_exp_neg_sqrt_le _ (by positivity)

/-- La misma serie sigue siendo sumable al sustituir `n` por cualquier
tamaño `m(n)≥n` eventualmente, como exige el Teorema 3.8. -/
theorem sumable_escala_raiz_de_tamanos
    (m : ℕ → ℕ) (hm : ∀ᶠ n in atTop, n ≤ m n) :
    Summable (fun n : ℕ =>
      Real.sqrt (m n : ℝ) * Real.exp (-Real.sqrt (m n : ℝ))) := by
  have hs : Summable (fun n : ℕ => (120 : ℝ) / (n : ℝ) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
    simpa [div_eq_mul_inv] using h.mul_left 120
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hm, eventually_ge_atTop (1 : ℕ)] with n hmn hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hm' : (0 : ℝ) < m n := Nat.cast_pos.mpr (by omega)
  have hmn' : (n : ℝ) ≤ m n := by exact_mod_cast hmn
  have hbound := sqrt_mul_exp_neg_sqrt_le (m n : ℝ) hm'
  have hdiv : (120 : ℝ) / (m n : ℝ) ^ 2 ≤
      120 / (n : ℝ) ^ 2 := by gcongr
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hbound.trans hdiv

/-- Escala auxiliar de (3.19) para `t_m=√m`: `η=(√m/(cm))^(1/s)`,
escrita en la forma algebraicamente equivalente `(c√m)^(-1/s)`. -/
def escalaAuxiliarRaiz (c s : ℝ) (m : ℕ) : ℝ :=
  (1 / (c * Real.sqrt (m : ℝ))) ^ (1 / s)

theorem escalaAuxiliarRaiz_masa (c s : ℝ) (m : ℕ)
    (hc : 0 < c) (hs : 0 < s) (hm : 0 < m) :
    c * escalaAuxiliarRaiz c s m ^ s =
      1 / Real.sqrt (m : ℝ) := by
  have hroot : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr hm)
  have hbase : 0 ≤ 1 / (c * Real.sqrt (m : ℝ)) := by positivity
  have hpow : escalaAuxiliarRaiz c s m ^ s =
      1 / (c * Real.sqrt (m : ℝ)) := by
    unfold escalaAuxiliarRaiz
    calc
      ((1 / (c * Real.sqrt (m : ℝ))) ^ (1 / s)) ^ s =
          (1 / (c * Real.sqrt (m : ℝ))) ^ ((1 / s) * s) :=
        (Real.rpow_mul hbase (1 / s) s).symm
      _ = (1 / (c * Real.sqrt (m : ℝ))) ^ (1 : ℝ) := by
        congr 1
        field_simp
      _ = 1 / (c * Real.sqrt (m : ℝ)) := Real.rpow_one _
  rw [hpow]
  field_simp

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (μ : Measure X) [IsProbabilityMeasure μ]
  (Z : ℕ → Ω → X)

/-- Ninguna de las primeras `m` muestras cae en `A`. -/
def celdaVacia (m : ℕ) (A : Set X) : Set Ω :=
  {ω | ∀ i : Fin m, Z i ω ∉ A}

theorem celdaVacia_measurable (m : ℕ) (A : Set X)
    (hA : MeasurableSet A) (hZ : ∀ i, Measurable (Z i)) :
    MeasurableSet (celdaVacia Z m A) := by
  classical
  rw [show celdaVacia Z m A = ⋂ i : Fin m, (Z i) ⁻¹' Aᶜ by
    ext ω; simp [celdaVacia]]
  exact MeasurableSet.iInter fun i => hA.compl.preimage (hZ i)

/-- Probabilidad exacta de una celda vacía: `(1-μ(A))^m`. -/
theorem medida_celdaVacia (m : ℕ) (A : Set X)
    (hA : MeasurableSet A)
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ) :
    P (celdaVacia Z m A) = (1 - μ A) ^ m := by
  classical
  have hi := ((iIndepFun_iff_measure_inter_preimage_eq_mul).mp
    (hIndep.precomp Fin.val_injective)) Finset.univ
    (sets := fun _ : Fin m => Aᶜ) (by intro i hi; exact hA.compl)
  have hpre (i : Fin m) : P ((Z i) ⁻¹' Aᶜ) = μ Aᶜ := by
    rw [← Measure.map_apply (hZ i) hA.compl, hLaw]
  have hi' : P (⋂ i : Fin m, (Z i) ⁻¹' Aᶜ) =
      ∏ i : Fin m, P ((Z i) ⁻¹' Aᶜ) := by simpa using hi
  change P (celdaVacia Z m A) = (1 - μ A) ^ m
  rw [show celdaVacia Z m A = ⋂ i : Fin m, (Z i) ⁻¹' Aᶜ by
    ext ω; simp [celdaVacia]]
  rw [hi']
  simp only [hpre, Finset.prod_const, Finset.card_fin]
  rw [prob_compl_eq_one_sub hA]

theorem medidaReal_celdaVacia (m : ℕ) (A : Set X)
    (hA : MeasurableSet A)
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ) :
    P.real (celdaVacia Z m A) = (1 - μ.real A) ^ m := by
  rw [measureReal_def, medida_celdaVacia P μ Z m A hA hZ hIndep hLaw,
    ← prob_compl_eq_one_sub hA, ENNReal.toReal_pow,
    ← measureReal_def, probReal_compl_eq_one_sub hA]

theorem medidaReal_celdaVacia_le_exp (m : ℕ) (A : Set X)
    (hA : MeasurableSet A)
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ)
    (p : ℝ) (hp : 0 ≤ p) (hmin : p ≤ μ.real A) :
    P.real (celdaVacia Z m A) ≤ Real.exp (-(m : ℝ) * p) := by
  have hμle : μ.real A ≤ 1 := by
    calc
      μ.real A ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := probReal_univ
  rw [medidaReal_celdaVacia P μ Z m A hA hZ hIndep hLaw]
  have hbase : 0 ≤ 1 - μ.real A := by linarith
  calc
    (1 - μ.real A) ^ m ≤ (1 - p) ^ m :=
      pow_le_pow_left₀ hbase (by linarith) m
    _ ≤ (Real.exp (-p)) ^ m :=
      pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg p) m
    _ = Real.exp (-(m : ℝ) * p) := by
      rw [← Real.exp_nat_mul]
      ring

/-- Todas las celdas de la familia reciben una muestra. -/
def todasCeldasOcupadas {K : ℕ} (m : ℕ) (cells : Fin K → Set X) : Set Ω :=
  {ω | ∀ k : Fin K, ∃ i : Fin m, Z i ω ∈ cells k}

theorem todasCeldasOcupadas_measurable {K : ℕ} (m : ℕ)
    (cells : Fin K → Set X) (hc : ∀ k, MeasurableSet (cells k))
    (hZ : ∀ i, Measurable (Z i)) :
    MeasurableSet (todasCeldasOcupadas Z m cells) := by
  classical
  rw [show todasCeldasOcupadas Z m cells =
      ⋂ k : Fin K, ⋃ i : Fin m, (Z i) ⁻¹' cells k by
      ext ω; simp [todasCeldasOcupadas]]
  exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun i =>
    (hc k).preimage (hZ i)

theorem falloOcupacion_eq_union {K : ℕ} (m : ℕ)
    (cells : Fin K → Set X) :
    (todasCeldasOcupadas Z m cells)ᶜ =
      ⋃ k : Fin K, celdaVacia Z m (cells k) := by
  classical
  ext ω
  simp [todasCeldasOcupadas, celdaVacia]

theorem medida_falloOcupacion_le_suma {K : ℕ} (m : ℕ)
    (cells : Fin K → Set X) (hc : ∀ k, MeasurableSet (cells k))
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ) :
    P (todasCeldasOcupadas Z m cells)ᶜ ≤
      ∑ k : Fin K, (1 - μ (cells k)) ^ m := by
  rw [falloOcupacion_eq_union]
  calc
    P (⋃ k : Fin K, celdaVacia Z m (cells k)) ≤
        ∑ k : Fin K, P (celdaVacia Z m (cells k)) :=
      measure_iUnion_fintype_le P _
    _ = ∑ k : Fin K, (1 - μ (cells k)) ^ m := by
      apply Finset.sum_congr rfl
      intro k hk
      exact medida_celdaVacia P μ Z m (cells k) (hc k) hZ hIndep hLaw

theorem medidaReal_falloOcupacion_le_exp {K : ℕ} (m : ℕ)
    (cells : Fin K → Set X) (hc : ∀ k, MeasurableSet (cells k))
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ)
    (p : ℝ) (hp : 0 ≤ p) (hmin : ∀ k, p ≤ μ.real (cells k)) :
    P.real (todasCeldasOcupadas Z m cells)ᶜ ≤
      (K : ℝ) * Real.exp (-(m : ℝ) * p) := by
  rw [falloOcupacion_eq_union]
  calc
    P.real (⋃ k : Fin K, celdaVacia Z m (cells k)) ≤
        ∑ k : Fin K, P.real (celdaVacia Z m (cells k)) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin K, Real.exp (-(m : ℝ) * p) := by
      apply Finset.sum_le_sum
      intro k hk
      exact medidaReal_celdaVacia_le_exp P μ Z m (cells k) (hc k)
        hZ hIndep hLaw p hp (hmin k)
    _ = (K : ℝ) * Real.exp (-(m : ℝ) * p) := by simp

theorem cardinal_por_masa_minima {K : ℕ}
    (cells : Fin K → Set X) (hc : ∀ k, MeasurableSet (cells k))
    (hdisj : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (p : ℝ) (hmin : ∀ k, p ≤ μ.real (cells k)) :
    (K : ℝ) * p ≤ 1 := by
  have hsum : ∑ k : Fin K, μ.real (cells k) ≤ 1 := by
    calc
      ∑ k : Fin K, μ.real (cells k) = μ.real (⋃ k, cells k) :=
        (measureReal_iUnion_fintype hdisj hc).symm
      _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := probReal_univ
  have hsumMin : ∑ _k : Fin K, p ≤ ∑ k : Fin K, μ.real (cells k) :=
    Finset.sum_le_sum fun k hk => hmin k
  simpa using hsumMin.trans hsum

/-- La elección `c η^s=m^{-1/2}` del Lema 3.6 da la cota de fallo
`√m exp(-√m)` sin un factor logarítmico. -/
theorem falloOcupacion_le_escala_raiz {K : ℕ} (m : ℕ) (hm : 0 < m)
    (cells : Fin K → Set X) (hc : ∀ k, MeasurableSet (cells k))
    (hdisj : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ)
    (hmin : ∀ k, 1 / Real.sqrt (m : ℝ) ≤ μ.real (cells k)) :
    P.real (todasCeldasOcupadas Z m cells)ᶜ ≤
      Real.sqrt (m : ℝ) * Real.exp (-Real.sqrt (m : ℝ)) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm'
  have hp : 0 ≤ 1 / Real.sqrt (m : ℝ) := by positivity
  have hcard := cardinal_por_masa_minima μ cells hc hdisj
    (1 / Real.sqrt (m : ℝ)) hmin
  have hK : (K : ℝ) ≤ Real.sqrt (m : ℝ) := by
    have hdiv : (K : ℝ) / Real.sqrt (m : ℝ) ≤ 1 := by
      simpa [div_eq_mul_inv] using hcard
    simpa using (div_le_iff₀ hsqrt).1 hdiv
  have hroot : (m : ℝ) * (1 / Real.sqrt (m : ℝ)) =
      Real.sqrt (m : ℝ) := by
    rw [one_div, ← div_eq_mul_inv]
    apply (div_eq_iff hsqrt.ne').2
    nlinarith [Real.sq_sqrt hm'.le]
  have hfail := medidaReal_falloOcupacion_le_exp P μ Z m cells hc
    hZ hIndep hLaw (1 / Real.sqrt (m : ℝ)) hp hmin
  have hneg : -(m : ℝ) * (1 / Real.sqrt (m : ℝ)) =
      -Real.sqrt (m : ℝ) := by nlinarith [hroot]
  rw [hneg] at hfail
  exact hfail.trans (mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _))

/-- Ocupación finita implica la cobertura geométrica, sin definir como evento
medible la cuantificación sobre todos los puntos del dominio. -/
theorem ocupacion_implica_cobertura
    [PseudoMetricSpace X] {K : ℕ} (m : ℕ)
    (U : Set X) (cells : Fin K → Set X) (ρ : ℝ)
    (hcover : U ⊆ ⋃ k, cells k)
    (hdiam : ∀ k, ∀ x ∈ cells k, ∀ y ∈ cells k, dist x y ≤ ρ)
    (ω : Ω) (hocc : ω ∈ todasCeldasOcupadas Z m cells) :
    MuestrasCubren U (fun i : Fin m => Z i ω) ρ := by
  intro x hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcover hx)
  obtain ⟨i, hi⟩ := hocc k
  exact ⟨i, hdiam k x hk (Z i ω) hi⟩

/-- Primer Borel–Cantelli aplicado a los eventos **finitos y medibles** de
fallo de ocupación. No se necesita independencia entre tamaños `n`. -/
theorem ocupacion_eventual_casi_segura
    (K m : ℕ → ℕ) (cells : ∀ n, Fin (K n) → Set X)
    (hsum : (∑' n, P ((todasCeldasOcupadas Z (m n) (cells n))ᶜ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∈ todasCeldasOcupadas Z (m n) (cells n) := by
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simpa only [Set.mem_compl_iff, not_not] using hn

theorem cobertura_eventual_casi_segura
    [PseudoMetricSpace X]
    (K m : ℕ → ℕ) (cells : ∀ n, Fin (K n) → Set X)
    (U : ℕ → Set X) (ρ : ℕ → ℝ)
    (hcover : ∀ n, U n ⊆ ⋃ k, cells n k)
    (hdiam : ∀ n k, ∀ x ∈ cells n k, ∀ y ∈ cells n k,
      dist x y ≤ ρ n)
    (hsum : (∑' n, P ((todasCeldasOcupadas Z (m n) (cells n))ᶜ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      MuestrasCubren (U n) (fun i : Fin (m n) => Z i ω) (ρ n) := by
  filter_upwards [ocupacion_eventual_casi_segura P Z K m cells hsum] with ω hω
  filter_upwards [hω] with n hn
  exact ocupacion_implica_cobertura Z (m n) (U n) (cells n)
    (ρ n) (hcover n) (hdiam n) ω hn

/-- Un mayorante real sumable de los fallos basta para la condición de
Borel–Cantelli en `ENNReal`. -/
theorem tsum_fallos_ne_top_de_mayorante
    (K m : ℕ → ℕ) (cells : ∀ n, Fin (K n) → Set X)
    (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ n,
      P.real ((todasCeldasOcupadas Z (m n) (cells n))ᶜ) ≤ b n) :
    (∑' n, P ((todasCeldasOcupadas Z (m n) (cells n))ᶜ)) ≠ ⊤ := by
  have hsum : Summable (fun n =>
      P.real ((todasCeldasOcupadas Z (m n) (cells n))ᶜ)) :=
    Summable.of_nonneg_of_le (fun n => measureReal_nonneg) hbound hb
  have hrepr (n : ℕ) :
      P ((todasCeldasOcupadas Z (m n) (cells n))ᶜ) =
        ENNReal.ofReal (P.real ((todasCeldasOcupadas Z (m n) (cells n))ᶜ)) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp_rw [hrepr]
  exact hsum.tsum_ofReal_ne_top

/-- Cobertura eventual casi segura en la escala de Shin `t_n=√m_n`.
Las particiones pueden variar con `n`; no se postula mensurabilidad del
predicado de cobertura sobre el dominio no numerable. -/
theorem cobertura_eventual_escala_raiz
    [PseudoMetricSpace X]
    (K m : ℕ → ℕ) (cells : ∀ n, Fin (K n) → Set X)
    (U : ℕ → Set X) (ρ : ℕ → ℝ)
    (hc : ∀ n k, MeasurableSet (cells n k))
    (hdisj : ∀ n, Pairwise (fun i j => Disjoint (cells n i) (cells n j)))
    (hcover : ∀ n, U n ⊆ ⋃ k, cells n k)
    (hdiam : ∀ n k, ∀ x ∈ cells n k, ∀ y ∈ cells n k,
      dist x y ≤ ρ n)
    (hmpos : ∀ n, 0 < m n)
    (hmGrowth : ∀ᶠ n in atTop, n ≤ m n)
    (hmin : ∀ n k, 1 / Real.sqrt (m n : ℝ) ≤ μ.real (cells n k))
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      MuestrasCubren (U n) (fun i : Fin (m n) => Z i ω) (ρ n) := by
  have hbound (n : ℕ) :
      P.real ((todasCeldasOcupadas Z (m n) (cells n))ᶜ) ≤
        Real.sqrt (m n : ℝ) * Real.exp (-Real.sqrt (m n : ℝ)) :=
    falloOcupacion_le_escala_raiz P μ Z (m n) (hmpos n) (cells n)
      (hc n) (hdisj n) hZ hIndep hLaw (hmin n)
  have hsum := tsum_fallos_ne_top_de_mayorante P Z K m cells
    (fun n => Real.sqrt (m n : ℝ) * Real.exp (-Real.sqrt (m n : ℝ)))
    (sumable_escala_raiz_de_tamanos m hmGrowth) hbound
  exact cobertura_eventual_casi_segura P Z K m cells U ρ
    hcover hdiam hsum

/-- Lema 3.6 en la elección `t_m=√m`, con la dimensión de masa `s`
explícita. En el cuadrado se instanciará con `s=2` para el interior y `s=1`
para la frontera; el factor geométrico es `√2` en ambos casos. -/
theorem cobertura_eventual_de_particiones_raiz
    [PseudoMetricSpace X]
    (K m : ℕ → ℕ) (cells : ∀ n, Fin (K n) → Set X)
    (U : Set X) (c s : ℝ) (hcpos : 0 < c) (hspos : 0 < s)
    (hc : ∀ n k, MeasurableSet (cells n k))
    (hdisj : ∀ n, Pairwise (fun i j => Disjoint (cells n i) (cells n j)))
    (hcover : ∀ n, U ⊆ ⋃ k, cells n k)
    (hdiam : ∀ n k, ∀ x ∈ cells n k, ∀ y ∈ cells n k,
      dist x y ≤ Real.sqrt 2 * escalaAuxiliarRaiz c s (m n))
    (hmpos : ∀ n, 0 < m n)
    (hmGrowth : ∀ᶠ n in atTop, n ≤ m n)
    (hmin : ∀ n k,
      c * escalaAuxiliarRaiz c s (m n) ^ s ≤ μ.real (cells n k))
    (hZ : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z P)
    (hLaw : ∀ i, Measure.map (Z i) P = μ) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      MuestrasCubren U (fun i : Fin (m n) => Z i ω)
        (Real.sqrt 2 * escalaAuxiliarRaiz c s (m n)) := by
  apply cobertura_eventual_escala_raiz P μ Z K m cells
    (fun _ => U) (fun n => Real.sqrt 2 * escalaAuxiliarRaiz c s (m n))
    hc hdisj hcover hdiam hmpos hmGrowth (fun n k => ?_) hZ hIndep hLaw
  rw [← escalaAuxiliarRaiz_masa c s (m n) hcpos hspos (hmpos n)]
  exact hmin n k

/-- Las dos coberturas del cuadrado se obtienen sobre el **mismo** espacio
probabilístico. La independencia entre muestreos interior y de frontera no es
necesaria para esta intersección de eventos de probabilidad uno. -/
theorem coberturas_cuadrado_eventuales_casi_seguras
    [PseudoMetricSpace X]
    {Y : Type*} [MeasurableSpace Y] [PseudoMetricSpace Y]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (Zb : ℕ → Ω → Y)
    (Kr Kb mr mb : ℕ → ℕ)
    (cellsR : ∀ n, Fin (Kr n) → Set X)
    (cellsB : ∀ n, Fin (Kb n) → Set Y)
    (U : Set X) (Gamma : Set Y) (cr cb : ℝ)
    (hcr : 0 < cr) (hcb : 0 < cb)
    (hcR : ∀ n k, MeasurableSet (cellsR n k))
    (hcB : ∀ n k, MeasurableSet (cellsB n k))
    (hdisjR : ∀ n, Pairwise (fun i j => Disjoint (cellsR n i) (cellsR n j)))
    (hdisjB : ∀ n, Pairwise (fun i j => Disjoint (cellsB n i) (cellsB n j)))
    (hcoverR : ∀ n, U ⊆ ⋃ k, cellsR n k)
    (hcoverB : ∀ n, Gamma ⊆ ⋃ k, cellsB n k)
    (hdiamR : ∀ n k, ∀ x ∈ cellsR n k, ∀ y ∈ cellsR n k,
      dist x y ≤ Real.sqrt 2 * escalaAuxiliarRaiz cr 2 (mr n))
    (hdiamB : ∀ n k, ∀ x ∈ cellsB n k, ∀ y ∈ cellsB n k,
      dist x y ≤ Real.sqrt 2 * escalaAuxiliarRaiz cb 1 (mb n))
    (hmrpos : ∀ n, 0 < mr n) (hmbpos : ∀ n, 0 < mb n)
    (hmrGrowth : ∀ᶠ n in atTop, n ≤ mr n)
    (hmbGrowth : ∀ᶠ n in atTop, n ≤ mb n)
    (hminR : ∀ n k, cr * escalaAuxiliarRaiz cr 2 (mr n) ^ (2 : ℝ) ≤
      μ.real (cellsR n k))
    (hminB : ∀ n k, cb * escalaAuxiliarRaiz cb 1 (mb n) ^ (1 : ℝ) ≤
      μb.real (cellsB n k))
    (hZr : ∀ i, Measurable (Z i)) (hZb : ∀ i, Measurable (Zb i))
    (hIndepR : iIndepFun Z P) (hIndepB : iIndepFun Zb P)
    (hLawR : ∀ i, Measure.map (Z i) P = μ)
    (hLawB : ∀ i, Measure.map (Zb i) P = μb) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      MuestrasCubren U (fun i : Fin (mr n) => Z i ω)
        (Real.sqrt 2 * escalaAuxiliarRaiz cr 2 (mr n)) ∧
      MuestrasCubren Gamma (fun i : Fin (mb n) => Zb i ω)
        (Real.sqrt 2 * escalaAuxiliarRaiz cb 1 (mb n)) := by
  have hr := cobertura_eventual_de_particiones_raiz P μ Z Kr mr cellsR U
    cr 2 hcr (by norm_num) hcR hdisjR hcoverR hdiamR hmrpos
    hmrGrowth hminR hZr hIndepR hLawR
  have hb := cobertura_eventual_de_particiones_raiz P μb Zb Kb mb cellsB Gamma
    cb 1 hcb (by norm_num) hcB hdisjB hcoverB hdiamB hmbpos
    hmbGrowth hminB hZb hIndepB hLawB
  filter_upwards [hr, hb] with ω hrω hbω
  filter_upwards [hrω, hbω] with n hnr hnb
  exact ⟨hnr, hnb⟩

/-- La cota poblacional de la etapa anterior, aplicada a una realización en
la que las particiones interiores y de frontera están ocupadas. Todas las
hipótesis analíticas y variacionales siguen visibles en el enunciado. -/
theorem perdidaPoblacional_de_ocupacion
    [PseudoMetricSpace X] [OpensMeasurableSpace X]
    {Y H : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {mr mb Kr Kb : ℕ}
    (Zb : ℕ → Ω → Y) (ω : Ω)
    (Pp : ProblemaPINN H X Y mr mb)
    (Hm : Set H) (U : Set X) (Gamma : Set Y)
    (cellsR : Fin Kr → Set X) (cellsB : Fin Kb → Set Y)
    (hcoverR : U ⊆ ⋃ k, cellsR k)
    (hcoverB : Gamma ⊆ ⋃ k, cellsB k)
    (α εr εb εr₀ εb₀ Cr Cb Sf Sg Rstar : ℝ)
    (hdiamR : ∀ k, ∀ x ∈ cellsR k, ∀ y ∈ cellsR k, dist x y ≤ εr)
    (hdiamB : ∀ k, ∀ x ∈ cellsB k, ∀ y ∈ cellsB k, dist x y ≤ εb)
    (hoccR : ω ∈ todasCeldasOcupadas Z mr cellsR)
    (hoccB : ω ∈ todasCeldasOcupadas Zb mb cellsB)
    (hsampleR : ∀ i : Fin mr, Pp.xr i = Z i ω)
    (hsampleB : ∀ i : Fin mb, Pp.xb i = Zb i ω)
    (hU : MeasurableSet U) (hGamma : MeasurableSet Gamma)
    (hμr : Pp.μr Uᶜ = 0) (hμb : Pp.μb Gammaᶜ = 0)
    (hα : 0 < α) (hεr : 0 < εr) (hεb : 0 < εb)
    (hεr₀ : εr ≤ εr₀) (hεb₀ : εb ≤ εb₀)
    (hCr : 0 < Cr) (hCb : 0 < Cb)
    (hsr : ∀ i, Pp.xr i ∈ U) (hsb : ∀ i, Pp.xb i ∈ Gamma)
    (hmassR : MasaBolaSuperior Pp.μr U εr₀ Cr 2)
    (hmassB : MasaBolaSuperior Pp.μb Gamma εb₀ Cb 1)
    (hHolder : CotasHolder Pp Hm U Gamma α Sf Sg)
    (hm g : H) (hmin : Pp.EsMinimizadorGlobal Hm hm)
    (hg : Pp.ComparadorExacto Hm g)
    (hRstar : Pp.regularidadTotal g ≤ Rstar)
    (hint : Pp.PoblacionIntegrable hm)
    (haR : Pp.regularizadorR =
      pesoRegularizacionIgual Pp.lambdaR Pp.lambdaB εr εb α
        (factorCoberturaCuadrado mr mb Cr Cb εr εb))
    (haB : Pp.regularizadorB =
      pesoRegularizacionIgual Pp.lambdaR Pp.lambdaB εr εb α
        (factorCoberturaCuadrado mr mb Cr Cb εr εb)) :
    Pp.perdidaPoblacional hm ≤
      factorCoberturaCuadrado mr mb Cr Cb εr εb *
        (pesoRegularizacionIgual Pp.lambdaR Pp.lambdaB εr εb α
          (factorCoberturaCuadrado mr mb Cr Cb εr εb) * Rstar) +
      3 * Pp.lambdaR * εr ^ (2 * α) * Sf ^ 2 +
      3 * Pp.lambdaB * εb ^ (2 * α) * Sg ^ 2 := by
  have hr : MuestrasCubren U Pp.xr εr := by
    have heq : Pp.xr = fun i : Fin mr => Z i ω := funext hsampleR
    rw [heq]
    exact ocupacion_implica_cobertura Z mr U cellsR εr hcoverR hdiamR ω hoccR
  have hb : MuestrasCubren Gamma Pp.xb εb := by
    have heq : Pp.xb = fun i : Fin mb => Zb i ω := funext hsampleB
    rw [heq]
    exact ocupacion_implica_cobertura Zb mb Gamma cellsB εb hcoverB hdiamB ω hoccB
  exact perdidaPoblacional_minimizador_bajo_cobertura Pp Hm U Gamma
    hU hGamma hμr hμb α εr εb εr₀ εb₀ Cr Cb Sf Sg Rstar
    hα hεr hεb hεr₀ hεb₀ hCr hCb hsr hsb hr hb hmassR hmassB
    hHolder hm g hmin hg hRstar hint haR haB

#print axioms TesisPINN.celdaVacia_measurable
#print axioms TesisPINN.medida_celdaVacia
#print axioms TesisPINN.medidaReal_celdaVacia_le_exp
#print axioms TesisPINN.todasCeldasOcupadas_measurable
#print axioms TesisPINN.medida_falloOcupacion_le_suma
#print axioms TesisPINN.medidaReal_falloOcupacion_le_exp
#print axioms TesisPINN.cardinal_por_masa_minima
#print axioms TesisPINN.falloOcupacion_le_escala_raiz
#print axioms TesisPINN.ocupacion_implica_cobertura
#print axioms TesisPINN.ocupacion_eventual_casi_segura
#print axioms TesisPINN.cobertura_eventual_casi_segura
#print axioms TesisPINN.tsum_fallos_ne_top_de_mayorante
#print axioms TesisPINN.sumable_sqrt_mul_exp_neg_sqrt
#print axioms TesisPINN.sumable_escala_raiz_de_tamanos
#print axioms TesisPINN.escalaAuxiliarRaiz_masa
#print axioms TesisPINN.cobertura_eventual_escala_raiz
#print axioms TesisPINN.cobertura_eventual_de_particiones_raiz
#print axioms TesisPINN.coberturas_cuadrado_eventuales_casi_seguras
#print axioms TesisPINN.perdidaPoblacional_de_ocupacion

end TesisPINN
