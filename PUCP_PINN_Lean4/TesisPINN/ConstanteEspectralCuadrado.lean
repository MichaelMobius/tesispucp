import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Certificado de la constante de la Proposición 3.22. Los índices naturales
representan frecuencias estrictamente positivas mediante el desplazamiento uno. -/

noncomputable section

namespace TesisPINN

open Filter
open scoped Topology

def denominadorEspectral (j k : ℕ) : ℕ := ((j + 1) ^ 2 + (k + 1) ^ 2) ^ 2

def terminoEspectral (p : ℕ × ℕ) : ℝ := 1 / (denominadorEspectral p.1 p.2 : ℝ)

def cuadradoIndices (N : ℕ) : Finset (ℕ × ℕ) := (Finset.range N) ×ˢ (Finset.range N)

def sumaEspectralFinita (N : ℕ) : ℝ := ∑ p ∈ cuadradoIndices N, terminoEspectral p

def sumaEspectral : ℝ := ∑' p : ℕ × ℕ, terminoEspectral p

def constanteEspectralCuadrado : ℝ := 4 / Real.pi ^ 2 * Real.sqrt sumaEspectral

private theorem terminoEspectral_nonneg (p : ℕ × ℕ) : 0 ≤ terminoEspectral p := by
  unfold terminoEspectral
  positivity

private def redondeoEspectral (j k : ℕ) : ℕ :=
  let d := denominadorEspectral j k
  (10 ^ 12 + d - 1) / d

private def sumaRedondeos (N : ℕ) : ℕ :=
  ((List.range N).map fun j => ((List.range N).map fun k => redondeoEspectral j k).sum).sum

private theorem suma_lista_rango {A : Type*} [AddCommMonoid A] (N : ℕ) (f : ℕ → A) :
    ((List.range N).map f).sum = ∑ n ∈ Finset.range N, f n := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, Finset.sum_range_succ, ih]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem certificado_entero_espectral : sumaRedondeos 100 = 424316479249 := by
  decide +kernel

private theorem terminoEspectral_le_redondeo (j k : ℕ) :
    terminoEspectral (j, k) ≤ (redondeoEspectral j k : ℝ) / 10 ^ 12 := by
  let d := denominadorEspectral j k
  have hd : 0 < d := by dsimp [d, denominadorEspectral]; positivity
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hn : 10 ^ 12 ≤ (d - 1 + 10 ^ 12) / d * d := by
    have hmod := Nat.mod_lt (d - 1 + 10 ^ 12) hd
    have hdiv := Nat.mod_add_div (d - 1 + 10 ^ 12) d
    rw [Nat.mul_comm d] at hdiv
    omega
  have hn' : 10 ^ 12 ≤ redondeoEspectral j k * d := by
    change 10 ^ 12 ≤ (10 ^ 12 + d - 1) / d * d
    rw [show 10 ^ 12 + d - 1 = d - 1 + 10 ^ 12 by omega]
    exact hn
  have hcast : (10 : ℝ) ^ 12 ≤ (redondeoEspectral j k : ℝ) * d := by exact_mod_cast hn'
  change (1 : ℝ) / (d : ℝ) ≤ (redondeoEspectral j k : ℝ) / 10 ^ 12
  apply (div_le_div_iff₀ hdR (by norm_num : (0 : ℝ) < 10 ^ 12)).2
  simpa using hcast

set_option maxRecDepth 4096 in
theorem sumaEspectralFinita_cien : sumaEspectralFinita 100 < (424317 / 1000000 : ℝ) := by
  unfold sumaEspectralFinita cuadradoIndices
  rw [Finset.sum_product]
  have h := Finset.sum_le_sum (s := Finset.range 100) fun j _ =>
    Finset.sum_le_sum (s := Finset.range 100) fun k _ => terminoEspectral_le_redondeo j k
  refine h.trans_lt ?_
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
  norm_cast
  have hsum : (∑ j ∈ Finset.range 100, ∑ k ∈ Finset.range 100, redondeoEspectral j k) =
      424316479249 := by
    simpa only [sumaRedondeos, suma_lista_rango] using certificado_entero_espectral
  rw [hsum]
  norm_num

private theorem terminoEspectral_le_nivel (j k N : ℕ) (h : j = N ∨ k = N) :
    terminoEspectral (j, k) ≤ 1 / ((N : ℝ) + 1) ^ 4 := by
  simp only [terminoEspectral, denominadorEspectral, Prod.fst, Prod.snd, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one]
  apply one_div_le_one_div_of_le (by positivity)
  rcases h with rfl | rfl
  · nlinarith [sq_nonneg ((j : ℝ) + 1), sq_nonneg ((k : ℝ) + 1),
      mul_nonneg (sq_nonneg ((j : ℝ) + 1)) (sq_nonneg ((k : ℝ) + 1))]
  · nlinarith [sq_nonneg ((j : ℝ) + 1), sq_nonneg ((k : ℝ) + 1),
      mul_nonneg (sq_nonneg ((j : ℝ) + 1)) (sq_nonneg ((k : ℝ) + 1))]

/-- La diferencia de dos cuadrados de índices consta de una fila y una
columna sin repetir la esquina. Para el nivel positivo `N+1` son `2N+1` términos. -/
theorem sumaEspectralFinita_nivel (N : ℕ) :
    sumaEspectralFinita (N + 1) ≤ sumaEspectralFinita N +
      (2 * (N : ℝ) + 1) / ((N : ℝ) + 1) ^ 4 := by
  have h₁ : (∑ j ∈ Finset.range N, terminoEspectral (j, N)) ≤
      (N : ℝ) * (1 / ((N : ℝ) + 1) ^ 4) := by
    simpa using Finset.sum_le_sum (s := Finset.range N) fun j _ =>
      terminoEspectral_le_nivel j N N (Or.inr rfl)
  have h₂ : (∑ k ∈ Finset.range (N + 1), terminoEspectral (N, k)) ≤
      ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1) ^ 4) := by
    simpa using Finset.sum_le_sum (s := Finset.range (N + 1)) fun k _ =>
      terminoEspectral_le_nivel N k N (Or.inl rfl)
  simp only [sumaEspectralFinita, cuadradoIndices, Finset.sum_product]
  rw [Finset.sum_range_succ]
  have he : (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range (N + 1), terminoEspectral (j, k)) =
      (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, terminoEspectral (j, k)) +
        ∑ j ∈ Finset.range N, terminoEspectral (j, N) := by
    simp_rw [Finset.sum_range_succ (n := N) (f := fun k => terminoEspectral (_, k))]
    rw [Finset.sum_add_distrib]
  rw [he]
  linarith only [h₁, h₂, show (2 * (N : ℝ) + 1) / ((N : ℝ) + 1) ^ 4 =
    ((N : ℝ) + ((N : ℝ) + 1)) * (1 / ((N : ℝ) + 1) ^ 4) by ring]

private theorem nivel_le_telescopica (N : ℕ) (hN : 0 < N) :
    (2 * (N : ℝ) + 1) / ((N : ℝ) + 1) ^ 4 ≤
      1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2 := by
  have hp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hq : 0 < (N : ℝ) + 1 := by positivity
  field_simp
  nlinarith only [sq_nonneg (N : ℝ), hp]

private theorem sumaFinita_le_telescopica (N k : ℕ) (hN : 0 < N) :
    sumaEspectralFinita (N + k) ≤
      sumaEspectralFinita N + 1 / (N : ℝ) ^ 2 - 1 / ((N + k : ℕ) : ℝ) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc]
    have ht := nivel_le_telescopica (N + k) (by omega)
    have hs := sumaEspectralFinita_nivel (N + k)
    push_cast at ih ht hs ⊢
    linarith only [ih, hs, ht]

private theorem cuadradoIndices_mono : Monotone cuadradoIndices := by
  intro n m h p hp
  simp only [cuadradoIndices, Finset.mem_product, Finset.mem_range] at hp ⊢
  exact ⟨hp.1.trans_le h, hp.2.trans_le h⟩

private theorem eventual_subconjunto_cuadrado (s : Finset (ℕ × ℕ)) :
    ∀ᶠ N in atTop, s ⊆ cuadradoIndices N := by
  classical
  let N := s.sup (fun p => max p.1 p.2) + 1
  apply (eventually_ge_atTop N).mono
  intro n hn p hp
  apply cuadradoIndices_mono hn
  simp only [cuadradoIndices, Finset.mem_product, Finset.mem_range, N]
  have hm := Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp
  exact ⟨Nat.lt_succ_of_le ((le_max_left _ _).trans hm),
    Nat.lt_succ_of_le ((le_max_right _ _).trans hm)⟩

theorem terminoEspectral_sumable : Summable terminoEspectral := by
  apply summable_of_sum_le (fun p => terminoEspectral_nonneg p)
    (c := sumaEspectralFinita 1 + 1)
  intro s
  obtain ⟨N, hs, hN⟩ := ((eventual_subconjunto_cuadrado s).and (eventually_ge_atTop 1)).exists
  have h := sumaFinita_le_telescopica 1 (N - 1) (by decide)
  rw [show 1 + (N - 1) = N by omega] at h
  refine (Finset.sum_le_sum_of_subset_of_nonneg hs fun p _ _ => terminoEspectral_nonneg p).trans ?_
  change sumaEspectralFinita N ≤ _
  norm_num at h
  exact h.trans (sub_le_self _ (by positivity))

theorem sumaEspectral_cola (N : ℕ) (hN : 0 < N) :
    sumaEspectral - sumaEspectralFinita N ≤ 1 / (N : ℝ) ^ 2 := by
  have h : Tendsto cuadradoIndices atTop atTop :=
    tendsto_atTop.2 eventual_subconjunto_cuadrado
  have ht : Tendsto sumaEspectralFinita atTop (𝓝 sumaEspectral) :=
    terminoEspectral_sumable.hasSum.comp h
  apply sub_le_iff_le_add.mpr
  rw [add_comm]
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop N] with n hn
  have h := sumaFinita_le_telescopica N (n - N) hN
  rw [show N + (n - N) = n by omega] at h
  exact h.trans (sub_le_self _ (by positivity))

theorem sumaEspectral_lt : sumaEspectral < (424417 / 1000000 : ℝ) := by
  have h := sumaEspectral_cola 100 (by decide)
  norm_num at h
  linarith [sumaEspectralFinita_cien]

theorem constanteEspectralCuadrado_lt : constanteEspectralCuadrado < (26404 / 100000 : ℝ) := by
  have hπ : (3141592 / 1000000 : ℝ) < Real.pi := by
    convert Real.pi_gt_d6 using 1 <;> norm_num
  have hroot : Real.sqrt sumaEspectral ≤ Real.sqrt (424417 / 1000000 : ℝ) :=
    Real.sqrt_le_sqrt sumaEspectral_lt.le
  have hrat : 4 / (3141592 / 1000000 : ℝ) ^ 2 * Real.sqrt (424417 / 1000000 : ℝ) <
      (26404 / 100000 : ℝ) := by
    have hh : Real.sqrt (424417 / 1000000 : ℝ) < (65148 / 100000 : ℝ) := by
      apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by norm_num)).1
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    exact (mul_lt_mul_of_pos_left hh (by norm_num)).trans_le (by norm_num)
  refine lt_of_le_of_lt (mul_le_mul ?_ hroot (Real.sqrt_nonneg _) (by positivity)) hrat
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    ((sq_le_sq₀ (by norm_num) Real.pi_pos.le).2 hπ.le)

#check sumaEspectral_cola
#check constanteEspectralCuadrado_lt
#print axioms certificado_entero_espectral
#print axioms sumaEspectralFinita_cien
#print axioms sumaEspectral_cola
#print axioms constanteEspectralCuadrado_lt

end TesisPINN
