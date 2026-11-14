import TesisPINN.ArquitecturaCuadratica
import TesisPINN.PuentePoisson38_320
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Funext

/-! Realización exacta de la clase polinómica del Lema 3.24. -/

noncomputable section

namespace TesisPINN

open scoped BigOperators

abbrev IndiceMonomio (D : ℕ) := Fin (D + 1) × Fin (D + 1)

abbrev Coeficientes324 (D : ℕ) := IndiceMonomio D → ℝ

def monomio324 {D : ℕ} (p : IndiceMonomio D) (x : Bool → ℝ) : ℝ :=
  x true ^ (p.1 : ℕ) * x false ^ (p.2 : ℕ)

def polinomio324 {D : ℕ} (a : Coeficientes324 D) (x : Bool → ℝ) : ℝ :=
  ∑ p, a p * monomio324 p x

def factor324 (x : Bool → ℝ) : ℝ := (1 - x true ^ 2) * (1 - x false ^ 2)

theorem factor324_eq_psiCuadrado (x : Plano) :
    factor324 (fun s => if s then x 0 else x 1) = psiCuadrado x := by
  simp [factor324, psiCuadrado]

def clase324 (D : ℕ) : Set ((Bool → ℝ) → ℝ) :=
  Set.range (fun a : Coeficientes324 D => fun x => factor324 x * polinomio324 a x)

/-- Enumera el banco con el segundo exponente como el índice que varía más rápido. -/
def enumeracion324 (D : ℕ) : IndiceMonomio D ≃ Fin ((D + 1) ^ 2) :=
  finProdFinEquiv.trans (finCongr (by simp [pow_two]))

theorem cardinal_indiceMonomio (D : ℕ) : Fintype.card (IndiceMonomio D) = (D + 1) ^ 2 := by
  simp [Fintype.card_prod, pow_two]

def mapaCoeficientes324 (D : ℕ) : Coeficientes324 D →ₗ[ℝ] ((Bool → ℝ) → ℝ) where
  toFun a x := factor324 x * polinomio324 a x
  map_add' a b := by
    funext x
    simp [polinomio324, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c a := by
    funext x
    simp [polinomio324, mul_assoc, ← Finset.mul_sum, mul_left_comm]

private def exponentes324 {D : ℕ} (p : IndiceMonomio D) : Bool →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun b => if b then p.1.val else p.2.val)

private theorem exponentes324_injective (D : ℕ) :
    Function.Injective (exponentes324 (D := D)) := by
  intro p q h
  have he := Finsupp.equivFunOnFinite.symm.injective h
  exact Prod.ext (Fin.ext (congrFun he true)) (Fin.ext (congrFun he false))

def polinomioFormal324 {D : ℕ} (a : Coeficientes324 D) : MvPolynomial Bool ℝ :=
  ∑ p, MvPolynomial.monomial (exponentes324 p) (a p)

@[simp] theorem polinomioFormal324_eval {D : ℕ} (a : Coeficientes324 D) (x : Bool → ℝ) :
    MvPolynomial.eval x (polinomioFormal324 a) = polinomio324 a x := by
  classical
  simp only [polinomioFormal324, polinomio324, map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finsupp.prod_fintype _ _ (fun b => pow_zero (x b))]
  simp [exponentes324, monomio324, mul_assoc, mul_comm, mul_left_comm]

private theorem polinomioFormal324_coef {D : ℕ} (a : Coeficientes324 D)
    (s : Bool →₀ ℕ) :
    (polinomioFormal324 a).coeff s =
      ∑ p, if exponentes324 p = s then a p else 0 := by
  classical
  simp only [polinomioFormal324, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

theorem polinomioFormal324_degreeOf {D : ℕ} (a : Coeficientes324 D) (b : Bool) :
    (polinomioFormal324 a).degreeOf b ≤ D := by
  classical
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro s hs
  by_contra! h
  apply (MvPolynomial.mem_support_iff.mp hs)
  rw [polinomioFormal324_coef]
  apply Finset.sum_eq_zero
  intro p _
  have he : exponentes324 p b ≤ D := by
    cases b
    · exact Nat.le_of_lt_succ p.2.isLt
    · exact Nat.le_of_lt_succ p.1.isLt
  have hne : exponentes324 p ≠ s := by
    intro heq
    exact (not_le_of_gt h) (heq ▸ he)
  simp [hne]

theorem polinomioFormal324_biyectivo_en_grado {D : ℕ} :
    Set.range (polinomioFormal324 (D := D)) =
      {q : MvPolynomial Bool ℝ | ∀ b, q.degreeOf b ≤ D} := by
  classical
  ext q
  constructor
  · rintro ⟨a, rfl⟩ b
    exact polinomioFormal324_degreeOf a b
  · intro hq
    let a : Coeficientes324 D := fun p => q.coeff (exponentes324 p)
    refine ⟨a, MvPolynomial.ext _ _ fun s => ?_⟩
    rw [polinomioFormal324_coef]
    by_cases hs : s ∈ q.support
    · have h₁ := MvPolynomial.degreeOf_le_iff.mp (hq true) s hs
      have h₂ := MvPolynomial.degreeOf_le_iff.mp (hq false) s hs
      let p : IndiceMonomio D := (⟨s true, Nat.lt_succ_of_le h₁⟩, ⟨s false, Nat.lt_succ_of_le h₂⟩)
      have he : exponentes324 p = s := by
        ext b
        cases b <;> rfl
      rw [Finset.sum_eq_single p]
      · simp [he, a]
      · intro j _ h
        rw [ite_eq_right (fun eq => h (exponentes324_injective D (eq.trans he.symm)))]
      · simp
    · have hz := MvPolynomial.notMem_support_iff.mp hs
      rw [hz]
      apply Finset.sum_eq_zero
      intro p _
      by_cases he : exponentes324 p = s <;> simp [a, he, hz]

theorem mapaCoeficientes324_inyectivo (D : ℕ) :
    Function.Injective (mapaCoeficientes324 D) := by
  classical
  intro a b h
  have hp : polinomioFormal324 a = polinomioFormal324 b := by
    apply MvPolynomial.funext_set (fun _ => Set.Ioo (-1 : ℝ) 1)
      (fun _ => Set.Ioo_infinite (by norm_num))
    intro x hx
    have hx' (s : Bool) : x s ∈ Set.Ioo (-1 : ℝ) 1 := hx s (Set.mem_univ _)
    have hpos (s : Bool) : 0 < 1 - x s ^ 2 := by
      have hh := hx' s
      exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr (abs_lt.mpr hh))
    have hfactor : factor324 x ≠ 0 := (mul_pos (hpos true) (hpos false)).ne'
    have he' : factor324 x * polinomio324 a x = factor324 x * polinomio324 b x :=
      congrFun h x
    simpa only [polinomioFormal324_eval] using mul_left_cancel₀ hfactor he'
  funext p
  have hc := congrArg (fun q : MvPolynomial Bool ℝ => q.coeff (exponentes324 p)) hp
  simp only [polinomioFormal324_coef, (exponentes324_injective D).eq_iff] at hc
  simpa using hc

private def grado {D : ℕ} (p : IndiceMonomio D) : ℕ := p.1.val + p.2.val

private def indice {D : ℕ} (i j : ℕ) (hi : i ≤ D) (hj : j ≤ D) : IndiceMonomio D :=
  (⟨i, by omega⟩, ⟨j, by omega⟩)

private def uno {D : ℕ} : IndiceMonomio D := indice 0 0 (Nat.zero_le _) (Nat.zero_le _)

private def ix {D : ℕ} (hD : 1 ≤ D) : IndiceMonomio D := indice 1 0 hD (Nat.zero_le _)

private def iy {D : ℕ} (hD : 1 ≤ D) : IndiceMonomio D := indice 0 1 (Nat.zero_le _) hD

private def valorBanco {D : ℕ} (k : ℕ) (x : Bool → ℝ) (p : IndiceMonomio D) : ℝ :=
  if grado p ≤ k then monomio324 p x else 0

private def capaInicial {D : ℕ} (hD : 1 ≤ D) :
    CapaCuadratica Bool (IndiceMonomio D × Bool) :=
  codificarCapa (fun p s => if p = (if s then ix hD else iy hD) then 1 else 0)
    (fun p => if p = uno then 1 else 0)

private theorem capaInicial_eval {D : ℕ} (hD : 1 ≤ D) (x : Bool → ℝ) :
    (capaInicial hD).eval x = banco (valorBanco 1 x) := by
  rw [capaInicial, codificarCapa_eval]
  congr 1
  funext p
  rcases p with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  have h₀ : (⟨i, hi⟩, ⟨j, hj⟩) = (uno : IndiceMonomio D) ↔ i = 0 ∧ j = 0 := by
    simp [uno, indice, Fin.ext_iff]
  have h₁ : (⟨i, hi⟩, ⟨j, hj⟩) = ix hD ↔ i = 1 ∧ j = 0 := by
    simp [ix, indice, Fin.ext_iff]
  have h₂ : (⟨i, hi⟩, ⟨j, hj⟩) = iy hD ↔ i = 0 ∧ j = 1 := by
    simp [iy, indice, Fin.ext_iff]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, h₀, h₁, h₂,
    valorBanco, grado, monomio324]
  by_cases h : i + j ≤ 1
  · have hh : (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) := by omega
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · have ha : ¬(i = 0 ∧ j = 0) := by omega
    have hb : ¬(i = 1 ∧ j = 0) := by omega
    have hc : ¬(i = 0 ∧ j = 1) := by omega
    simp [h, ha, hb, hc]

private def anteriorX {D : ℕ} (p : IndiceMonomio D) : IndiceMonomio D :=
  (⟨p.1.val - 1, by have := p.1.isLt; omega⟩, p.2)

private def anteriorY {D : ℕ} (p : IndiceMonomio D) : IndiceMonomio D :=
  (p.1, ⟨p.2.val - 1, by have := p.2.isLt; omega⟩)

private def ronda {D : ℕ} (hD : 1 ≤ D) (k : ℕ) (p : IndiceMonomio D) :
    OperacionRegistro (IndiceMonomio D) :=
  if grado p = k + 1 then
    if 0 < p.1.val then .producto (ix hD) (anteriorX p)
    else .producto (iy hD) (anteriorY p)
  else .copiar p

private theorem ronda_valor {D : ℕ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    (x : Bool → ℝ) (p : IndiceMonomio D) :
    (ronda hD k p).valor (valorBanco k x) = valorBanco (k + 1) x p := by
  by_cases hp : grado p = k + 1
  · have hX : valorBanco k x (ix hD) = x true := by
      simp [valorBanco, grado, ix, indice, monomio324, hk]
    have hY : valorBanco k x (iy hD) = x false := by
      simp [valorBanco, grado, iy, indice, monomio324, hk]
    by_cases hi : 0 < p.1.val
    · have ha : grado (anteriorX p) ≤ k := by
        simp only [grado, anteriorX] at hp ⊢
        omega
      have he : p.1.val - 1 + 1 = p.1.val := by omega
      have hm : monomio324 p x = x true * monomio324 (anteriorX p) x := by
        unfold monomio324
        change x true ^ p.1.val * x false ^ p.2.val =
          x true * (x true ^ (p.1.val - 1) * x false ^ p.2.val)
        conv_lhs => rw [← he, pow_succ]
        ring
      rw [ronda, ite_eq_left hp, ite_eq_left hi, OperacionRegistro.valor, hX]
      simp [valorBanco, ha, hp, hm]
    · have ha : grado (anteriorY p) ≤ k := by
        simp only [grado, anteriorY] at hp ⊢
        omega
      have he : p.2.val - 1 + 1 = p.2.val := by
        simp only [grado] at hp
        omega
      have hm : monomio324 p x = x false * monomio324 (anteriorY p) x := by
        unfold monomio324
        change x true ^ p.1.val * x false ^ p.2.val =
          x false * (x true ^ p.1.val * x false ^ (p.2.val - 1))
        conv_lhs => rw [← he, pow_succ]
        ring
      rw [ronda, ite_eq_left hp, ite_eq_right hi, OperacionRegistro.valor, hY]
      simp [valorBanco, ha, hp, hm]
  · have he : (grado p ≤ k) = (grado p ≤ k + 1) := propext (by omega)
    simp [ronda, hp, OperacionRegistro.valor, valorBanco, he]

private def redMonomios {D : ℕ} (hD : 1 ≤ D) :
    ℕ → CapasCuadraticas Bool (IndiceMonomio D × Bool)
  | 0 => (CapasCuadraticas.vacia Bool).agregar (capaInicial hD)
  | n + 1 => bloqueRegistros (redMonomios hD n) (ronda hD (n + 1))

private theorem redMonomios_eval {D : ℕ} (hD : 1 ≤ D) (n : ℕ) (x : Bool → ℝ) :
    (redMonomios hD n).eval x = banco (valorBanco (n + 1) x) := by
  induction n with
  | zero => exact capaInicial_eval hD x
  | succ n ih =>
    rw [redMonomios, bloqueRegistros_eval _ _ _ _ ih]
    simp_rw [ronda_valor hD (by omega : 1 ≤ n + 1) x]

private theorem redMonomios_dimensiones {D : ℕ} (hD : 1 ≤ D) (n : ℕ) :
    (redMonomios hD n).dimensiones = List.replicate (1 + 2 * n) (2 * (D + 1) ^ 2) := by
  induction n with
  | zero => simp [redMonomios, CapasCuadraticas.dimensiones, Fintype.card_prod, pow_two,
      Nat.mul_comm]
  | succ n ih =>
    rw [redMonomios, bloqueRegistros_dimensiones, ih, cardinal_indiceMonomio,
      show 1 + 2 * (n + 1) = (1 + 2 * n) + 2 by omega]
    exact (List.replicate_add (1 + 2 * n) 2 _).symm

private theorem redMonomios_completo {D : ℕ} (hD : 1 ≤ D) (x : Bool → ℝ) :
    (redMonomios hD (2 * D - 1)).eval x = banco (fun p => monomio324 p x) := by
  rw [redMonomios_eval]
  congr 1
  funext p
  have hp : grado p ≤ 2 * D - 1 + 1 := by
    have ha := p.1.isLt
    have hb := p.2.isLt
    simp only [grado]
    omega
  simp [valorBanco, hp]

private def capaFactor {D : ℕ} (hD : 2 ≤ D) :
    CapaCuadratica (IndiceMonomio D × Bool) ((IndiceMonomio D ⊕ Unit) × Bool) :=
  desdeRegistros (codificarCapa
    (fun j p => match j with
      | .inl i => filaRegistro i p
      | .inr _ => -filaRegistro (indice 2 0 hD (Nat.zero_le _)) p -
          filaRegistro (indice 0 2 (Nat.zero_le _) hD) p + filaRegistro (indice 2 2 hD hD) p)
    (fun j => match j with
      | .inl _ => 0
      | .inr _ => 1))

private theorem capaFactor_eval {D : ℕ} (hD : 2 ≤ D) (x : Bool → ℝ) :
    (capaFactor hD).eval (banco (fun p : IndiceMonomio D => monomio324 p x)) =
      banco (Sum.elim (fun p => monomio324 p x) (fun _ => factor324 x)) := by
  rw [capaFactor, desdeRegistros_eval, codificarCapa_eval]
  simp only [banco, decodificar_codificar]
  congr 1
  funext p
  cases p with
  | inl p => simp
  | inr u =>
    rw [factor324, factor_frontera]
    simp [sub_mul, add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, indice, monomio324]
    ring

/-- Las capas ocultas dependen solo del grado. La última capa conserva
los pares codificados de los monomios multiplicados por el factor de frontera. -/
def red324 {D : ℕ} (hD : 2 ≤ D) : CapasCuadraticas Bool (IndiceMonomio D × Bool) :=
  bloqueRegistros ((redMonomios (show 1 ≤ D by omega) (2 * D - 1)).agregar (capaFactor hD))
    (fun p => .producto (.inr ()) (.inl p))

theorem red324_eval {D : ℕ} (hD : 2 ≤ D) (x : Bool → ℝ) :
    (red324 hD).eval x = banco (fun p => factor324 x * monomio324 p x) := by
  unfold red324
  apply bloqueRegistros_eval _ _ _ (Sum.elim (fun p => monomio324 p x) (fun _ => factor324 x))
  change (capaFactor hD).eval ((redMonomios _ _).eval x) = _
  rw [redMonomios_completo, capaFactor_eval]

theorem red324_dimensiones {D : ℕ} (hD : 2 ≤ D) :
    (red324 hD).dimensiones =
      List.replicate (1 + 2 * (2 * D - 1)) (2 * (D + 1) ^ 2) ++
        [2 * ((D + 1) ^ 2 + 1), 2 * (D + 1) ^ 2, 2 * (D + 1) ^ 2] := by
  rw [red324, bloqueRegistros_dimensiones, CapasCuadraticas.dimensiones, redMonomios_dimensiones]
  simp [Fintype.card_prod, Fintype.card_sum, pow_two, Nat.mul_comm]

def pesoSalida324 {D : ℕ} (a : Coeficientes324 D) (j : IndiceMonomio D × Bool) : ℝ :=
  a j.1 * coefRegistro j.2

def pesosSalidaLineales324 (D : ℕ) :
    Coeficientes324 D →ₗ[ℝ] ((IndiceMonomio D × Bool) → ℝ) where
  toFun := pesoSalida324
  map_add' a b := by
    funext j
    simp [pesoSalida324, add_mul]
  map_smul' c a := by
    funext j
    simp [pesoSalida324, mul_assoc]

theorem pesosSalida324_continuos (D : ℕ) :
    Continuous (pesoSalida324 (D := D)) := by
  exact continuous_pi fun j => (continuous_apply j.1).mul continuous_const

theorem red324_salida {D : ℕ} (hD : 2 ≤ D) (a : Coeficientes324 D) (x : Bool → ℝ) :
    (red324 hD).salida (pesoSalida324 a) x = factor324 x * polinomio324 a x := by
  rw [CapasCuadraticas.salida, red324_eval, Fintype.sum_prod_type]
  simp_rw [pesoSalida324, banco, mul_assoc, ← Finset.mul_sum, suma_coefRegistro,
    decodificar_codificar, polinomio324]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem red324_dirichlet {D : ℕ} (hD : 2 ≤ D) (a : Coeficientes324 D)
    (x : Plano) (hx : x ∈ frontier cuadrado) :
    (red324 hD).salida (pesoSalida324 a) (fun s => if s then x 0 else x 1) = 0 := by
  rw [red324_salida, factor324_eq_psiCuadrado, psiCuadrado_cero_frontera x hx, zero_mul]

theorem red324_cotas {D : ℕ} (hD : 2 ≤ D) :
    (red324 hD).profundidad = 4 * D + 2 ∧
      ∀ w ∈ (red324 hD).dimensiones, w ≤ 2 * ((D + 1) ^ 2 + 1) := by
  constructor
  · rw [CapasCuadraticas.profundidad, red324_dimensiones]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  · intro w hw
    rw [red324_dimensiones] at hw
    simp at hw
    rcases hw with ⟨_, rfl⟩ | rfl | rfl <;> omega

theorem clase324_eq_polinomios (D : ℕ) :
    clase324 D =
      {f | ∃ q : MvPolynomial Bool ℝ, (∀ b, q.degreeOf b ≤ D) ∧
        ∀ x, f x = factor324 x * MvPolynomial.eval x q} := by
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨polinomioFormal324 a, polinomioFormal324_degreeOf a, by simp⟩
  · rintro ⟨q, hq, hf⟩
    have hq' : q ∈ Set.range (polinomioFormal324 (D := D)) := by
      rw [polinomioFormal324_biyectivo_en_grado]
      exact hq
    obtain ⟨a, rfl⟩ := hq'
    exact ⟨a, funext fun x => by simpa using (hf x).symm⟩

/-- Arquitectura común del Lema 3.24. Se cuentan las neuronas de cada capa
cuadrática y se excluye la lectura lineal del recuento de capas ocultas. -/
theorem lema324 (m : ℕ) (hm : 1 ≤ m) :
    let D := 4 * m - 1
    let N := (D + 1) ^ 2
    ∃ red : CapasCuadraticas Bool (IndiceMonomio D × Bool),
      (∀ w ∈ red.dimensiones, w ≤ 4 * N + 4) ∧
      red.profundidad ≤ 4 * N - 4 ∧
      Set.range (fun a : Coeficientes324 D => red.salida (pesoSalida324 a)) = clase324 D := by
  dsimp only
  let D := 4 * m - 1
  have hD : 2 ≤ D := by
    dsimp [D]
    omega
  have hc := red324_cotas hD
  refine ⟨red324 hD, ?_, ?_, ?_⟩
  · intro w hw
    change w ≤ 4 * (D + 1) ^ 2 + 4
    exact (hc.2 w hw).trans (by omega)
  · rw [hc.1]
    have hsq : (D + 1) ^ 2 = D * D + 2 * D + 1 := by ring
    rw [hsq]
    omega
  · unfold clase324
    congr 1
    funext a x
    exact red324_salida hD a x

/-- La familia de salidas parametriza exactamente los polinomios con los
dos grados parciales prescritos, multiplicados por el factor de Dirichlet. -/
theorem lema324_grado_parcial (m : ℕ) (hm : 1 ≤ m) :
    let D := 4 * m - 1
    let N := (D + 1) ^ 2
    N = 16 * m ^ 2 ∧
      ∃ red : CapasCuadraticas Bool (IndiceMonomio D × Bool),
        (∀ w ∈ red.dimensiones, w ≤ 4 * N + 4) ∧
        red.profundidad ≤ 4 * N - 4 ∧
        Set.range (fun a : Coeficientes324 D => red.salida (pesoSalida324 a)) =
          {f | ∃ q : MvPolynomial Bool ℝ, (∀ b, q.degreeOf b ≤ D) ∧
            ∀ x, f x = factor324 x * MvPolynomial.eval x q} := by
  dsimp only
  constructor
  · rw [show 4 * m - 1 + 1 = 4 * m by omega]
    ring
  · simpa only [clase324_eq_polinomios] using lema324 m hm

theorem red324_m_uno :
    let red := red324 (D := 3) (by decide)
    Fintype.card (IndiceMonomio 3) = 16 ∧
      red.profundidad = 14 ∧ (∀ w ∈ red.dimensiones, w ≤ 34) := by
  dsimp only
  rw [cardinal_indiceMonomio, CapasCuadraticas.profundidad, red324_dimensiones]
  decide

#check lema324
#check lema324_grado_parcial
#print axioms red324_cotas
#print axioms lema324
#print axioms lema324_grado_parcial
#print axioms red324_m_uno
#print axioms red324_dirichlet
#print axioms clase324_eq_polinomios
#print axioms mapaCoeficientes324_inyectivo

end TesisPINN
