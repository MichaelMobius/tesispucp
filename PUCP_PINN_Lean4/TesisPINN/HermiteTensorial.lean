import TesisPINN.HermiteUnivariado
import TesisPINN.Lema324
import TesisPINN.HermiteRestoComplejo
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Complex.RealDeriv

/-! Nodos distintos de una muestra ordenada y comparador tensorial de Hermite. -/

noncomputable section

namespace TesisPINN

open Polynomial
open scoped Polynomial

def nodosDistintosHermite {m : ℕ} (t : Fin m → ℝ) : Finset ℝ :=
  Finset.univ.image t

theorem nodosDistintosHermite_card {m : ℕ} (t : Fin m → ℝ) :
    (nodosDistintosHermite t).card ≤ m := by
  simpa [nodosDistintosHermite] using (Finset.card_image_le (s := Finset.univ) (f := t))

def nodosOrdenadosHermite {m : ℕ} (t : Fin m → ℝ) :
    Fin (nodosDistintosHermite t).card ↪o ℝ :=
  (nodosDistintosHermite t).orderEmbOfFin rfl

theorem nodo_muestra_en_enumeracion {m : ℕ} (t : Fin m → ℝ) (i : Fin m) :
    ∃ j, nodosOrdenadosHermite t j = t i := by
  change t i ∈ Set.range (nodosOrdenadosHermite t)
  rw [nodosOrdenadosHermite, Finset.range_orderEmbOfFin]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem nodosOrdenadosHermite_mem_Icc {m : ℕ} (t : Fin m → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (-1 : ℝ) 1) (j : Fin (nodosDistintosHermite t).card) :
    nodosOrdenadosHermite t j ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := (nodosDistintosHermite t).orderEmbOfFin_mem rfl j
  change nodosOrdenadosHermite t j ∈ Finset.univ.image t at h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  exact hi ▸ ht i

theorem nodosDistintosHermite_constante {m : ℕ} (hm : 1 ≤ m) (a : ℝ) :
    nodosDistintosHermite (fun _ : Fin m => a) = {a} := by
  ext x
  simp only [nodosDistintosHermite, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    exact h.symm
  · intro h
    exact ⟨⟨0, hm⟩, h.symm⟩

theorem nodosDistintosHermite_uno (t : Fin 1 → ℝ) :
    nodosDistintosHermite t = {t 0} := by
  have ht : t = fun _ => t 0 := funext fun i => congrArg t (Subsingleton.elim i 0)
  exact ht.symm ▸ nodosDistintosHermite_constante (m := 1) le_rfl (t 0)

def hermiteMuestra {m : ℕ} (t : Fin m → ℝ) (datos : ℝ → Fin 4 → ℝ) :
    PolinomiosHermite (nodosDistintosHermite t).card :=
  interpolanteHermite (nodosOrdenadosHermite t) (nodosOrdenadosHermite t).injective
    (fun j => datos (nodosOrdenadosHermite t j.1) j.2)

theorem hermiteMuestra_jet {m : ℕ} (t : Fin m → ℝ) (datos : ℝ → Fin 4 → ℝ)
    (i : Fin m) (k : Fin 4) :
    jetHermite (t i) k (hermiteMuestra t datos) = datos (t i) k := by
  obtain ⟨j, hj⟩ := nodo_muestra_en_enumeracion t i
  rw [← hj]
  exact interpolanteHermite_jet _ _ _ j k

theorem hermiteMuestra_grado {m : ℕ} (hm : 1 ≤ m) (t : Fin m → ℝ) (datos : ℝ → Fin 4 → ℝ) :
    (hermiteMuestra t datos : ℝ[X]).natDegree < 4 * m := by
  let p : ℝ[X] := hermiteMuestra t datos
  by_cases hp : p = 0
  · change p.natDegree < _
    rw [hp, natDegree_zero]
    omega
  have h := (natDegree_lt_iff_degree_lt hp).mpr (mem_degreeLT.mp (hermiteMuestra t datos).property)
  exact h.trans_le (Nat.mul_le_mul_left 4 (nodosDistintosHermite_card t))

def aManufacturada (t : ℝ) : ℝ :=
  if t = 1 then Real.pi / 2 else
    if t = -1 then -(Real.pi / 2) else Real.sin (Real.pi * t) / (1 - t ^ 2)

theorem aManufacturada_extension (t : ℝ) :
    aManufacturadaCompleja (t : ℂ) = (aManufacturada t : ℂ) := by
  by_cases h₁ : t = 1
  · simp [h₁, aManufacturadaCompleja, aManufacturada]
  by_cases h₂ : t = -1
  · subst t
    norm_num [aManufacturadaCompleja, aManufacturada]
  have h₁' : (t : ℂ) ≠ 1 := by exact_mod_cast h₁
  have h₂' : (t : ℂ) ≠ -1 := by exact_mod_cast h₂
  simp [aManufacturadaCompleja, aManufacturada, h₁, h₂, h₁', h₂']

theorem aManufacturada_suave (n : WithTop ℕ∞) : ContDiff ℝ n aManufacturada := by
  have hc : ContDiff ℂ n aManufacturadaCompleja :=
    contDiff_iff_contDiffAt.mpr fun x => (aManufacturadaCompleja_entera x).contDiffAt
  simpa only [aManufacturada_extension, Complex.ofReal_re] using hc.real_of_complex

def solucionManufacturada (x : Plano) : ℝ :=
  Real.sin (Real.pi * x 0) * Real.sin (Real.pi * x 1)

def fuenteManufacturada (x : Plano) : ℝ :=
  -2 * Real.pi ^ 2 * solucionManufacturada x

theorem factor_aManufacturada (t : ℝ) :
    (1 - t ^ 2) * aManufacturada t = Real.sin (Real.pi * t) := by
  by_cases h₁ : t = 1
  · subst t
    simp [aManufacturada, Real.sin_pi]
  by_cases h₂ : t = -1
  · subst t
    simp [aManufacturada, Real.sin_neg, Real.sin_pi]
  have hn : 1 - t ^ 2 ≠ 0 := by
    intro h
    have he : (t - 1) * (t + 1) = 0 := by linarith only [h, show (t - 1) * (t + 1) = t ^ 2 - 1 by ring]
    rcases mul_eq_zero.mp he with he | he
    · exact h₁ (by linarith)
    · exact h₂ (by linarith)
  simp only [aManufacturada, h₁, h₂, ite_false]
  field_simp

theorem solucionManufacturada_factorizada (x : Plano) :
    solucionManufacturada x = psiCuadrado x * (aManufacturada (x 0) * aManufacturada (x 1)) := by
  unfold solucionManufacturada psiCuadrado
  rw [← factor_aManufacturada (x 0), ← factor_aManufacturada (x 1)]
  ring

def datosManufacturados (t : ℝ) (k : Fin 4) : ℝ :=
  iteratedDeriv k aManufacturada t

def factorHermite325 {m : ℕ} (z : Fin m → Plano) (axis : Fin 2) : ℝ[X] :=
  hermiteMuestra (fun j => z j axis) datosManufacturados

theorem factorHermite325_jet {m : ℕ} (z : Fin m → Plano) (axis : Fin 2)
    (i : Fin m) (k : Fin 4) :
    jetHermite (z i axis) k (factorHermite325 z axis) = datosManufacturados (z i axis) k :=
  hermiteMuestra_jet (fun j => z j axis) datosManufacturados i k

def coeficientesHermite325 {m : ℕ} (z : Fin m → Plano) :
    Coeficientes324 (4 * m - 1) :=
  fun p => (factorHermite325 z 0).coeff p.1 * (factorHermite325 z 1).coeff p.2

theorem polinomioHermite325_tensor {m : ℕ} (hm : 1 ≤ m) (z : Fin m → Plano) (x : Bool → ℝ) :
    polinomio324 (coeficientesHermite325 z) x =
      (factorHermite325 z 0).eval (x true) * (factorHermite325 z 1).eval (x false) := by
  have he : 4 * m - 1 + 1 = 4 * m := by omega
  have hx (i : Fin 2) :
      (factorHermite325 z i).eval (x (decide (i = 0))) =
        ∑ j : Fin (4 * m - 1 + 1), (factorHermite325 z i).coeff j * x (decide (i = 0)) ^ j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (factorHermite325 z i).coeff j *
      x (decide (i = 0)) ^ j)]
    exact eval_eq_sum_range' (he ▸ hermiteMuestra_grado hm (fun j => z j i) datosManufacturados) _
  have h₀ := hx 0
  have h₁ := hx 1
  simp at h₀ h₁
  rw [h₀, h₁, Finset.sum_mul, polinomio324, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [coeficientesHermite325, monomio324]
  ring

theorem polinomioHermite325_grado_parcial {m : ℕ} (z : Fin m → Plano) (eje : Bool) :
    (polinomioFormal324 (coeficientesHermite325 z)).degreeOf eje ≤ 4 * m - 1 :=
  polinomioFormal324_degreeOf (coeficientesHermite325 z) eje

def comparador325 {m : ℕ} (z : Fin m → Plano) (x : Plano) : ℝ :=
  psiCuadrado x * ((factorHermite325 z 0).eval (x 0) * (factorHermite325 z 1).eval (x 1))

theorem comparador325_realizacion {m : ℕ} (hm : 1 ≤ m) (z : Fin m → Plano) (x : Plano)
    (hD : 2 ≤ 4 * m - 1) :
    (red324 hD).salida (pesoSalida324 (coeficientesHermite325 z)) (fun b => if b then x 0 else x 1) =
      comparador325 z x := by
  rw [red324_salida, factor324_eq_psiCuadrado, polinomioHermite325_tensor hm]
  rfl

theorem comparador325_dirichlet {m : ℕ} (z : Fin m → Plano) (x : Plano)
    (hx : x ∈ frontier cuadrado) : comparador325 z x = 0 := by
  simp [comparador325, psiCuadrado_cero_frontera x hx]

private theorem iteratedDeriv_eval_polynomial (n : ℕ) (p : ℝ[X]) :
    iteratedDeriv n p.eval = ((derivative^[n]) p).eval := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext x
    exact (((derivative^[n]) p).hasDerivAt x).deriv

private def senoManufacturado (t : ℝ) : ℝ := Real.sin (Real.pi * t)

private def pesoHermite (t : ℝ) : ℝ := 1 - t ^ 2

private theorem eval_polynomial_contDiff {K : Type*} [NontriviallyNormedField K]
    (p : K[X]) (n : WithTop ℕ∞) : ContDiff K n p.eval := by
  have h : (fun x : K => aeval x p) = p.eval := by
    funext x
    exact aeval_algebraMap_apply_eq_algebraMap_eval x p
  rw [← h]
  exact p.contDiff_aeval n

private theorem factorHermite325_peso_jet {m : ℕ} (z : Fin m → Plano)
    (axis : Fin 2) (i : Fin m)
    (n : ℕ) (hn : n ≤ 2) :
    iteratedDeriv n (fun t => pesoHermite t * (factorHermite325 z axis).eval t) (z i axis) =
      iteratedDeriv n senoManufacturado (z i axis) := by
  let a := z i axis
  let q := factorHermite325 z axis
  have hw : ContDiff ℝ n pesoHermite := by unfold pesoHermite; fun_prop
  have hq : ContDiff ℝ n q.eval := eval_polynomial_contDiff q n
  have hA : ContDiffAt ℝ n aManufacturada a := (aManufacturada_suave n).contDiffAt
  have hf : (fun t => pesoHermite t * aManufacturada t) = senoManufacturado :=
    funext factor_aManufacturada
  rw [← hf, iteratedDeriv_fun_mul hw.contDiffAt hq.contDiffAt,
    iteratedDeriv_fun_mul hw.contDiffAt hA]
  apply Finset.sum_congr rfl
  intro j _
  have hlt : n - j < 4 := by omega
  have h := factorHermite325_jet z axis i ⟨n - j, hlt⟩
  rw [jetHermite_eval] at h
  change (((derivative^[n - j]) q).eval) a = iteratedDeriv (n - j) aManufacturada a at h
  rw [← iteratedDeriv_eval_polynomial] at h
  rw [show iteratedDeriv (n - j) q.eval a = iteratedDeriv (n - j) aManufacturada a from h]

private theorem senoManufacturado_deriv (t : ℝ) :
    deriv senoManufacturado t = Real.pi * Real.cos (Real.pi * t) := by
  have hd : HasDerivAt (fun s : ℝ => Real.pi * s) Real.pi t := by
    simpa using (hasDerivAt_id t).const_mul Real.pi
  change deriv (fun s => Real.sin (Real.pi * s)) t = _
  exact hd.sin.deriv.trans (mul_comm _ _)

private theorem senoManufacturado_segunda (t : ℝ) :
    deriv (deriv senoManufacturado) t = -Real.pi ^ 2 * senoManufacturado t := by
  have hd : HasDerivAt (fun s : ℝ => Real.pi * s) Real.pi t := by
    simpa using (hasDerivAt_id t).const_mul Real.pi
  rw [show deriv senoManufacturado = _ from funext senoManufacturado_deriv, (hd.cos.const_mul Real.pi).deriv]
  unfold senoManufacturado
  ring

private theorem laplaciano_separable325 (p q : ℝ → ℝ)
    (hp : ContDiff ℝ 2 p) (hq : ContDiff ℝ 2 q) (x : Plano) :
    laplacianoClásico (fun y => p (y 0) * q (y 1)) x =
      deriv (deriv p) (x 0) * q (x 1) + p (x 0) * deriv (deriv q) (x 1) := by
  let P (i : Fin 2) : Plano →L[ℝ] ℝ := EuclideanSpace.proj i
  have hd (a b : ℝ → ℝ) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
      (y : Plano) (i : Fin 2) :
      derivadaClásica (fun z => a (z 0) * b (z 1)) i y =
        if i = 0 then deriv a (y 0) * b (y 1) else a (y 0) * deriv b (y 1) := by
    have h₀ := (ha (y 0)).hasDerivAt.comp_hasFDerivAt y (P 0).hasFDerivAt
    have h₁ := (hb (y 1)).hasDerivAt.comp_hasFDerivAt y (P 1).hasFDerivAt
    have he := (h₀.mul h₁).fderiv
    unfold derivadaClásica
    change (fderiv ℝ (fun z => a (P 0 z) * b (P 1 z)) y) (basePlano i) = _
    change fderiv ℝ (fun z => a (P 0 z) * b (P 1 z)) y = _ at he
    rw [he]
    fin_cases i <;> simp [P, basePlano, EuclideanSpace.basisFun_apply, EuclideanSpace.single, mul_comm]
  have hp' := hp.differentiable (by norm_num)
  have hq' := hq.differentiable (by norm_num)
  have hp₁ : Differentiable ℝ (deriv p) :=
    (hp.deriv' (n := 1)).differentiable (by norm_num)
  have hq₁ : Differentiable ℝ (deriv q) :=
    (hq.deriv' (n := 1)).differentiable (by norm_num)
  have ha : derivadaClásica (fun y => p (y 0) * q (y 1)) 0 =
      fun y => deriv p (y 0) * q (y 1) :=
    funext fun y => by simpa using hd p q hp' hq' y 0
  have hb : derivadaClásica (fun y => p (y 0) * q (y 1)) 1 =
      fun y => p (y 0) * deriv q (y 1) :=
    funext fun y => by simpa using hd p q hp' hq' y 1
  rw [laplacianoClásico, Fin.sum_univ_two, ha, hb]
  change derivadaClásica (fun y => deriv p (y 0) * q (y 1)) 0 x +
    derivadaClásica (fun y => p (y 0) * deriv q (y 1)) 1 x = _
  rw [hd _ _ hp₁ hq', hd _ _ hp' hq₁]
  simp

theorem laplaciano_solucionManufacturada (x : Plano) :
    laplacianoClásico solucionManufacturada x = fuenteManufacturada x := by
  change laplacianoClásico (fun y => senoManufacturado (y 0) * senoManufacturado (y 1)) x = _
  rw [laplaciano_separable325 _ _ (by unfold senoManufacturado; fun_prop)
    (by unfold senoManufacturado; fun_prop), senoManufacturado_segunda, senoManufacturado_segunda]
  unfold fuenteManufacturada solucionManufacturada senoManufacturado
  ring

theorem comparador325_laplaciano_nodo {m : ℕ} (z : Fin m → Plano) (i : Fin m) :
    laplacianoClásico (comparador325 z) (z i) = fuenteManufacturada (z i) := by
  let p (j : Fin 2) := fun t => pesoHermite t * (factorHermite325 z j).eval t
  have hp (j : Fin 2) : ContDiff ℝ 2 (p j) :=
    (show ContDiff ℝ 2 pesoHermite by unfold pesoHermite; fun_prop).mul
      (eval_polynomial_contDiff (factorHermite325 z j) 2)
  have he : comparador325 z = fun y => p 0 (y 0) * p 1 (y 1) := by
    funext y
    unfold comparador325 psiCuadrado p pesoHermite
    ring
  have hv (j : Fin 2) : p j (z i j) = senoManufacturado (z i j) := by
    simpa only [iteratedDeriv_zero] using factorHermite325_peso_jet z j i 0 (by decide)
  have hd (j : Fin 2) : deriv (deriv (p j)) (z i j) =
      deriv (deriv senoManufacturado) (z i j) := by
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
      iteratedDeriv_zero] using
      factorHermite325_peso_jet z j i 2 (by decide)
  rw [he, laplaciano_separable325 _ _ (hp 0) (hp 1), hv, hv, hd, hd,
    senoManufacturado_segunda, senoManufacturado_segunda]
  unfold fuenteManufacturada solucionManufacturada senoManufacturado
  ring

/-- Derivar primero respecto de la segunda variable y luego respecto de la
primera recupera los jets tensoriales en la cuadrícula de proyecciones. -/
theorem hermite325_jet_mixto {m : ℕ} (z : Fin m → Plano) (i j : Fin m)
    (r s : Fin 4) :
    iteratedDeriv r (fun x =>
      iteratedDeriv s (fun y => (factorHermite325 z 0).eval x *
        (factorHermite325 z 1).eval y) (z j 1)) (z i 0) =
      datosManufacturados (z i 0) r * datosManufacturados (z j 1) s := by
  simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field]
  rw [iteratedDeriv_eval_polynomial, iteratedDeriv_eval_polynomial]
  exact congrArg₂ (· * ·)
    (by simpa only [jetHermite_eval] using factorHermite325_jet z 0 i r)
    (by simpa only [jetHermite_eval] using factorHermite325_jet z 1 j s)

private theorem iteratedDeriv_eje_real (f : ℂ → ℂ) (g : ℝ → ℝ)
    (hf : ContDiff ℂ ⊤ f) (hg : ContDiff ℝ ⊤ g)
    (he : ∀ t : ℝ, f t = (g t : ℂ)) (n : ℕ) (t : ℝ) :
    iteratedDeriv n f t = ((iteratedDeriv n g t : ℝ) : ℂ) := by
  induction n generalizing t with
  | zero => simpa only [iteratedDeriv_zero] using he t
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hdF : Differentiable ℂ (iteratedDeriv n f) :=
      hf.differentiable_iteratedDeriv n (by simp)
    have hdG : Differentiable ℝ (iteratedDeriv n g) :=
      hg.differentiable_iteratedDeriv n (by simp)
    have eq : (fun x : ℝ => iteratedDeriv n f (x : ℂ)) =
        (fun x : ℝ => ((iteratedDeriv n g x : ℝ) : ℂ)) := funext ih
    exact ((hdF (t : ℂ)).hasDerivAt.comp_ofReal.deriv.symm.trans
      (congrArg (fun F : ℝ → ℂ => deriv F t) eq)).trans
        (hdG t).hasDerivAt.ofReal_comp.deriv

private theorem eval_polynomial_analytic (p : ℂ[X]) (z : ℂ) :
    AnalyticAt ℂ p.eval z := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h : (p + q).eval = p.eval + q.eval := funext (fun x => eval_add)
    rw [h]
    exact hp.add hq
  | monomial n a =>
    simp_rw [show (monomial n a).eval = fun z => a * z ^ n from funext (fun x => eval_monomial)]
    fun_prop

theorem factorHermite325_jet_complejo {m : ℕ} (s : Fin m → Plano) (a : Fin 2)
    (j : Fin (nodosDistintosHermite (fun i => s i a)).card) (k : ℕ) (hk : k < 4) :
    let t := nodosOrdenadosHermite (fun i => s i a) j
    let p := (factorHermite325 s a).map Complex.ofRealHom
    iteratedDeriv k (aManufacturadaCompleja - p.eval) (t : ℂ) = 0 := by
  dsimp only
  let v := fun i : Fin m => s i a
  let t := nodosOrdenadosHermite v j
  let q := factorHermite325 s a
  let p := q.map Complex.ofRealHom
  have hA : ContDiff ℂ ⊤ aManufacturadaCompleja :=
    contDiff_iff_contDiffAt.mpr fun x => (aManufacturadaCompleja_entera x).contDiffAt
  have hP : ContDiff ℂ ⊤ p.eval := eval_polynomial_contDiff p ⊤
  have hjet := interpolanteHermite_jet (nodosOrdenadosHermite v)
    (nodosOrdenadosHermite v).injective
    (fun i => datosManufacturados (nodosOrdenadosHermite v i.1) i.2) j ⟨k, hk⟩
  change jetHermite t ⟨k, hk⟩ q = iteratedDeriv k aManufacturada t at hjet
  rw [jetHermite_eval] at hjet
  have hreal : iteratedDeriv k q.eval t = iteratedDeriv k aManufacturada t :=
    (congrFun (iteratedDeriv_eval_polynomial k q) t).trans hjet
  change iteratedDeriv k (aManufacturadaCompleja - p.eval) (t : ℂ) = 0
  rw [iteratedDeriv_sub (hA.contDiffAt.of_le (by simp)) (hP.contDiffAt.of_le (by simp)),
    iteratedDeriv_eje_real _ _ hA (aManufacturada_suave ⊤) aManufacturada_extension,
    iteratedDeriv_eje_real _ _ hP (eval_polynomial_contDiff q ⊤)
      (fun x => eval_map_apply Complex.ofRealHom x), hreal, sub_self]

/-- Aplicación de Cauchy al cociente regularizado del interpolante
real prolongado por evaluación polinómica compleja. -/
theorem factorHermite325_resto_diferencia {m : ℕ} (s : Fin m → Plano) (a : Fin 2)
    (hs : ∀ i, s i a ∈ Set.Icc (-1 : ℝ) 1) {z : ℂ} (hz : ‖z‖ < 4) :
    let t := nodosOrdenadosHermite (fun i => s i a)
    let p := ((factorHermite325 s a).map Complex.ofRealHom).eval
    restoContornoHermite t (aManufacturadaCompleja - p) z = aManufacturadaCompleja z - p z :=
  restoContornoHermite_diferencia _ (nodosOrdenadosHermite _).injective
    (nodosOrdenadosHermite_mem_Icc _ hs) _ _ aManufacturadaCompleja_entera
    (eval_polynomial_analytic _) (factorHermite325_jet_complejo s a) hz

#check comparador325_realizacion
#print axioms hermiteMuestra_jet
#print axioms polinomioHermite325_tensor
#print axioms polinomioHermite325_grado_parcial
#print axioms comparador325_realizacion
#print axioms laplaciano_solucionManufacturada
#print axioms comparador325_laplaciano_nodo
#print axioms hermite325_jet_mixto
#print axioms factorHermite325_resto_diferencia

end TesisPINN
