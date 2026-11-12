import TesisPINN.ConvergenciaUniforme
import EllipticPdes.Existence.ClassicalMaximum
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Estabilidad de Dirichlet en la convención de signo del capítulo III. -/

noncomputable section

namespace TesisPINN

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace ENNReal
open EllipticPdes.Classical
open EllipticPdes.Sobolev (partialD partialD_apply)

abbrev EspacioEliptico (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure OperadorEliptico (d : ℕ) where
  a : EspacioEliptico d → Fin d → Fin d → ℝ
  b : EspacioEliptico d → Fin d → ℝ
  c : EspacioEliptico d → ℝ

namespace OperadorEliptico

variable {d : ℕ} (L : OperadorEliptico d)

/-- Convención de la tesis: la parte principal es positiva. -/
def aplica (v : EspacioEliptico d → ℝ) (x : EspacioEliptico d) : ℝ :=
  -nondivOp L.a (fun y i => -L.b y i) (fun y => -L.c y) v x

theorem aplica_eq_suma (v : EspacioEliptico d → ℝ) (x : EspacioEliptico d) :
    L.aplica v x = (∑ i, ∑ j, L.a x i j * partialD i (partialD j v) x) +
      (∑ j, L.b x j * partialD j v x) + L.c x * v x := by
  simp only [aplica, nondivOp, neg_mul, Finset.sum_neg_distrib]
  ring

private def matriz (x : EspacioEliptico d) := matrixCLM (L.a x)
private def transporte (x : EspacioEliptico d) : EspacioEliptico d :=
  -(WithLp.toLp 2 (L.b x))

private theorem aplica_eq (v : EspacioEliptico d → ℝ) (x : EspacioEliptico d)
    (hv : ContDiffAt ℝ 2 v x) :
    L.aplica v x = -nondivOperator L.matriz L.transporte (fun y => -L.c y) v x := by
  rw [aplica, nondivOp_eq hv]
  rfl

theorem aplica_resta {u v : EspacioEliptico d → ℝ} {x : EspacioEliptico d}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    L.aplica (fun y => u y - v y) x = L.aplica u x - L.aplica v x := by
  rw [L.aplica_eq _ _ (hu.sub hv), L.aplica_eq _ _ hu, L.aplica_eq _ _ hv,
    nondivOperator_sub _ _ _ hu hv]
  ring

theorem aplica_neg {u : EspacioEliptico d → ℝ} {x : EspacioEliptico d}
    (hu : ContDiffAt ℝ 2 u x) : L.aplica (fun y => -u y) x = -L.aplica u x := by
  rw [L.aplica_eq _ _ hu.neg, L.aplica_eq _ _ hu, nondivOperator_neg _ _ _ hu]

theorem aplica_const (k : ℝ) (x : EspacioEliptico d) :
    L.aplica (fun _ => k) x = L.c x * k := by
  rw [L.aplica_eq _ _ contDiffAt_const, nondivOperator_const]
  ring

theorem aplica_mul_const {v : EspacioEliptico d → ℝ} {x : EspacioEliptico d}
    (hv : ContDiffAt ℝ 2 v x) (k : ℝ) :
    L.aplica (fun y => k * v y) x = k * L.aplica v x := by
  have he : (fun y => k * v y) = fun y => 0 + k * v y := by simp
  rw [L.aplica_eq _ _ (contDiffAt_const.mul hv), L.aplica_eq _ _ hv, he,
    nondivOperator_add_smul _ _ _ contDiffAt_const hv, nondivOperator_const]
  ring

structure Datos (U : Set (EspacioEliptico d)) (lam B : ℝ) : Prop where
  lambda_pos : 0 < lam
  B_nonneg : 0 ≤ B
  simetria : ∀ x ∈ U, ∀ i j, L.a x i j = L.a x j i
  elipticidad : ∀ x ∈ U, ∀ ξ : Fin d → ℝ,
    lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, L.a x i j * ξ i * ξ j
  transporte_acotado : ∀ x ∈ U, ∀ i, |L.b x i| ≤ B
  signo : ∀ x ∈ U, L.c x ≤ 0

structure ContinuoEn (U : Set (EspacioEliptico d)) : Prop where
  principal : ∀ i j, ContinuousOn (fun x => L.a x i j) U
  primero : ∀ i, ContinuousOn (fun x => L.b x i) U
  cero : ContinuousOn L.c U

private theorem contDiffOn_partialD {U : Set (EspacioEliptico d)} (hU : IsOpen U)
    {v : EspacioEliptico d → ℝ} {n m : WithTop ℕ∞} (hv : ContDiffOn ℝ n v U)
    (hm : m + 1 ≤ n) (i : Fin d) : ContDiffOn ℝ m (partialD i v) U :=
  (hv.fderiv_of_isOpen hU hm).clm_apply contDiffOn_const

theorem aplica_continuo {U : Set (EspacioEliptico d)} (hU : IsOpen U)
    (hL : L.ContinuoEn U) {v : EspacioEliptico d → ℝ} (hv : ContDiffOn ℝ 2 v U) :
    ContinuousOn (L.aplica v) U := by
  simp only [funext (L.aplica_eq_suma v)]
  have h1 (i : Fin d) : ContDiffOn ℝ 1 (partialD i v) U :=
    contDiffOn_partialD hU hv (by decide) i
  have h2 (i j : Fin d) : ContinuousOn (partialD i (partialD j v)) U :=
    (contDiffOn_partialD (m := 0) hU (h1 j) (by decide) i).continuousOn
  exact ((continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
    (hL.principal i j).mul (h2 i j)).add
    (continuousOn_finsetSum _ fun j _ => (hL.primero j).mul (h1 j).continuousOn)).add
    (hL.cero.mul hv.continuousOn)

/-- Principio clásico para el signo de la tesis, derivado del teorema
de EllipticPDE para `-ℒ`. -/
theorem maximo_debil {U : Set (EspacioEliptico d)} {lam B : ℝ}
    (hd : 0 < d) (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hL : L.Datos U lam B) {v : EspacioEliptico d → ℝ}
    (hv : ContDiffOn ℝ 2 v U) (hvc : ContinuousOn v (closure U))
    (hsub : ∀ x ∈ U, 0 ≤ L.aplica v x) (hbd : ∀ x ∈ frontier U, v x ≤ 0) :
    ∀ x ∈ closure U, v x ≤ 0 := by
  obtain ⟨y, hy, hymax⟩ :=
    EllipticPdes.Classical.weak_maximum_principle_of_nonneg hd hU hUb hUne
      hL.lambda_pos hL.simetria hL.elipticidad
      (b := fun x i => -L.b x i) (c := fun x => -L.c x)
      (fun x hx i => by simpa using hL.transporte_acotado x hx i)
      (fun x hx => neg_nonneg.mpr (hL.signo x hx)) hv hvc
      (fun x hx => neg_nonneg.mp (hsub x hx))
  intro x hx
  exact (hymax x hx).trans (max_le (hbd y hy) le_rfl)

end OperadorEliptico

/-- Coeficientes del operador en divergencia del capítulo I. -/
structure OperadorDivergencia (d : ℕ) where
  a : EspacioEliptico d → Fin d → Fin d → ℝ
  b : EspacioEliptico d → Fin d → ℝ
  c : EspacioEliptico d → Fin d → ℝ
  cero : EspacioEliptico d → ℝ

namespace OperadorDivergencia

variable {d : ℕ} (L : OperadorDivergencia d)

def aplica (v : EspacioEliptico d → ℝ) (x : EspacioEliptico d) : ℝ :=
  (∑ i, ∑ j, partialD i (fun y => L.a y i j * partialD j v y) x) +
    (∑ i, partialD i (fun y => L.b y i * v y) x) +
    (∑ j, L.c x j * partialD j v x) + L.cero x * v x

def noDivergente : OperadorEliptico d where
  a := L.a
  b x j := (∑ i, partialD i (fun y => L.a y i j) x) + L.b x j + L.c x j
  c x := (∑ i, partialD i (fun y => L.b y i) x) + L.cero x

private theorem parcial_producto (i : Fin d) {p q : EspacioEliptico d → ℝ}
    {x : EspacioEliptico d} (hp : DifferentiableAt ℝ p x) (hq : DifferentiableAt ℝ q x) :
    partialD i (fun y => p y * q y) x = partialD i p x * q x + p x * partialD i q x := by
  rw [partialD_apply, fderiv_fun_mul hp hq]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ← partialD_apply]
  ring

theorem aplica_eq_noDivergente {v : EspacioEliptico d → ℝ} {x : EspacioEliptico d}
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => L.a y i j) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => L.b y i) x) (hv : ContDiffAt ℝ 2 v x) :
    L.aplica v x = L.noDivergente.aplica v x := by
  have hv₁ := hv.differentiableAt (by decide)
  have hpart (j : Fin d) : DifferentiableAt ℝ (partialD j v) x :=
    ((hv.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)).clm_apply
      (differentiableAt_const _)
  have hd (i j : Fin d) :
      partialD i (fun y => L.a y i j * partialD j v y) x =
        partialD i (fun y => L.a y i j) x * partialD j v x +
          L.a x i j * partialD i (partialD j v) x :=
    parcial_producto i (ha i j) (hpart j)
  have hdb (i : Fin d) : partialD i (fun y => L.b y i * v y) x =
      partialD i (fun y => L.b y i) x * v x + L.b x i * partialD i v x :=
    parcial_producto i (hb i) hv₁
  rw [aplica, L.noDivergente.aplica_eq_suma]
  simp only [hd, hdb, noDivergente, Finset.sum_add_distrib, add_mul, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun i j => partialD i (fun y => L.a y i j) x * partialD j v x)]
  ring

theorem continuo_noDivergente {U : Set (EspacioEliptico d)} (hU : IsOpen U)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => L.a x i j) U)
    (hb : ∀ i, ContDiffOn ℝ 1 (fun x => L.b x i) U)
    (hc : ∀ i, ContinuousOn (fun x => L.c x i) U) (h0 : ContinuousOn L.cero U) :
    L.noDivergente.ContinuoEn U := by
  refine ⟨fun i j => (ha i j).continuousOn, fun j => ?_, ?_⟩
  · exact ((continuousOn_finsetSum _ fun i _ =>
      (OperadorEliptico.contDiffOn_partialD (m := 0) hU (ha i j) (by decide) i).continuousOn).add
      (hb j).continuousOn).add (hc j)
  · exact (continuousOn_finsetSum _ fun i _ =>
      (OperadorEliptico.contDiffOn_partialD (m := 0) hU (hb i) (by decide) i).continuousOn).add h0

private theorem abs_suma_le {M : ℝ} (f : Fin d → ℝ) (hf : ∀ i, |f i| ≤ M) :
    |∑ i, f i| ≤ (d : ℝ) * M :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (by simpa using Finset.sum_le_sum (s := Finset.univ) fun i _ => hf i)

/-- Las cotas de la Hipótesis 3.16 controlan los coeficientes que aparecen
tras expandir la divergencia. El mismo mayorante sirve en cada coordenada. -/
theorem cotas_noDivergente {U : Set (EspacioEliptico d)} {M : ℝ}
    (ha : ∀ x ∈ U, ∀ i j, |partialD i (fun y => L.a y i j) x| ≤ M)
    (hb : ∀ x ∈ U, ∀ i, |L.b x i| ≤ M)
    (hDb : ∀ x ∈ U, ∀ i, |partialD i (fun y => L.b y i) x| ≤ M)
    (hc : ∀ x ∈ U, ∀ i, |L.c x i| ≤ M)
    (h0 : ∀ x ∈ U, |L.cero x| ≤ M) :
    (∀ x ∈ U, ∀ i, |L.noDivergente.b x i| ≤ ((d : ℝ) + 2) * M) ∧
      ∀ x ∈ U, |L.noDivergente.c x| ≤ ((d : ℝ) + 1) * M := by
  constructor
  · intro x hx j
    unfold noDivergente
    have hs := abs_suma_le (fun i => partialD i (fun y => L.a y i j) x) (fun i => ha x hx i j)
    calc
      _ ≤ (|∑ i, partialD i (fun y => L.a y i j) x| + |L.b x j|) + |L.c x j| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ _ := by linarith only [hs, hb x hx j, hc x hx j]
  · intro x hx
    unfold noDivergente
    have hs := abs_suma_le (fun i => partialD i (fun y => L.b y i) x) (hDb x hx)
    exact (abs_add_le _ _).trans (by linarith only [hs, h0 x hx])

end OperadorDivergencia

section Barrera

variable {d : ℕ}

def barreraExponencial (γ R : ℝ) (e x : EspacioEliptico d) : ℝ :=
  1 - Real.exp (γ * (⟪e, x⟫ - R))

theorem barreraExponencial_eq (γ R : ℝ) (e : EspacioEliptico d) :
    barreraExponencial γ R e =
      fun x => 1 + (-Real.exp (-γ * R)) * expInner γ e x := by
  funext x
  rw [barreraExponencial, expInner, show γ * (⟪e, x⟫ - R) = -γ * R + γ * ⟪e, x⟫ by ring,
    Real.exp_add]
  ring

theorem barreraExponencial_suave (γ R : ℝ) (e : EspacioEliptico d) :
    ContDiff ℝ 2 (barreraExponencial γ R e) := by
  rw [barreraExponencial_eq]
  exact contDiff_const.add (contDiff_const.mul (contDiff_expInner _ _))

private theorem hasFDerivAt_exp_desplazada (γ R : ℝ) (e x : EspacioEliptico d) :
    HasFDerivAt (fun y => Real.exp (γ * (⟪e, y⟫ - R)))
      (Real.exp (γ * (⟪e, x⟫ - R)) • (γ • innerSL ℝ e)) x :=
  (Real.hasDerivAt_exp _).comp_hasFDerivAt x
    (((innerSL ℝ e).hasFDerivAt.sub_const R).const_mul γ)

theorem derivada_barreraExponencial (γ R : ℝ) (e x ξ : EspacioEliptico d) :
    fderiv ℝ (barreraExponencial γ R e) x ξ =
      -γ * Real.exp (γ * (⟪e, x⟫ - R)) * ⟪e, ξ⟫ := by
  change fderiv ℝ (fun y => 1 - Real.exp (γ * (⟪e, y⟫ - R))) x ξ = _
  rw [((hasFDerivAt_exp_desplazada γ R e x).const_sub 1).fderiv]
  simp
  ring

theorem segunda_derivada_barreraExponencial (γ R : ℝ) (e x ξ η : EspacioEliptico d) :
    fderiv ℝ (fderiv ℝ (barreraExponencial γ R e)) x ξ η =
      -(γ ^ 2) * Real.exp (γ * (⟪e, x⟫ - R)) * ⟪e, ξ⟫ * ⟪e, η⟫ := by
  have hf : fderiv ℝ (barreraExponencial γ R e) =
      fun y => -(Real.exp (γ * (⟪e, y⟫ - R)) • (γ • innerSL ℝ e)) :=
    funext fun y => ((hasFDerivAt_exp_desplazada γ R e y).const_sub 1).fderiv
  rw [hf, fderiv_fun_neg,
    ((hasFDerivAt_exp_desplazada γ R e x).smul_const (γ • innerSL ℝ e)).fderiv]
  simp
  ring

theorem aplica_barreraExponencial (L : OperadorEliptico d)
    (γ R : ℝ) (e x : EspacioEliptico d) :
    L.aplica (barreraExponencial γ R e) x =
      -(γ ^ 2 * ⟪e, L.matriz x e⟫ + γ * ⟪e, (WithLp.toLp 2 (L.b x) : EspacioEliptico d)⟫) *
        Real.exp (γ * (⟪e, x⟫ - R)) + L.c x * barreraExponencial γ R e x := by
  rw [L.aplica_eq _ _ (barreraExponencial_suave γ R e).contDiffAt, barreraExponencial_eq,
    nondivOperator_add_smul _ _ _ contDiffAt_const
      (contDiff_expInner γ e (n := 2)).contDiffAt,
    nondivOperator_const, nondivOperator_expInner]
  simp only [OperadorEliptico.transporte, inner_neg_right]
  rw [show γ * (⟪e, x⟫ - R) = -γ * R + γ * ⟪e, x⟫ by ring, Real.exp_add]
  unfold expInner
  ring

theorem barrera317 (L : OperadorEliptico d) {U : Set (EspacioEliptico d)} {lam B : ℝ}
    (hd : 0 < d) (hUb : Bornology.IsBounded U) (hL : L.Datos U lam B) :
    ∃ C₀ > 0, ∃ ψ : EspacioEliptico d → ℝ,
      ContDiff ℝ 2 ψ ∧ (∀ x ∈ closure U, 0 ≤ ψ x ∧ ψ x ≤ C₀) ∧
      ∀ x ∈ U, L.aplica ψ x ≤ -1 := by
  let i : Fin d := ⟨0, hd⟩
  let e : EspacioEliptico d := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e]
  obtain ⟨r, hr⟩ := hUb.subset_closedBall (0 : EspacioEliptico d)
  have hproj (x : EspacioEliptico d) (hx : x ∈ closure U) : |⟪e, x⟫| ≤ r := by
    have hx' := (closure_minimal hr Metric.isClosed_closedBall) hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx'
    simpa [he] using (abs_real_inner_le_norm e x).trans (by simpa [he] using hx')
  let γ := 2 + 2 * B / lam
  let R := r + 1
  let q := barreraExponencial γ R e
  let k := lam * γ ^ 2 - B * γ
  let δ := Real.exp (γ * (-r - R)) * k
  have hlam := hL.lambda_pos
  have hB := hL.B_nonneg
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have heq : lam * γ = 2 * lam + 2 * B := by dsimp [γ]; field_simp
  have hk : 0 < k := by
    change 0 < lam * γ ^ 2 - B * γ
    rw [show lam * γ ^ 2 - B * γ = (lam * γ - B) * γ by ring, heq]
    apply mul_pos _ hγ
    linarith
  have hδ : 0 < δ := mul_pos (Real.exp_pos _) hk
  have hq (x : EspacioEliptico d) (hx : x ∈ closure U) : 0 ≤ q x ∧ q x ≤ 1 := by
    have hu := (abs_le.mp (hproj x hx)).2
    change 0 ≤ 1 - Real.exp (γ * (⟪e, x⟫ - R)) ∧ 1 - Real.exp (γ * (⟪e, x⟫ - R)) ≤ 1
    have hnon : γ * (⟪e, x⟫ - R) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hγ.le (by dsimp [R]; linarith)
    exact ⟨sub_nonneg.mpr (Real.exp_le_one_iff.mpr hnon),
      sub_le_self _ (Real.exp_nonneg _)⟩
  have hOp (x : EspacioEliptico d) (hx : x ∈ U) : L.aplica q x ≤ -δ := by
    have hA := isUniformlyElliptic_matrixCLM hlam hL.simetria hL.elipticidad
    have ha : lam ≤ ⟪e, L.matriz x e⟫ := by
      simpa [OperadorEliptico.matriz, real_inner_comm] using hA.le_inner_self hx he
    have hb : -B ≤ ⟪e, (WithLp.toLp 2 (L.b x) : EspacioEliptico d)⟫ := by
      simpa [e, EuclideanSpace.inner_single_left] using (abs_le.mp (hL.transporte_acotado x hx i)).1
    have hlo := (abs_le.mp (hproj x (subset_closure hx))).1
    have hexp : Real.exp (γ * (-r - R)) ≤ Real.exp (γ * (⟪e, x⟫ - R)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right hlo R) hγ.le)
    have hcoef : k ≤ γ ^ 2 * ⟪e, L.matriz x e⟫ +
        γ * ⟪e, (WithLp.toLp 2 (L.b x) : EspacioEliptico d)⟫ := by
      dsimp [k]
      nlinarith only [mul_le_mul_of_nonneg_left ha (sq_nonneg γ),
        mul_le_mul_of_nonneg_left hb hγ.le]
    have hcz := mul_nonpos_of_nonpos_of_nonneg (hL.signo x hx) (hq x (subset_closure hx)).1
    change L.aplica (barreraExponencial γ R e) x ≤ -δ
    rw [aplica_barreraExponencial]
    have hprod := mul_le_mul hcoef hexp (Real.exp_nonneg _) (hk.le.trans hcoef)
    dsimp [δ]
    nlinarith only [hprod, hcz]
  refine ⟨δ⁻¹, inv_pos.mpr hδ, fun x => δ⁻¹ * q x, ?_, ?_, ?_⟩
  · exact contDiff_const.mul (barreraExponencial_suave γ R e)
  · intro x hx
    exact ⟨mul_nonneg (inv_nonneg.mpr hδ.le) (hq x hx).1,
      (mul_le_mul_of_nonneg_left (hq x hx).2 (inv_nonneg.mpr hδ.le)).trans_eq (mul_one _)⟩
  · intro x hx
    rw [L.aplica_mul_const (barreraExponencial_suave γ R e).contDiffAt]
    calc
      _ ≤ δ⁻¹ * (-δ) := mul_le_mul_of_nonneg_left (hOp x hx) (inv_nonneg.mpr hδ.le)
      _ = -1 := by rw [mul_neg, inv_mul_cancel₀ hδ.ne']

end Barrera

section Supremo

variable {X : Type*}

theorem abs_le_supResiduo {U : Set X} {v : X → ℝ} {x : X} (hx : x ∈ U)
    (hb : ∃ M : ℝ, ∀ y ∈ U, |v y| ≤ M) : |v x| ≤ supResiduo U v := by
  obtain ⟨M, hM⟩ := hb
  unfold supResiduo
  apply le_csSup (a := |v x|) _
    (Set.mem_insert_of_mem 0 (Set.mem_image_of_mem (fun y => |v y|) hx))
  refine ⟨max M 0, ?_⟩
  intro t ht
  rcases Set.mem_insert_iff.mp ht with rfl | ⟨y, hy, rfl⟩
  · exact le_max_right _ _
  · exact (hM y hy).trans (le_max_left _ _)

theorem supResiduo_nonneg_de_acotada {U : Set X} {v : X → ℝ}
    (hb : ∃ M : ℝ, ∀ y ∈ U, |v y| ≤ M) : 0 ≤ supResiduo U v := by
  obtain ⟨M, hM⟩ := hb
  exact (supResiduo_le U v (max M 0) (le_max_right _ _)
    fun y hy => (hM y hy).trans (le_max_left _ _)).1

theorem supResiduo_congr {U : Set X} {v w : X → ℝ} (h : EqOn v w U) :
    supResiduo U v = supResiduo U w := by
  unfold supResiduo
  rw [Set.image_congr (fun x hx => congrArg abs (h hx))]

theorem supResiduo_closure {X : Type*} [TopologicalSpace X] {U : Set X} {v : X → ℝ}
    (hv : ContinuousOn v (closure U)) (hb : ∃ M : ℝ, ∀ x ∈ closure U, |v x| ≤ M) :
    supResiduo (closure U) v = supResiduo U v := by
  obtain ⟨M, hM⟩ := hb
  have hU : ∃ B : ℝ, ∀ x ∈ U, |v x| ≤ B := ⟨M, fun x hx => hM x (subset_closure hx)⟩
  apply le_antisymm
  · refine (supResiduo_le _ _ _ (supResiduo_nonneg_de_acotada hU) fun x hx => ?_).2
    let : (𝓝[U] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
    exact le_of_tendsto ((hv x hx).abs.mono subset_closure)
      (mem_of_superset self_mem_nhdsWithin fun y hy => abs_le_supResiduo hy hU)
  · exact (supResiduo_le _ _ _ (supResiduo_nonneg_de_acotada ⟨M, hM⟩)
      fun x hx => abs_le_supResiduo (subset_closure hx) ⟨M, hM⟩).2

/-- Una función continua y acotada en un abierto tiene el mismo supremo
puntual y esencial para una medida positiva en abiertos no vacíos. -/
theorem supResiduo_eq_Linfty {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {U : Set X} (hU : IsOpen U) {v : X → ℝ} (hv : ContinuousOn v U)
    (hb : ∃ M : ℝ, ∀ x ∈ U, |v x| ≤ M) :
    supResiduo U v = (eLpNormEssSup v (μ.restrict U)).toReal := by
  obtain ⟨M, hM⟩ := hb
  have hAE : ∀ᵐ x ∂μ.restrict U, ‖v x‖ ≤ M :=
    (ae_restrict_mem hU.measurableSet).mono fun x hx => by simpa [Real.norm_eq_abs] using hM x hx
  have hfin := eLpNormEssSup_lt_top_of_ae_bound hAE
  have ha : ∀ᵐ x ∂μ.restrict U, |v x| ≤ (eLpNormEssSup v (μ.restrict U)).toReal := by
    filter_upwards [enorm_ae_le_eLpNormEssSup v (μ.restrict U)] with x hx
    simpa [Real.norm_eq_abs] using ENNReal.toReal_mono hfin.ne hx
  have heq : EqOn (fun x => min (|v x|) (eLpNormEssSup v (μ.restrict U)).toReal)
      (fun x => |v x|) U :=
    Measure.eqOn_open_of_ae_eq (ha.mono fun _ h => min_eq_left h) hU
      (hv.abs.inf continuousOn_const) hv.abs
  apply le_antisymm
  · exact (supResiduo_le U v _ ENNReal.toReal_nonneg fun x hx =>
      (heq hx).symm.trans_le (min_le_right _ _)).2
  · have ha' : ∀ᵐ x ∂μ.restrict U, ‖v x‖ ≤ supResiduo U v :=
      (ae_restrict_mem hU.measurableSet).mono fun x hx => by
        simpa [Real.norm_eq_abs] using abs_le_supResiduo hx ⟨M, hM⟩
    simpa [ENNReal.toReal_ofReal (supResiduo_nonneg_de_acotada ⟨M, hM⟩)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound ha')

end Supremo

section Estabilidad

variable {d : ℕ} (L : OperadorEliptico d) {U : Set (EspacioEliptico d)} {lam B : ℝ}

/-- Comparación de ambos signos con cualquier barrera no negativa y normalizada. -/
theorem estabilidad_de_barrera (hd : 0 < d) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty) (hL : L.Datos U lam B)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (ψ : EspacioEliptico d → ℝ) (hψd : ContDiff ℝ 2 ψ)
    (hψ : ∀ x ∈ closure U, 0 ≤ ψ x ∧ ψ x ≤ C₀)
    (hψL : ∀ x ∈ U, L.aplica ψ x ≤ -1)
    (v : EspacioEliptico d → ℝ) (hv : ContDiffOn ℝ 2 v U) (hvc : ContinuousOn v (closure U))
    (hb : ∃ M : ℝ, ∀ x ∈ U, |L.aplica v x| ≤ M) :
    supResiduo (closure U) v ≤ supResiduo (frontier U) v + C₀ * supResiduo U (L.aplica v) := by
  let M := supResiduo (frontier U) v
  let F := supResiduo U (L.aplica v)
  obtain ⟨M', hM'⟩ := (hUb.isCompact_closure.of_isClosed_subset isClosed_frontier
    frontier_subset_closure).exists_bound_of_continuousOn (hvc.mono frontier_subset_closure)
  have hbM : ∃ M' : ℝ, ∀ x ∈ frontier U, |v x| ≤ M' :=
    ⟨M', fun x hx => by simpa [Real.norm_eq_abs] using hM' x hx⟩
  have hM := supResiduo_nonneg_de_acotada hbM
  have hF := supResiduo_nonneg_de_acotada hb
  have hside (u : EspacioEliptico d → ℝ) (hu : ContDiffOn ℝ 2 u U)
      (huc : ContinuousOn u (closure U)) (huM : ∀ x ∈ frontier U, u x ≤ M)
      (huF : ∀ x ∈ U, -F ≤ L.aplica u x) :
      ∀ x ∈ closure U, u x ≤ M + C₀ * F := by
    let w := fun x => (u x - M) - F * ψ x
    have hw : ContDiffOn ℝ 2 w U :=
      (hu.sub contDiffOn_const).sub (contDiffOn_const.mul hψd.contDiffOn)
    have hwc : ContinuousOn w (closure U) :=
      (huc.sub continuousOn_const).sub (continuousOn_const.mul hψd.continuous.continuousOn)
    have hsub (x : EspacioEliptico d) (hx : x ∈ U) : 0 ≤ L.aplica w x := by
      have hu' := hu.contDiffAt (hU.mem_nhds hx)
      change 0 ≤ L.aplica (fun y => (u y - M) - F * ψ y) x
      rw [L.aplica_resta (hu'.sub contDiffAt_const) (contDiffAt_const.mul hψd.contDiffAt),
        L.aplica_resta hu' contDiffAt_const, L.aplica_const,
        L.aplica_mul_const hψd.contDiffAt]
      linarith only [huF x hx, mul_nonpos_of_nonpos_of_nonneg (hL.signo x hx) hM,
        mul_le_mul_of_nonneg_left (hψL x hx) hF]
    have hbd (x : EspacioEliptico d) (hx : x ∈ frontier U) : w x ≤ 0 := by
      exact sub_nonpos.mpr ((sub_nonpos.mpr (huM x hx)).trans
        (mul_nonneg hF (hψ x (frontier_subset_closure hx)).1))
    intro x hx
    have hmax := L.maximo_debil hd hU hUb hUne hL hw hwc hsub hbd x hx
    change u x - M - F * ψ x ≤ 0 at hmax
    linarith only [hmax, mul_le_mul_of_nonneg_left (hψ x hx).2 hF]
  have hpos := hside v hv hvc
    (fun x hx => (le_abs_self _).trans (abs_le_supResiduo hx hbM))
    (fun x hx => (abs_le.mp (abs_le_supResiduo hx hb)).1)
  have hneg := hside (fun x => -v x) hv.neg hvc.neg
    (fun x hx => (neg_le_abs _).trans (abs_le_supResiduo hx hbM))
    (fun x hx => by
      rw [L.aplica_neg (hv.contDiffAt (hU.mem_nhds hx))]
      exact neg_le_neg ((abs_le.mp (abs_le_supResiduo hx hb)).2))
  refine (supResiduo_le _ _ _ (add_nonneg hM (mul_nonneg hC₀ hF)) fun x hx => ?_).2
  exact abs_le.mpr ⟨by linarith only [hneg x hx], hpos x hx⟩

/-- (3.67) en forma puntual. La constante se elige antes de la función. -/
theorem lema317_estabilidad_uniforme (hd : 0 < d) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty) (hL : L.Datos U lam B) :
    ∃ C₀ > 0, ∀ v : EspacioEliptico d → ℝ, ContDiffOn ℝ 2 v U →
      ContinuousOn v (closure U) →
      (∃ M : ℝ, ∀ x ∈ U, |L.aplica v x| ≤ M) →
      supResiduo (closure U) v ≤ supResiduo (frontier U) v + C₀ * supResiduo U (L.aplica v) := by
  obtain ⟨C₀, hC₀, ψ, hψd, hψ, hψL⟩ := barrera317 L hd hUb hL
  exact ⟨C₀, hC₀, estabilidad_de_barrera L hd hU hUb hUne hL C₀ hC₀.le ψ hψd hψ hψL⟩

theorem lema317_estabilidad_Linfty (hd : 0 < d) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty) (hL : L.Datos U lam B)
    (hLc : L.ContinuoEn U) :
    ∃ C₀ > 0, ∀ v : EspacioEliptico d → ℝ, ContDiffOn ℝ 2 v U →
      ContinuousOn v (closure U) →
      (∃ M : ℝ, ∀ x ∈ U, |L.aplica v x| ≤ M) →
      supResiduo (closure U) v ≤ supResiduo (frontier U) v +
        C₀ * (eLpNormEssSup (L.aplica v) (volume.restrict U)).toReal := by
  obtain ⟨C₀, hC, hc⟩ := lema317_estabilidad_uniforme L hd hU hUb hUne hL
  exact ⟨C₀, hC, fun v hv hvc hb =>
    (supResiduo_eq_Linfty volume hU (L.aplica_continuo hU hLc hv) hb) ▸ hc v hv hvc hb⟩

end Estabilidad

#check lema317_estabilidad_uniforme
#check lema317_estabilidad_Linfty
#print axioms OperadorEliptico.maximo_debil
#print axioms OperadorDivergencia.aplica_eq_noDivergente
#print axioms OperadorDivergencia.cotas_noDivergente
#print axioms derivada_barreraExponencial
#print axioms segunda_derivada_barreraExponencial
#print axioms barrera317
#print axioms estabilidad_de_barrera
#print axioms lema317_estabilidad_uniforme
#print axioms lema317_estabilidad_Linfty

end TesisPINN
