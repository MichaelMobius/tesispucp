import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Sequences

/-!
# Lema 3.1 (afín a Shin–Darbon–Karniadakis, Lemma 2.1): regularidad y precompacidad de redes

El archivo tiene dos partes.

**Parte abstracta.** Sea `G : Θ × E → F` conjuntamente de clase `C^k` en el
parámetro y en la variable espacial, `K ⊆ Θ` compacto y `A ⊆ E` compacto (en la
tesis, `A = closure U` con `U` acotado). Entonces:

* `continuous_iteratedFDeriv_parcial`: las derivadas iteradas en `x` de orden
  `i ≤ k` dependen continuamente de `(θ, x)`;
* `cotas_uniformes_derivadas`: están acotadas uniformemente en `K × A`;
* `equicontinuidad_uniforme_derivadas`: son uniformemente equicontinuas en `A`,
  con módulo independiente de `θ ∈ K`;
* `precompacidad_derivadas`: toda sucesión de parámetros en `K` admite una
  subsucesión convergente a `θ∞ ∈ K` cuyas derivadas de orden `≤ k` convergen
  uniformemente en `A` a las de `G (θ∞, ·)`.

**Parte concreta.** `red σ n p θ` es la red totalmente conectada de arquitectura
`(n 0, …, n p, 1)`: `p` capas ocultas con activación `σ` componente a
componente y una capa de salida afín escalar, como en la demostración del
Lema 3.1 (en la notación de la tesis, `L = p + 1` y `n_L = 1`). Los teoremas
`lema31_*` son los apartados (i) y (ii) del lema.

## Diferencias respecto del enunciado de la tesis

* Solo se usa `σ ∈ C^k`. No intervienen ni `k' > k` ni la acotación y la
  condición de Lipschitz de `σ^{(s)}`: la prueba no pasa por la fórmula de Faà
  di Bruno capa a capa, sino por la suavidad conjunta de `(θ, x) ↦ h_θ(x)` y la
  compacidad de `K_M × closure U`. Es el argumento que el propio enunciado
  invoca para el apartado (ii).
* La constante `C` existe pero no es explícita.
* Las derivadas se miden con `iteratedFDeriv` (la derivada de Fréchet de orden
  `i`, una aplicación `i`-lineal). Las derivadas parciales `D^β h` con
  `|β| = i` son sus valores en vectores de la base canónica, de norma uno;
  `lema31_cotas_direccionales` da esa forma.
* Los pesos de cada capa son aplicaciones lineales continuas
  `(Fin a → ℝ) →L[ℝ] (Fin b → ℝ)`, es decir, matrices `b × a`. El conjunto de
  parámetros admisibles es un compacto arbitrario `K`; `lema31_cotas_bola` lo
  especializa a una bola cerrada. Como el espacio de parámetros tiene dimensión
  finita, todo conjunto cerrado y acotado para cualquier norma (en particular
  `‖θ‖₂ ≤ M`) es compacto: `parametros_compacto_de_cerrado_acotado`.
* Se obtiene equicontinuidad y convergencia para todos los órdenes `i ≤ k`,
  no solo `i ≤ k - 1`.
-/

noncomputable section

namespace TesisPINN

open Filter Topology Set

/-! ## Parte abstracta: familias conjuntamente `C^k` sobre parámetros compactos -/

section Abstracto

variable {Θ E F : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- La derivada iterada en `x` de `G (θ, ·)` es la derivada iterada conjunta de
`G` restringida a las direcciones espaciales. -/
theorem iteratedFDeriv_parcial {k : ℕ} (G : Θ × E → F) (hG : ContDiff ℝ k G)
    (i : ℕ) (hi : i ≤ k) (θ : Θ) (x : E) :
    iteratedFDeriv ℝ i (fun y => G (θ, y)) x =
      (iteratedFDeriv ℝ i G (θ, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ Θ E) := by
  have hshift : ContDiff ℝ k (fun z : Θ × E => G ((θ, 0) + z)) :=
    hG.comp (contDiff_const.add contDiff_id)
  have hcomp : (fun y => G (θ, y)) =
      (fun z : Θ × E => G ((θ, 0) + z)) ∘ (ContinuousLinearMap.inr ℝ Θ E) := by
    funext y
    simp
  have hi' : (i : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hi
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hshift x hi',
    iteratedFDeriv_comp_add_left]
  simp

/-- Continuidad conjunta en `(θ, x)` de las derivadas iteradas en `x`. -/
theorem continuous_iteratedFDeriv_parcial {k : ℕ} (G : Θ × E → F)
    (hG : ContDiff ℝ k G) (i : ℕ) (hi : i ≤ k) :
    Continuous (fun q : Θ × E => iteratedFDeriv ℝ i (fun y => G (q.1, y)) q.2) := by
  have hi' : (i : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hi
  have hcont : Continuous (fun q : Θ × E =>
      ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin i => ContinuousLinearMap.inr ℝ Θ E) (iteratedFDeriv ℝ i G q)) :=
    (ContinuousLinearMap.continuous _).comp (hG.continuous_iteratedFDeriv hi')
  have heq : (fun q : Θ × E => iteratedFDeriv ℝ i (fun y => G (q.1, y)) q.2) =
      (fun q : Θ × E =>
        ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin i => ContinuousLinearMap.inr ℝ Θ E) (iteratedFDeriv ℝ i G q)) := by
    funext q
    rw [iteratedFDeriv_parcial G hG i hi q.1 q.2]
    rfl
  rw [heq]
  exact hcont

/-- **Cotas uniformes.** Las derivadas en `x` de orden `i ≤ k` están acotadas
por una misma constante para todos los parámetros de un compacto y todos los
puntos de un compacto. -/
theorem cotas_uniformes_derivadas {k : ℕ} (G : Θ × E → F) (hG : ContDiff ℝ k G)
    (K : Set Θ) (hK : IsCompact K) (A : Set E) (hA : IsCompact A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ K, ∀ x ∈ A, ∀ i ≤ k,
      ‖iteratedFDeriv ℝ i (fun y => G (θ, y)) x‖ ≤ C := by
  have hKA : IsCompact (K ×ˢ A) := hK.prod hA
  have hex : ∀ i : ℕ, ∃ C : ℝ, i ≤ k → ∀ q ∈ K ×ˢ A,
      ‖iteratedFDeriv ℝ i (fun y => G (q.1, y)) q.2‖ ≤ C := by
    intro i
    by_cases hi : i ≤ k
    · obtain ⟨C, hC⟩ := hKA.exists_bound_of_continuousOn
        (continuous_iteratedFDeriv_parcial G hG i hi).continuousOn
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose C hC using hex
  refine ⟨∑ i ∈ Finset.range (k + 1), |C i|,
    Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  intro θ hθ x hx i hi
  have h1 := hC i hi (θ, x) ⟨hθ, hx⟩
  have h2 : |C i| ≤ ∑ j ∈ Finset.range (k + 1), |C j| :=
    Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  exact h1.trans ((le_abs_self _).trans h2)

/-- **Equicontinuidad uniforme.** Las derivadas en `x` de orden `i ≤ k` son
uniformemente continuas en el compacto `A`, con un módulo de continuidad común
a todos los parámetros de `K`. -/
theorem equicontinuidad_uniforme_derivadas {k : ℕ} (G : Θ × E → F)
    (hG : ContDiff ℝ k G) (K : Set Θ) (hK : IsCompact K) (A : Set E)
    (hA : IsCompact A) (i : ℕ) (hi : i ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ ∈ K, ∀ x ∈ A, ∀ y ∈ A, dist x y < δ →
      dist (iteratedFDeriv ℝ i (fun z => G (θ, z)) x)
        (iteratedFDeriv ℝ i (fun z => G (θ, z)) y) < ε := by
  have hu := (hK.prod hA).uniformContinuousOn_of_continuous
    (continuous_iteratedFDeriv_parcial G hG i hi).continuousOn
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ, hδ, fun θ hθ x hx y hy hxy => ?_⟩
  have hd : dist ((θ, x) : Θ × E) (θ, y) < δ := by
    rw [Prod.dist_eq]
    simpa using hxy
  exact h (θ, x) ⟨hθ, hx⟩ (θ, y) ⟨hθ, hy⟩ hd

/-- **Precompacidad.** Toda sucesión de parámetros en el compacto `K` tiene
una subsucesión que converge a un parámetro `θ∞ ∈ K` y tal que, para cada orden
`i ≤ k`, las derivadas en `x` convergen uniformemente en `A` a las de
`G (θ∞, ·)`. El límite pertenece, por tanto, a la misma familia. -/
theorem precompacidad_derivadas {k : ℕ} (G : Θ × E → F) (hG : ContDiff ℝ k G)
    (K : Set Θ) (hK : IsCompact K) (A : Set E) (hA : IsCompact A)
    (θ : ℕ → Θ) (hθ : ∀ j, θ j ∈ K) :
    ∃ θinf ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => θ (φ j)) atTop (𝓝 θinf) ∧
      ∀ i ≤ k, TendstoUniformlyOn
        (fun j x => iteratedFDeriv ℝ i (fun y => G (θ (φ j), y)) x)
        (fun x => iteratedFDeriv ℝ i (fun y => G (θinf, y)) x) atTop A := by
  obtain ⟨θinf, hθinf, φ, hφ, hlim⟩ := hK.tendsto_subseq hθ
  refine ⟨θinf, hθinf, φ, hφ, hlim, fun i hi => ?_⟩
  have hu := (hK.prod hA).uniformContinuousOn_of_continuous
    (continuous_iteratedFDeriv_parcial G hG i hi).continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  have hev : ∀ᶠ j in atTop, dist (θ (φ j)) θinf < δ :=
    (Metric.tendsto_nhds.mp hlim) δ hδ
  filter_upwards [hev] with j hj x hx
  have hd : dist ((θinf, x) : Θ × E) (θ (φ j), x) < δ := by
    rw [Prod.dist_eq]
    simpa [dist_comm] using hj
  exact h (θinf, x) ⟨hθinf, hx⟩ (θ (φ j), x) ⟨hθ (φ j), hx⟩ hd

end Abstracto

/-! ## Parte concreta: redes totalmente conectadas con activación `σ` -/

/-- Parámetros de una capa afín de `ℝ^a` en `ℝ^b`: la matriz de pesos, como
aplicación lineal continua, y el vector de sesgos. -/
abbrev Capa (a b : ℕ) : Type :=
  ((Fin a → ℝ) →L[ℝ] (Fin b → ℝ)) × (Fin b → ℝ)

/-- Parámetros de las `p` capas ocultas de la arquitectura `(n 0, …, n p)`. -/
abbrev ParametrosOcultos (n : ℕ → ℕ) (p : ℕ) : Type :=
  ∀ j : Fin p, Capa (n j.val) (n (j.val + 1))

/-- Parámetros `θ` de una red de arquitectura `(n 0, …, n p, 1)`: las capas
ocultas y la capa de salida afín escalar. -/
abbrev Parametros (n : ℕ → ℕ) (p : ℕ) : Type :=
  ParametrosOcultos n p × (((Fin (n p) → ℝ) →L[ℝ] ℝ) × ℝ)

/-- Estado `z_ℓ(x)` de la capa oculta `ℓ ≤ p`: `z_0 = x` y
`z_{ℓ+1} = σ(W_{ℓ+1} z_ℓ + b_{ℓ+1})`, con `σ` aplicada componente a
componente. -/
def estadoOculto (σ : ℝ → ℝ) (n : ℕ → ℕ) (p : ℕ) (θ : ParametrosOcultos n p) :
    (ℓ : ℕ) → ℓ ≤ p → (Fin (n 0) → ℝ) → (Fin (n ℓ) → ℝ)
  | 0, _, x => x
  | ℓ + 1, h, x => fun r =>
      σ (((θ ⟨ℓ, h⟩).1 (estadoOculto σ n p θ ℓ (Nat.le_of_succ_le h) x) +
        (θ ⟨ℓ, h⟩).2) r)

/-- La red `h_θ(x) = W_out z_p(x) + b_out`, con última capa afín. -/
def red (σ : ℝ → ℝ) (n : ℕ → ℕ) (p : ℕ) (θ : Parametros n p)
    (x : Fin (n 0) → ℝ) : ℝ :=
  θ.2.1 (estadoOculto σ n p θ.1 p le_rfl x) + θ.2.2

/-- Comprobación de la definición: sin capas ocultas la red es afín. -/
theorem red_sin_capas (σ : ℝ → ℝ) (n : ℕ → ℕ) (θ : Parametros n 0)
    (x : Fin (n 0) → ℝ) :
    red σ n 0 θ x = θ.2.1 x + θ.2.2 :=
  rfl

/-- Comprobación de la definición: con una capa oculta la red es
`x ↦ W_out σ(W₁ x + b₁) + b_out`, con `σ` componente a componente. -/
theorem red_una_capa (σ : ℝ → ℝ) (n : ℕ → ℕ) (θ : Parametros n 1)
    (x : Fin (n 0) → ℝ) :
    red σ n 1 θ x =
      θ.2.1 (fun r => σ (((θ.1 ⟨0, Nat.one_pos⟩).1 x + (θ.1 ⟨0, Nat.one_pos⟩).2) r)) +
        θ.2.2 :=
  rfl

/-- Suavidad conjunta en `(θ, x)` del estado de cada capa oculta. -/
theorem contDiff_estadoOculto {k : ℕ} {σ : ℝ → ℝ} (hσ : ContDiff ℝ k σ)
    (n : ℕ → ℕ) (p : ℕ) (ℓ : ℕ) (h : ℓ ≤ p) :
    ContDiff ℝ k (fun q : ParametrosOcultos n p × (Fin (n 0) → ℝ) =>
      estadoOculto σ n p q.1 ℓ h q.2) := by
  induction ℓ with
  | zero => exact contDiff_snd
  | succ ℓ ih =>
    have hcapa : ContDiff ℝ k
        (fun q : ParametrosOcultos n p × (Fin (n 0) → ℝ) => q.1 ⟨ℓ, h⟩) :=
      (contDiff_pi (Φ := fun q : ParametrosOcultos n p × (Fin (n 0) → ℝ) => q.1)).1
        contDiff_fst (⟨ℓ, h⟩ : Fin p)
    have hafin : ContDiff ℝ k
        (fun q : ParametrosOcultos n p × (Fin (n 0) → ℝ) =>
          (q.1 ⟨ℓ, h⟩).1 (estadoOculto σ n p q.1 ℓ (Nat.le_of_succ_le h) q.2) +
            (q.1 ⟨ℓ, h⟩).2) :=
      (hcapa.fst.clm_apply (ih (Nat.le_of_succ_le h))).add hcapa.snd
    exact contDiff_pi.2 fun r => hσ.comp (contDiff_pi.1 hafin r)

/-- Suavidad conjunta de la aplicación parámetro–función `(θ, x) ↦ h_θ(x)`. -/
theorem contDiff_red_conjunta {k : ℕ} {σ : ℝ → ℝ} (hσ : ContDiff ℝ k σ)
    (n : ℕ → ℕ) (p : ℕ) :
    ContDiff ℝ k (fun q : Parametros n p × (Fin (n 0) → ℝ) =>
      red σ n p q.1 q.2) := by
  have hz : ContDiff ℝ k (fun q : Parametros n p × (Fin (n 0) → ℝ) =>
      estadoOculto σ n p q.1.1 p le_rfl q.2) :=
    (contDiff_estadoOculto hσ n p p le_rfl).comp
      ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hsal : ContDiff ℝ k
      (fun q : Parametros n p × (Fin (n 0) → ℝ) => q.1.2) :=
    contDiff_snd.comp contDiff_fst
  exact (hsal.fst.clm_apply hz).add hsal.snd

/-- **Lema 3.1 (i), regularidad.** Si `σ ∈ C^k`, toda red `h_θ` pertenece a
`C^k(ℝ^{n_0})`. -/
theorem lema31_regularidad {k : ℕ} {σ : ℝ → ℝ} (hσ : ContDiff ℝ k σ)
    (n : ℕ → ℕ) (p : ℕ) (θ : Parametros n p) :
    ContDiff ℝ k (red σ n p θ) :=
  (contDiff_red_conjunta hσ n p).comp (contDiff_const.prodMk contDiff_id)

/-- **Lema 3.1 (i), cotas uniformes.** Para parámetros en un compacto `K` y
`U` acotado, existe una constante `C = C(n, p, k, K, σ, U)` que acota en
`closure U` todas las derivadas de orden `i ≤ k` de todas las redes. -/
theorem lema31_cotas {k : ℕ} {σ : ℝ → ℝ} (hσ : ContDiff ℝ k σ)
    (n : ℕ → ℕ) (p : ℕ) (K : Set (Parametros n p)) (hK : IsCompact K)
    (U : Set (Fin (n 0) → ℝ)) (hU : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ K, ∀ x ∈ closure U, ∀ i ≤ k,
      ‖iteratedFDeriv ℝ i (red σ n p θ) x‖ ≤ C :=
  cotas_uniformes_derivadas
    (fun q : Parametros n p × (Fin (n 0) → ℝ) => red σ n p q.1 q.2)
    (contDiff_red_conjunta hσ n p) K hK (closure U) hU.isCompact_closure

/-- Forma direccional de las cotas: cualquier derivada de orden `i ≤ k` en
direcciones de norma a lo sumo uno, en particular cualquier derivada parcial
`D^β h_θ` con `|β| = i`, queda acotada por la misma constante. -/
theorem lema31_cotas_direccionales {k : ℕ} {σ : ℝ → ℝ} (hσ : ContDiff ℝ k σ)
    (n : ℕ → ℕ) (p : ℕ) (K : Set (Parametros n p)) (hK : IsCompact K)
    (U : Set (Fin (n 0) → ℝ)) (hU : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ K, ∀ x ∈ closure U, ∀ i ≤ k,
      ∀ v : Fin i → (Fin (n 0) → ℝ), (∀ j, ‖v j‖ ≤ 1) →
        |iteratedFDeriv ℝ i (red σ n p θ) x v| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := lema31_cotas hσ n p K hK U hU
  refine ⟨C, hC0, fun θ hθ x hx i hi v hv => ?_⟩
  have hprod : ∏ j, ‖v j‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => norm_nonneg _) (fun j _ => hv j)
  calc
    |iteratedFDeriv ℝ i (red σ n p θ) x v|
        = ‖iteratedFDeriv ℝ i (red σ n p θ) x v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖iteratedFDeriv ℝ i (red σ n p θ) x‖ * ∏ j, ‖v j‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ ‖iteratedFDeriv ℝ i (red σ n p θ) x‖ * 1 :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ C := by
      rw [mul_one]
      exact hC θ hθ x hx i hi

/-- En el espacio de parámetros, de dimensión finita, todo conjunto cerrado y
acotado es compacto. Cubre la condición `‖θ‖₂ ≤ M` de la tesis, cualquiera
que sea la norma empleada. -/
theorem parametros_compacto_de_cerrado_acotado (n : ℕ → ℕ) (p : ℕ)
    (K : Set (Parametros n p)) (hc : IsClosed K) (hb : Bornology.IsBounded K) :
    IsCompact K :=
  Metric.isCompact_of_isClosed_isBounded hc hb

/-- **Lema 3.1 (i) para la bola `‖θ‖ ≤ M`.** -/
theorem lema31_cotas_bola {k : ℕ} {σ : ℝ → ℝ} (hσ : ContDiff ℝ k σ)
    (n : ℕ → ℕ) (p : ℕ) (M : ℝ)
    (U : Set (Fin (n 0) → ℝ)) (hU : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : Parametros n p, ‖θ‖ ≤ M → ∀ x ∈ closure U, ∀ i ≤ k,
      ‖iteratedFDeriv ℝ i (red σ n p θ) x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := lema31_cotas hσ n p (Metric.closedBall 0 M)
    (isCompact_closedBall 0 M) U hU
  exact ⟨C, hC0, fun θ hθ => hC θ (mem_closedBall_zero_iff.mpr hθ)⟩

/-- **Lema 3.1 (ii), equicontinuidad.** Para cada orden `i ≤ k`, la familia
`{D^i h_θ : θ ∈ K}` es uniformemente equicontinua en `closure U`. El caso
`i = 0` es la equicontinuidad de las propias redes. -/
theorem lema31_equicontinuidad {k : ℕ} {σ : ℝ → ℝ} (hσ : ContDiff ℝ k σ)
    (n : ℕ → ℕ) (p : ℕ) (K : Set (Parametros n p)) (hK : IsCompact K)
    (U : Set (Fin (n 0) → ℝ)) (hU : Bornology.IsBounded U)
    (i : ℕ) (hi : i ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ ∈ K, ∀ x ∈ closure U, ∀ y ∈ closure U, dist x y < δ →
      dist (iteratedFDeriv ℝ i (red σ n p θ) x)
        (iteratedFDeriv ℝ i (red σ n p θ) y) < ε :=
  equicontinuidad_uniforme_derivadas
    (fun q : Parametros n p × (Fin (n 0) → ℝ) => red σ n p q.1 q.2)
    (contDiff_red_conjunta hσ n p) K hK (closure U) hU.isCompact_closure i hi ε hε

/-- Equicontinuidad de los valores de las redes, sin pasar por `iteratedFDeriv`. -/
theorem lema31_equicontinuidad_valores {k : ℕ} {σ : ℝ → ℝ} (hσ : ContDiff ℝ k σ)
    (n : ℕ → ℕ) (p : ℕ) (K : Set (Parametros n p)) (hK : IsCompact K)
    (U : Set (Fin (n 0) → ℝ)) (hU : Bornology.IsBounded U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ ∈ K, ∀ x ∈ closure U, ∀ y ∈ closure U, dist x y < δ →
      |red σ n p θ x - red σ n p θ y| < ε := by
  have hu := (hK.prod hU.isCompact_closure).uniformContinuousOn_of_continuous
    (contDiff_red_conjunta hσ n p).continuous.continuousOn
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ, hδ, fun θ hθ x hx y hy hxy => ?_⟩
  have hd : dist ((θ, x) : Parametros n p × (Fin (n 0) → ℝ)) (θ, y) < δ := by
    rw [Prod.dist_eq]
    simpa using hxy
  have := h (θ, x) ⟨hθ, hx⟩ (θ, y) ⟨hθ, hy⟩ hd
  rwa [Real.dist_eq] at this

/-- **Lema 3.1 (ii), precompacidad en `C^k(closure U)`.** Toda sucesión de
redes con parámetros en el compacto `K` admite una subsucesión cuyas derivadas
de todos los órdenes `i ≤ k` convergen uniformemente en `closure U`. El límite
es una red de la misma arquitectura con parámetro `θ∞ ∈ K`. -/
theorem lema31_precompacidad {k : ℕ} {σ : ℝ → ℝ} (hσ : ContDiff ℝ k σ)
    (n : ℕ → ℕ) (p : ℕ) (K : Set (Parametros n p)) (hK : IsCompact K)
    (U : Set (Fin (n 0) → ℝ)) (hU : Bornology.IsBounded U)
    (θ : ℕ → Parametros n p) (hθ : ∀ j, θ j ∈ K) :
    ∃ θinf ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => θ (φ j)) atTop (𝓝 θinf) ∧
      ∀ i ≤ k, TendstoUniformlyOn
        (fun j x => iteratedFDeriv ℝ i (red σ n p (θ (φ j))) x)
        (fun x => iteratedFDeriv ℝ i (red σ n p θinf) x) atTop (closure U) :=
  precompacidad_derivadas
    (fun q : Parametros n p × (Fin (n 0) → ℝ) => red σ n p q.1 q.2)
    (contDiff_red_conjunta hσ n p) K hK (closure U) hU.isCompact_closure θ hθ

/-- Convergencia uniforme de los valores de la subsucesión del apartado (ii),
escrita directamente para las redes. -/
theorem lema31_precompacidad_valores {k : ℕ} {σ : ℝ → ℝ} (hσ : ContDiff ℝ k σ)
    (n : ℕ → ℕ) (p : ℕ) (K : Set (Parametros n p)) (hK : IsCompact K)
    (U : Set (Fin (n 0) → ℝ)) (hU : Bornology.IsBounded U)
    (θ : ℕ → Parametros n p) (hθ : ∀ j, θ j ∈ K) :
    ∃ θinf ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun j x => red σ n p (θ (φ j)) x)
        (fun x => red σ n p θinf x) atTop (closure U) := by
  obtain ⟨θinf, hθinf, φ, hφ, hlim⟩ := hK.tendsto_subseq hθ
  refine ⟨θinf, hθinf, φ, hφ, ?_⟩
  have hu := (hK.prod hU.isCompact_closure).uniformContinuousOn_of_continuous
    (contDiff_red_conjunta hσ n p).continuous.continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  have hev : ∀ᶠ j in atTop, dist (θ (φ j)) θinf < δ :=
    (Metric.tendsto_nhds.mp hlim) δ hδ
  filter_upwards [hev] with j hj x hx
  have hd : dist ((θinf, x) : Parametros n p × (Fin (n 0) → ℝ)) (θ (φ j), x) < δ := by
    rw [Prod.dist_eq]
    simpa [dist_comm] using hj
  exact h (θinf, x) ⟨hθinf, hx⟩ (θ (φ j), x) ⟨hθ (φ j), hx⟩ hd

#print axioms TesisPINN.iteratedFDeriv_parcial
#print axioms TesisPINN.cotas_uniformes_derivadas
#print axioms TesisPINN.equicontinuidad_uniforme_derivadas
#print axioms TesisPINN.precompacidad_derivadas
#print axioms TesisPINN.contDiff_red_conjunta
#print axioms TesisPINN.lema31_regularidad
#print axioms TesisPINN.lema31_cotas
#print axioms TesisPINN.lema31_cotas_direccionales
#print axioms TesisPINN.lema31_cotas_bola
#print axioms TesisPINN.lema31_equicontinuidad
#print axioms TesisPINN.lema31_equicontinuidad_valores
#print axioms TesisPINN.lema31_precompacidad
#print axioms TesisPINN.lema31_precompacidad_valores

end TesisPINN
