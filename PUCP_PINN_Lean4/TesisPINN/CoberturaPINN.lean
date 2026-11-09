import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import TesisPINN.VariacionalPINN

/-!
# Paso puntual del lema determinista de cobertura

Se formaliza la estimación de un residuo entre un punto y una muestra próxima.
La integración sobre celdas de Voronoi y la cota completa (3.13) requieren
construir la partición medible y sus masas; se registran como trabajo pendiente.
-/

namespace TesisPINN

noncomputable section

theorem cuadrado_suma_tres_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

/-- Consecuencia puntual de la cobertura y las cotas Hölder de `L[h]` y `f`.
Es el paso (3.14) aplicado al residuo antes de integrar sobre las celdas. -/
theorem residuo_puntual_de_cobertura
    {X : Type*} [PseudoMetricSpace X]
    (U : Set X) (L f : X → ℝ) (m : ℕ) (s : Fin m → X)
    (alpha epsilon CL Cf : ℝ)
    (halpha : 0 < alpha) (heps : 0 ≤ epsilon)
    (hCL : 0 ≤ CL) (hCf : 0 ≤ Cf)
    (hs : ∀ i, s i ∈ U)
    (hCover : ∀ x ∈ U, ∃ i, dist x (s i) ≤ epsilon)
    (hL : ∀ x ∈ U, ∀ y ∈ U,
      |L x - L y| ≤ CL * dist x y ^ alpha)
    (hf : ∀ x ∈ U, ∀ y ∈ U,
      |f x - f y| ≤ Cf * dist x y ^ alpha)
    (x : X) (hx : x ∈ U) :
    ∃ i : Fin m,
      (L x - f x) ^ 2 ≤
        3 * ((L (s i) - f (s i)) ^ 2 +
          (CL * epsilon ^ alpha) ^ 2 +
          (Cf * epsilon ^ alpha) ^ 2) := by
  obtain ⟨i, hdist⟩ := hCover x hx
  refine ⟨i, ?_⟩
  have hpow : dist x (s i) ^ alpha ≤ epsilon ^ alpha :=
    Real.rpow_le_rpow (dist_nonneg) hdist halpha.le
  have hA : |L x - L (s i)| ≤ CL * epsilon ^ alpha :=
    (hL x hx (s i) (hs i)).trans (mul_le_mul_of_nonneg_left hpow hCL)
  have hC : |f (s i) - f x| ≤ Cf * epsilon ^ alpha := by
    rw [abs_sub_comm]
    exact (hf x hx (s i) (hs i)).trans
      (mul_le_mul_of_nonneg_left hpow hCf)
  have hAn : 0 ≤ CL * epsilon ^ alpha :=
    mul_nonneg hCL (Real.rpow_nonneg heps _)
  have hCn : 0 ≤ Cf * epsilon ^ alpha :=
    mul_nonneg hCf (Real.rpow_nonneg heps _)
  have hAsq : (L x - L (s i)) ^ 2 ≤ (CL * epsilon ^ alpha) ^ 2 := by
    calc
      (L x - L (s i)) ^ 2 = |L x - L (s i)| ^ 2 := by simp
      _ ≤ (CL * epsilon ^ alpha) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hAn).2 hA
  have hCsq : (f (s i) - f x) ^ 2 ≤ (Cf * epsilon ^ alpha) ^ 2 := by
    calc
      (f (s i) - f x) ^ 2 = |f (s i) - f x| ^ 2 := by simp
      _ ≤ (Cf * epsilon ^ alpha) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hCn).2 hC
  have hThree := cuadrado_suma_tres_le
    (L x - L (s i)) (L (s i) - f (s i)) (f (s i) - f x)
  nlinarith

/-- Evento geométrico de cobertura por los puntos muestreados. -/
def MuestrasCubren {X : Type*} [PseudoMetricSpace X]
    (U : Set X) {m : ℕ} (s : Fin m → X) (epsilon : ℝ) : Prop :=
  ∀ x ∈ U, ∃ i, dist x (s i) ≤ epsilon

/-- Cota de masa de bolas cerradas de (3.4), con exponente `s=2` en el
interior del cuadrado y `s=1` en su frontera. -/
def MasaBolaSuperior {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (U : Set X)
    (epsilon0 C s : ℝ) : Prop :=
  ∀ x ∈ U, ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon0 →
    μ (Metric.closedBall x epsilon ∩ U) ≤
      ENNReal.ofReal (C * epsilon ^ s)

/-- Las constantes que figuran como seminormas en el funcional realmente
controlan los incrementos Hölder de operadores y datos. -/
def CotasHolder
    {H X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    {mr mb : ℕ} (P : ProblemaPINN H X Y mr mb)
    (Hm : Set H) (U : Set X) (Gamma : Set Y)
    (alpha Sf Sg : ℝ) : Prop :=
  0 ≤ Sf ∧ 0 ≤ Sg ∧
  (∀ h ∈ Hm, 0 ≤ P.seminormaL h ∧ 0 ≤ P.seminormaB h ∧
    (∀ x ∈ U, ∀ y ∈ U,
      |P.L h x - P.L h y| ≤ P.seminormaL h * dist x y ^ alpha) ∧
    (∀ x ∈ Gamma, ∀ y ∈ Gamma,
      |P.B h x - P.B h y| ≤ P.seminormaB h * dist x y ^ alpha)) ∧
  (∀ x ∈ U, ∀ y ∈ U, |P.f x - P.f y| ≤ Sf * dist x y ^ alpha) ∧
  (∀ x ∈ Gamma, ∀ y ∈ Gamma,
    |P.g x - P.g y| ≤ Sg * dist x y ^ alpha)

/-- Factor `C_m` de (3.13) para `d=2`. -/
def factorCoberturaCuadrado (mr mb : ℕ)
    (Cr Cb epsilonR epsilonB : ℝ) : ℝ :=
  3 * max (Cr * mr * epsilonR ^ 2) (Cb * mb * epsilonB)

/-- El peso `hatλ_Rr,m` de (3.7): al multiplicarlo por `C_m`, queda
`3 λr εr^(2α)`; análogamente para frontera. -/
def pesoCobertura (lambda epsilon alpha Cm : ℝ) : ℝ :=
  3 * lambda * epsilon ^ (2 * alpha) / Cm

/-- Elección de pesos iguales `a_m` de (3.23). -/
def pesoRegularizacionIgual (lambdaR lambdaB epsilonR epsilonB alpha Cm : ℝ) : ℝ :=
  max (pesoCobertura lambdaR epsilonR alpha Cm)
    (pesoCobertura lambdaB epsilonB alpha Cm)

theorem pesoInterior_le_igual (lambdaR lambdaB epsilonR epsilonB alpha Cm : ℝ) :
    pesoCobertura lambdaR epsilonR alpha Cm ≤
      pesoRegularizacionIgual lambdaR lambdaB epsilonR epsilonB alpha Cm :=
  le_max_left _ _

theorem pesoFrontera_le_igual (lambdaR lambdaB epsilonR epsilonB alpha Cm : ℝ) :
    pesoCobertura lambdaB epsilonB alpha Cm ≤
      pesoRegularizacionIgual lambdaR lambdaB epsilonR epsilonB alpha Cm :=
  le_max_right _ _

/-- Enunciado objetivo de (3.13), todavía **no demostrado**. `Sf` y
`Sg` representan las seminormas Hölder de los datos.
La prueba requiere una partición de Voronoi medible y control de sus masas. -/
def ObjetivoCoberturaIntegral
    {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mr mb : ℕ} (P : ProblemaPINN H X Y mr mb)
    (epsilonR epsilonB alpha Cr Cb Sf Sg : ℝ)
    (h : H) : Prop :=
  let Cm := factorCoberturaCuadrado mr mb Cr Cb epsilonR epsilonB
  P.perdidaPoblacional h ≤
    Cm * (P.perdidaEmpirica h +
      pesoCobertura P.lambdaR epsilonR alpha Cm * P.regularidadInterior h +
      pesoCobertura P.lambdaB epsilonB alpha Cm * P.regularidadFrontera h) +
    3 * P.lambdaR * epsilonR ^ (2 * alpha) * Sf ^ 2 +
    3 * P.lambdaB * epsilonB ^ (2 * alpha) * Sg ^ 2

#print axioms TesisPINN.cuadrado_suma_tres_le
#print axioms TesisPINN.residuo_puntual_de_cobertura
#print axioms TesisPINN.pesoInterior_le_igual
#print axioms TesisPINN.pesoFrontera_le_igual

end

end TesisPINN

