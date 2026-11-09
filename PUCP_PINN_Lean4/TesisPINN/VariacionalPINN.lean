import TesisPINN.Minimalidad
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

/-!
# Funcional empírico y principio variacional del Teorema 3.8

`H` es una clase abstracta de candidatos. Los operadores, datos, muestras y
seminormas Hölder son parámetros; no se postula una red concreta ni una
desigualdad de cobertura. Los términos de frontera se conservan separados.
-/

noncomputable section

open MeasureTheory

namespace TesisPINN

structure ProblemaPINN (H X Y : Type*) [MeasurableSpace X]
    [MeasurableSpace Y] (mr mb : ℕ) where
  L : H → X → ℝ
  f : X → ℝ
  B : H → Y → ℝ
  g : Y → ℝ
  xr : Fin mr → X
  xb : Fin mb → Y
  μr : Measure X
  μb : Measure Y
  μr_prob : μr Set.univ = 1
  μb_prob : μb Set.univ = 1
  seminormaL : H → ℝ
  seminormaB : H → ℝ
  lambdaR : ℝ
  lambdaB : ℝ
  regularizadorR : ℝ
  regularizadorB : ℝ
  mr_pos : 0 < mr
  mb_pos : 0 < mb
  lambdaR_pos : 0 < lambdaR
  lambdaB_pos : 0 < lambdaB
  regularizadorR_nonneg : 0 ≤ regularizadorR
  regularizadorB_nonneg : 0 ≤ regularizadorB

namespace ProblemaPINN

variable {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mr mb : ℕ} (P : ProblemaPINN H X Y mr mb)

/-- Primer sumando de `LossPINN_m`, con el promedio `1/mr`. -/
def perdidaEmpiricaInterior (h : H) : ℝ :=
  P.lambdaR / (mr : ℝ) *
    ∑ i : Fin mr, (P.L h (P.xr i) - P.f (P.xr i)) ^ 2

/-- Segundo sumando de `LossPINN_m`, con el promedio `1/mb`. -/
def perdidaEmpiricaFrontera (h : H) : ℝ :=
  P.lambdaB / (mb : ℝ) *
    ∑ j : Fin mb, (P.B h (P.xb j) - P.g (P.xb j)) ^ 2

/-- `LossPINN_m(h;λ)` de la tesis, sin regularización. -/
def perdidaEmpirica (h : H) : ℝ :=
  P.perdidaEmpiricaInterior h + P.perdidaEmpiricaFrontera h

/-- `LossPINN(h;λ)` poblacional. La integrabilidad de sus sumandos se
formula aparte, porque no se deduce de la definición algebraica. -/
def perdidaPoblacional (h : H) : ℝ :=
  P.lambdaR * ∫ x, (P.L h x - P.f x) ^ 2 ∂P.μr +
    P.lambdaB * ∫ y, (P.B h y - P.g y) ^ 2 ∂P.μb

def PoblacionIntegrable (h : H) : Prop :=
  Integrable (fun x => (P.L h x - P.f x) ^ 2) P.μr ∧
    Integrable (fun y => (P.B h y - P.g y) ^ 2) P.μb

/-- `[L[h]]²_{α;U}`. El valor de la seminorma es un parámetro; su
caracterización Hölder se exige separadamente cuando se use cobertura. -/
def regularidadInterior (h : H) : ℝ := (P.seminormaL h) ^ 2

/-- `[B[h]]²_{α;Γ}`. -/
def regularidadFrontera (h : H) : ℝ := (P.seminormaB h) ^ 2

def regularidadTotal (h : H) : ℝ :=
  P.regularidadInterior h + P.regularidadFrontera h

/-- `Loss_m(h;λ,λ_R,m)` de (3.22). Los pesos de los dos seminormas
pueden ser distintos. -/
def funcionalRegularizado (h : H) : ℝ :=
  P.perdidaEmpirica h +
    P.regularizadorR * P.regularidadInterior h +
    P.regularizadorB * P.regularidadFrontera h

theorem perdidaEmpiricaInterior_nonneg (h : H) :
    0 ≤ P.perdidaEmpiricaInterior h := by
  unfold perdidaEmpiricaInterior
  apply mul_nonneg
  · exact div_nonneg P.lambdaR_pos.le (Nat.cast_nonneg _)
  · exact Finset.sum_nonneg fun i hi => sq_nonneg _

theorem perdidaEmpiricaFrontera_nonneg (h : H) :
    0 ≤ P.perdidaEmpiricaFrontera h := by
  unfold perdidaEmpiricaFrontera
  apply mul_nonneg
  · exact div_nonneg P.lambdaB_pos.le (Nat.cast_nonneg _)
  · exact Finset.sum_nonneg fun j hj => sq_nonneg _

theorem perdidaEmpirica_nonneg (h : H) : 0 ≤ P.perdidaEmpirica h :=
  add_nonneg (P.perdidaEmpiricaInterior_nonneg h)
    (P.perdidaEmpiricaFrontera_nonneg h)

theorem regularidadTotal_nonneg (h : H) : 0 ≤ P.regularidadTotal h :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem funcionalRegularizado_nonneg (h : H) :
    0 ≤ P.funcionalRegularizado h := by
  unfold funcionalRegularizado
  exact add_nonneg
    (add_nonneg (P.perdidaEmpirica_nonneg h)
      (mul_nonneg P.regularizadorR_nonneg (sq_nonneg _)))
    (mul_nonneg P.regularizadorB_nonneg (sq_nonneg _))

theorem perdidaPoblacional_nonneg (h : H) (_hInt : P.PoblacionIntegrable h) :
    0 ≤ P.perdidaPoblacional h := by
  unfold perdidaPoblacional
  apply add_nonneg
  · exact mul_nonneg P.lambdaR_pos.le (integral_nonneg fun x => sq_nonneg _)
  · exact mul_nonneg P.lambdaB_pos.le (integral_nonneg fun y => sq_nonneg _)

/-- La fórmula con pesos iguales `a_m` de (3.23). -/
theorem funcional_pesos_iguales (h : H) (a : ℝ)
    (hR : P.regularizadorR = a) (hB : P.regularizadorB = a) :
    P.funcionalRegularizado h =
      P.perdidaEmpirica h + a * P.regularidadTotal h := by
  simp [funcionalRegularizado, regularidadTotal, hR, hB, mul_add]
  ring

/-- Definición de minimizador global sobre la clase admisible `H_m`. -/
def EsMinimizadorGlobal (Hm : Set H) (hm : H) : Prop :=
  hm ∈ Hm ∧ ∀ g ∈ Hm, P.funcionalRegularizado hm ≤ P.funcionalRegularizado g

theorem comparacion_global (Hm : Set H) (hm g : H)
    (hmin : P.EsMinimizadorGlobal Hm hm) (hg : g ∈ Hm) :
    P.funcionalRegularizado hm ≤ P.funcionalRegularizado g :=
  hmin.2 g hg

/-- Interpolación exacta (3.24), expresada para un comparador admisible. -/
def ComparadorExacto (Hm : Set H) (g : H) : Prop :=
  g ∈ Hm ∧ P.perdidaEmpirica g = 0

theorem comparacion_con_interpolador (Hm : Set H) (hm g : H)
    (hmin : P.EsMinimizadorGlobal Hm hm)
    (hg : P.ComparadorExacto Hm g)
    (a : ℝ) (haR : P.regularizadorR = a)
    (haB : P.regularizadorB = a) :
    P.perdidaEmpirica hm + a * P.regularidadTotal hm ≤
      a * P.regularidadTotal g := by
  have hc := P.comparacion_global Hm hm g hmin hg.1
  rw [P.funcional_pesos_iguales hm a haR haB,
    P.funcional_pesos_iguales g a haR haB, hg.2, zero_add] at hc
  exact hc

/-- (3.29): la regularidad del minimizador no supera la del comparador. -/
theorem regularidad_minimizador_le_comparador (Hm : Set H) (hm g : H)
    (hmin : P.EsMinimizadorGlobal Hm hm)
    (hg : P.ComparadorExacto Hm g)
    (a : ℝ) (ha : 0 < a)
    (haR : P.regularizadorR = a) (haB : P.regularizadorB = a) :
    P.regularidadTotal hm ≤ P.regularidadTotal g :=
  regularidad_controlada a (P.perdidaEmpirica hm)
    (P.regularidadTotal hm) (P.regularidadTotal g) ha
    (P.perdidaEmpirica_nonneg hm)
    (P.comparacion_con_interpolador Hm hm g hmin hg a haR haB)

/-- (3.30) en su parte empírica. La cota es de `LossPINN_m`, no de
`LossPINN`; ese segundo paso necesita cobertura. -/
theorem perdidaEmpirica_minimizador_le (Hm : Set H) (hm g : H)
    (hmin : P.EsMinimizadorGlobal Hm hm)
    (hg : P.ComparadorExacto Hm g)
    (a : ℝ) (ha : 0 < a)
    (haR : P.regularizadorR = a) (haB : P.regularizadorB = a) :
    P.perdidaEmpirica hm ≤ a * P.regularidadTotal g :=
  perdida_empirica_controlada a (P.perdidaEmpirica hm)
    (P.regularidadTotal hm) (P.regularidadTotal g) ha
    (P.regularidadTotal_nonneg hm)
    (P.comparacion_con_interpolador Hm hm g hmin hg a haR haB)

/-- (3.30) con la cota uniforme del comparador como premisa explícita. -/
theorem perdidaEmpirica_le_regularidad_uniforme (Hm : Set H) (hm g : H)
    (hmin : P.EsMinimizadorGlobal Hm hm)
    (hg : P.ComparadorExacto Hm g)
    (a Rstar : ℝ) (ha : 0 < a)
    (haR : P.regularizadorR = a) (haB : P.regularizadorB = a)
    (hRstar : P.regularidadTotal g ≤ Rstar) :
    P.perdidaEmpirica hm ≤ a * Rstar :=
  (P.perdidaEmpirica_minimizador_le Hm hm g hmin hg a ha haR haB).trans
    (mul_le_mul_of_nonneg_left hRstar ha.le)

end ProblemaPINN

#print axioms TesisPINN.ProblemaPINN.perdidaEmpirica_nonneg
#print axioms TesisPINN.ProblemaPINN.funcionalRegularizado_nonneg
#print axioms TesisPINN.ProblemaPINN.comparacion_global
#print axioms TesisPINN.ProblemaPINN.regularidad_minimizador_le_comparador
#print axioms TesisPINN.ProblemaPINN.perdidaEmpirica_minimizador_le
#print axioms TesisPINN.ProblemaPINN.perdidaEmpirica_le_regularidad_uniforme

end TesisPINN

