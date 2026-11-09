import TesisPINN.LaplacianoDistribucional
import EllipticPdes.Poincare.BoxSlice

/-!
# Dirichlet exacto en el cuadrado abierto

Esta etapa especializa la estimación analítica al cuadrado `(-1,1)²`. La pertenencia
de un error general con traza nula a `H01` requiere una prueba de aproximación en
`H¹`; no se deduce solo de la igualdad puntual en la frontera.
-/

noncomputable section

open MeasureTheory TopologicalSpace EllipticPdes EllipticPdes.H1Graph
open scoped RealInnerProductSpace

namespace TesisPINN

/-- El dominio `(-1,1)²` de la arquitectura de Dirichlet. -/
def cuadrado : Set Plano :=
  EllipticPdes.Poincare.euclBox (fun _ : Fin 2 => (-1 : ℝ)) (fun _ => (1 : ℝ))

theorem cuadrado_abierto : IsOpen cuadrado :=
  EllipticPdes.Poincare.isOpen_euclBox _ _

theorem cuadrado_acotado : Bornology.IsBounded cuadrado := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2, ?_⟩
  intro x hx
  have hx0 : -1 < x 0 ∧ x 0 < 1 := hx 0
  have hx1 : -1 < x 1 ∧ x 1 < 1 := hx 1
  have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x
  nlinarith [norm_nonneg x]

/-- El cuadrado, como abierto para las distribuciones. -/
def cuadradoOpens : Opens Plano := ⟨cuadrado, cuadrado_abierto⟩

/-- Factor de frontera de la arquitectura PINN, para `g=0`. -/
def psiCuadrado (x : Plano) : ℝ :=
  (1 - (x 0) ^ 2) * (1 - (x 1) ^ 2)

theorem psiCuadrado_suave : ContDiff ℝ (⊤ : ℕ∞) psiCuadrado := by
  unfold psiCuadrado
  fun_prop

theorem psiCuadrado_cero_coord0 (x : Plano) (hx : (x 0) ^ 2 = 1) :
    psiCuadrado x = 0 := by
  simp [psiCuadrado, hx]

theorem psiCuadrado_cero_coord1 (x : Plano) (hx : (x 1) ^ 2 = 1) :
    psiCuadrado x = 0 := by
  simp [psiCuadrado, hx]

/-- Primer caso construido: si `q` tiene soporte compacto dentro del cuadrado,
`ψ q` es una función de prueba y por tanto su grafo pertenece a `H₀¹`.
La hipótesis de soporte de `q` es más fuerte que la suavidad requerida por la
arquitectura PINN general; no cubre `q` no nula hasta la frontera. -/
def psiPorPrueba (q : testFunctions cuadrado) : testFunctions cuadrado :=
  ⟨fun x => psiCuadrado x * (q : Plano → ℝ) x,
    psiCuadrado_suave.mul q.2.1,
    q.2.2.1.mul_left,
    (tsupport_mul_subset_right (f := psiCuadrado) (g := (q : Plano → ℝ))).trans
      q.2.2.2⟩

theorem psiPorPrueba_mem_H01 (q : testFunctions cuadrado) :
    testGraphₗ volume cuadrado (psiPorPrueba q) ∈
      H01 (volume : Measure Plano) cuadrado :=
  testGraphₗ_mem_H01 _

/-- La condición exacta de aproximación necesaria para introducir un grafo en
`H₀¹`: convergencia separada de la función y del gradiente en `L²`. -/
theorem mem_H01_de_aproximacion_l2
    (U : H1Graph (volume : Measure Plano) cuadrado)
    (φ : ℕ → testFunctions cuadrado)
    (hfn : Filter.Tendsto (fun n => fnL (testGraphₗ volume cuadrado (φ n)))
      Filter.atTop (nhds (fnL U)))
    (hgrad : Filter.Tendsto (fun n => gradL (testGraphₗ volume cuadrado (φ n)))
      Filter.atTop (nhds (gradL U))) :
    U ∈ H01 (volume : Measure Plano) cuadrado := by
  apply isClosed_H01.mem_of_tendsto (f := fun n => testGraphₗ volume cuadrado (φ n))
    (b := Filter.atTop)
  · exact H1Graph.tendsto_iff.mpr ⟨hfn, hgrad⟩
  · exact Filter.Eventually.of_forall (fun n => testGraphₗ_mem_H01 (φ n))

/-- Una vez demostrada la pertenencia a `H₀¹`, la densidad de pruebas produce
convergencia en `L²` de ambas componentes. -/
theorem existe_aproximacion_l2_de_H01
    (U : H01 (volume : Measure Plano) cuadrado) :
    ∃ φ : ℕ → testFunctions cuadrado,
      Filter.Tendsto (fun n => fnL (testGraphₗ volume cuadrado (φ n)))
        Filter.atTop (nhds (fnL (U : H1Graph volume cuadrado))) ∧
      Filter.Tendsto (fun n => gradL (testGraphₗ volume cuadrado (φ n)))
        Filter.atTop (nhds (gradL (U : H1Graph volume cuadrado))) := by
  obtain ⟨φ, hφ⟩ := exists_seq_testGraphₗ_tendsto U.2
  exact ⟨φ, H1Graph.tendsto_iff.mp hφ⟩

theorem psiPorPrueba_aproximacion_l2 (q : testFunctions cuadrado) :
    ∃ φ : ℕ → testFunctions cuadrado,
      Filter.Tendsto (fun n => fnL (testGraphₗ volume cuadrado (φ n)))
        Filter.atTop (nhds (fnL (testGraphₗ volume cuadrado (psiPorPrueba q)))) ∧
      Filter.Tendsto (fun n => gradL (testGraphₗ volume cuadrado (φ n)))
        Filter.atTop (nhds (gradL (testGraphₗ volume cuadrado (psiPorPrueba q)))) :=
  existe_aproximacion_l2_de_H01
    ⟨testGraphₗ volume cuadrado (psiPorPrueba q), psiPorPrueba_mem_H01 q⟩

/-- Cota determinista (3.74) especializada a `(-1,1)²`. El error ya es un
elemento de `H₀¹` y el residuo es su laplaciano distribucional en `L²`. -/
theorem energia_dirichlet_cuadrado
    (e : H01 (volume : Measure Plano) cuadrado)
    (r : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (hΔ : HasDistributionalLaplacian cuadradoOpens volume e r) :
    ∃ Cₚ : ℝ, 0 < Cₚ ∧
      ‖(e : H1Graph (volume : Measure Plano) cuadrado)‖ ≤
        Cₚ * Real.sqrt (1 + Cₚ ^ 2) * ‖r‖ :=
  energia_sobolev_plano_volumen cuadradoOpens cuadrado_acotado e r hΔ

/-- Forma de (3.74) para el error `h-u*` de dos grafos. Las premisas
`h-u* ∈ H₀¹` y `Δ(h-u*)=r` se muestran explícitas: la igualdad de valores
en la frontera aún no está conectada formalmente con la primera. -/
theorem estimacion_error_dirichlet_exacto
    (h u : H1Graph (volume : Measure Plano) cuadrado)
    (r : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (he : h - u ∈ H01 (volume : Measure Plano) cuadrado)
    (hΔ : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL (h - u)) volume ⊤) =
      Distribution.ofFun cuadradoOpens r volume ⊤) :
    ∃ Cₚ : ℝ, 0 < Cₚ ∧
      ‖h - u‖ ≤ Cₚ * Real.sqrt (1 + Cₚ ^ 2) * ‖r‖ := by
  let e : H01 (volume : Measure Plano) cuadrado := ⟨h - u, he⟩
  exact energia_dirichlet_cuadrado e r hΔ

/-- Caso concreto de dos candidatos `ψ q` con `q` de soporte compacto interior.
La pertenencia del error a `H₀¹` ya se deduce de las pruebas construidas arriba;
queda explícita solamente la identificación distribucional del residuo `r`. -/
theorem estimacion_psi_por_pruebas
    (qh qu : testFunctions cuadrado)
    (r : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (hΔ : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens
        (fnL (testGraphₗ volume cuadrado (psiPorPrueba qh) -
          testGraphₗ volume cuadrado (psiPorPrueba qu))) volume ⊤) =
      Distribution.ofFun cuadradoOpens r volume ⊤) :
    ∃ Cₚ : ℝ, 0 < Cₚ ∧
      ‖testGraphₗ volume cuadrado (psiPorPrueba qh) -
          testGraphₗ volume cuadrado (psiPorPrueba qu)‖ ≤
        Cₚ * Real.sqrt (1 + Cₚ ^ 2) * ‖r‖ := by
  apply estimacion_error_dirichlet_exacto _ _ r
    (Submodule.sub_mem _ (psiPorPrueba_mem_H01 qh) (psiPorPrueba_mem_H01 qu))
  exact hΔ

#print axioms TesisPINN.cuadrado_acotado
#print axioms TesisPINN.psiPorPrueba_mem_H01
#print axioms TesisPINN.mem_H01_de_aproximacion_l2
#print axioms TesisPINN.psiPorPrueba_aproximacion_l2
#print axioms TesisPINN.energia_dirichlet_cuadrado
#print axioms TesisPINN.estimacion_error_dirichlet_exacto
#print axioms TesisPINN.estimacion_psi_por_pruebas

end TesisPINN

