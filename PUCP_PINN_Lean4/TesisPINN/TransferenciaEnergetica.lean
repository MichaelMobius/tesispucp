import TesisPINN.ResiduoCuadrado

/-!
# Constante energética uniforme y transferencia determinista

Se fija una sola constante para `U=(-1,1)²`, independiente del error, del
residuo y del índice de aproximación. No se hacen afirmaciones probabilísticas.
-/

noncomputable section

open MeasureTheory TopologicalSpace Topology Filter EllipticPdes EllipticPdes.H1Graph
open scoped RealInnerProductSpace Distributions

namespace TesisPINN

private theorem existe_constante_energia_uniforme :
    ∃ K : ℝ, 0 < K ∧
      ∀ (e : H01 (volume : Measure Plano) cuadrado)
        (r : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado)),
        HasDistributionalLaplacian cuadradoOpens volume e r →
          ‖(e : H1Graph (volume : Measure Plano) cuadrado)‖ ≤ K * ‖r‖ := by
  obtain ⟨Cₚ, hCₚ, hP⟩ :=
    exists_poincare_constant (μ := (volume : Measure Plano)) cuadrado_acotado
  let K : ℝ := Cₚ * Real.sqrt (1 + Cₚ ^ 2)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro e r hΔ
  have htest := laplaciano_distribucional_implica_prueba cuadradoOpens volume e r hΔ
  have hGreen := green_por_densidad e r htest
  have hEnergy := energia_norma_par_debil Cₚ
    (fnL (e : H1Graph volume cuadrado)) r (gradL (e : H1Graph volume cuadrado))
    hCₚ hGreen (hP e)
  change ‖mk (fnL (e : H1Graph volume cuadrado))
    (gradL (e : H1Graph volume cuadrado))‖ ≤ _ at hEnergy
  rw [mk_fnL_gradL] at hEnergy
  exact hEnergy

/-- Una constante elegida una sola vez para el cuadrado y la medida de volumen. -/
def constanteEnergiaCuadrado : ℝ := Classical.choose existe_constante_energia_uniforme

theorem constanteEnergiaCuadrado_pos : 0 < constanteEnergiaCuadrado :=
  (Classical.choose_spec existe_constante_energia_uniforme).1

/-- Forma uniforme del Lema 3.19 en el cuadrado, con `K` fija. -/
theorem energia_cuadrado_uniforme
    (e : H01 (volume : Measure Plano) cuadrado)
    (r : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (hΔ : HasDistributionalLaplacian cuadradoOpens volume e r) :
    ‖(e : H1Graph (volume : Measure Plano) cuadrado)‖ ≤
      constanteEnergiaCuadrado * ‖r‖ :=
  (Classical.choose_spec existe_constante_energia_uniforme).2 e r hΔ

private theorem ofFun_lp_sub_uniforme
    (a b : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado)) :
    Distribution.ofFun cuadradoOpens (a - b) volume ⊤ =
      Distribution.ofFun cuadradoOpens a volume ⊤ -
        Distribution.ofFun cuadradoOpens b volume ⊤ := by
  calc
    Distribution.ofFun cuadradoOpens (a - b) volume ⊤ =
        Distribution.ofFun cuadradoOpens
          ((a : Plano → ℝ) - (b : Plano → ℝ)) volume ⊤ :=
      Distribution.ofFun_congr_ae (Lp.coeFn_sub a b)
    _ = Distribution.ofFun cuadradoOpens a volume ⊤ -
        Distribution.ofFun cuadradoOpens b volume ⊤ := by
      rw [sub_eq_add_neg, Distribution.ofFun_add
        (locallyIntegrableOn_lp a) (locallyIntegrableOn_lp b).neg,
        Distribution.ofFun_neg]
      rfl

/-- Residuo `Δ(ψq)-f` en `L²(U)` para un candidato suave. -/
def residuoAproximacion (q : Plano → ℝ)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (f : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado)) :
    Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado) :=
  laplacianoLp (fun x => psiCuadrado x * q x) (psiCuadrado_suave.mul hq) - f

/-- Identidad residual para una solución exacta general. -/
theorem laplaciano_error_psi_solucion_exacta
    (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤) :
    laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL (psiGraph q hq - u)) volume ⊤) =
        Distribution.ofFun cuadradoOpens (residuoAproximacion q hq f) volume ⊤ := by
  rw [map_sub, ofFun_lp_sub_uniforme, map_sub]
  rw [Distribution.ofFun_congr_ae (psiGraph_fnL_ae q hq)]
  rw [laplaciano_distribucional_eq_laplacianoLp
    (fun x => psiCuadrado x * q x) (psiCuadrado_suave.mul hq), hsol]
  exact (ofFun_lp_sub_uniforme _ _).symm

/-- Constante uniforme para todos los candidatos suaves `ψq` frente a `u*` fija. -/
theorem estimacion_uniforme_psi_solucion_exacta
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤)
    (q : Plano → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ‖psiGraph q hq - u‖ ≤
      constanteEnergiaCuadrado * ‖residuoAproximacion q hq f‖ := by
  let e : H01 (volume : Measure Plano) cuadrado :=
    ⟨psiGraph q hq - u, Submodule.sub_mem _ (psiGraph_mem_H01 q hq) hu⟩
  exact energia_cuadrado_uniforme e (residuoAproximacion q hq f)
    (laplaciano_error_psi_solucion_exacta q hq u f hsol)

/-- Transferencia cuantitativa de cualquier cota residual `εₘ`. -/
theorem cota_error_de_cota_residuo
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤)
    (q : ℕ → Plano → ℝ) (hq : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (q m))
    (ε : ℕ → ℝ)
    (hε : ∀ m, ‖residuoAproximacion (q m) (hq m) f‖ ≤ ε m) :
    ∀ m, ‖psiGraph (q m) (hq m) - u‖ ≤ constanteEnergiaCuadrado * ε m := by
  intro m
  exact (estimacion_uniforme_psi_solucion_exacta u f hu hsol (q m) (hq m)).trans
    (mul_le_mul_of_nonneg_left (hε m) constanteEnergiaCuadrado_pos.le)

/-- Convergencia `L²` del residuo implica convergencia `H¹` de los grafos.
El límite y la ecuación exacta son fijos; no interviene probabilidad. -/
theorem tendsto_psiGraph_de_residuo_l2
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤)
    (q : ℕ → Plano → ℝ) (hq : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (q m))
    (hres : Tendsto (fun m => residuoAproximacion (q m) (hq m) f)
      atTop (𝓝 0)) :
    Tendsto (fun m => psiGraph (q m) (hq m)) atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hnorm : Tendsto (fun m => ‖residuoAproximacion (q m) (hq m) f‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, norm_zero] using (continuous_norm.tendsto
      (0 : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))).comp hres
  apply squeeze_zero (fun m => norm_nonneg _)
    (fun m => estimacion_uniforme_psi_solucion_exacta u f hu hsol (q m) (hq m))
  simpa using (tendsto_const_nhds.mul hnorm :
    Tendsto (fun m => constanteEnergiaCuadrado *
      ‖residuoAproximacion (q m) (hq m) f‖) atTop
      (𝓝 (constanteEnergiaCuadrado * 0)))

/-- Si una cota numérica del residuo tiende a cero, también lo hace el error H¹. -/
theorem tendsto_psiGraph_de_cota_residuo
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤)
    (q : ℕ → Plano → ℝ) (hq : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (q m))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hres : ∀ m, ‖residuoAproximacion (q m) (hq m) f‖ ≤ ε m) :
    Tendsto (fun m => psiGraph (q m) (hq m)) atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun m => norm_nonneg _)
    (cota_error_de_cota_residuo u f hu hsol q hq ε hres)
  simpa using (tendsto_const_nhds.mul hε :
    Tendsto (fun m => constanteEnergiaCuadrado * ε m) atTop
      (𝓝 (constanteEnergiaCuadrado * 0)))

/-- La transferencia conserva un exponente de tasa supuesto para el residuo.
No se demuestra aquí que el residuo tenga esta tasa. -/
theorem tasa_potencia_psi
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤)
    (q : ℕ → Plano → ℝ) (hq : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (q m))
    (A β : ℝ)
    (hres : ∀ m, ‖residuoAproximacion (q m) (hq m) f‖ ≤
      A * ((m : ℝ) + 1) ^ (-β)) :
    ∀ m, ‖psiGraph (q m) (hq m) - u‖ ≤
      (constanteEnergiaCuadrado * A) * ((m : ℝ) + 1) ^ (-β) := by
  intro m
  calc
    ‖psiGraph (q m) (hq m) - u‖ ≤
        constanteEnergiaCuadrado * ‖residuoAproximacion (q m) (hq m) f‖ :=
      estimacion_uniforme_psi_solucion_exacta u f hu hsol (q m) (hq m)
    _ ≤ constanteEnergiaCuadrado * (A * ((m : ℝ) + 1) ^ (-β)) :=
      mul_le_mul_of_nonneg_left (hres m) constanteEnergiaCuadrado_pos.le
    _ = (constanteEnergiaCuadrado * A) * ((m : ℝ) + 1) ^ (-β) := by ring

/-- La misma cota se aplica realización por realización en cualquier evento `A`.
No se afirma que `A` tenga probabilidad uno. -/
theorem cota_error_en_evento
    {S : Type*} (A : Set S)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (f : Lp ℝ 2 ((volume : Measure Plano).restrict cuadrado))
    (hu : u ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
        Distribution.ofFun cuadradoOpens f volume ⊤)
    (q : S → ℕ → Plano → ℝ)
    (hq : ∀ ω m, ContDiff ℝ (⊤ : ℕ∞) (q ω m))
    (ε : S → ℕ → ℝ)
    (hε : ∀ ω ∈ A, ∀ m,
      ‖residuoAproximacion (q ω m) (hq ω m) f‖ ≤ ε ω m) :
    ∀ ω ∈ A, ∀ m,
      ‖psiGraph (q ω m) (hq ω m) - u‖ ≤
        constanteEnergiaCuadrado * ε ω m := by
  intro ω hω
  exact cota_error_de_cota_residuo u f hu hsol (q ω) (hq ω) (ε ω) (hε ω hω)

#print axioms TesisPINN.constanteEnergiaCuadrado_pos
#print axioms TesisPINN.energia_cuadrado_uniforme
#print axioms TesisPINN.laplaciano_error_psi_solucion_exacta
#print axioms TesisPINN.estimacion_uniforme_psi_solucion_exacta
#print axioms TesisPINN.cota_error_de_cota_residuo
#print axioms TesisPINN.tendsto_psiGraph_de_residuo_l2
#print axioms TesisPINN.tendsto_psiGraph_de_cota_residuo
#print axioms TesisPINN.tasa_potencia_psi
#print axioms TesisPINN.cota_error_en_evento

end TesisPINN
