import TesisPINN.Puente326_315
import TesisPINN.Corolario323

/-! Convergencia espectral de los minimizadores neuronales manufacturados. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Filter Set Asymptotics EllipticPdes EllipticPdes.H1Graph
open scoped Topology Distributions

private def factorSolucionManufacturada (x : Plano) : ℝ :=
  aManufacturada (x 0) * aManufacturada (x 1)

private theorem factorSolucionManufacturada_suave :
    ContDiff ℝ (⊤ : ℕ∞) factorSolucionManufacturada :=
  ((aManufacturada_suave _).comp (EuclideanSpace.proj (0 : Fin 2)).contDiff).mul
    ((aManufacturada_suave _).comp (EuclideanSpace.proj (1 : Fin 2)).contDiff)

def solucionSobolevManufacturada : W12 (volume : Measure Plano) cuadrado :=
  ⟨psiGraph factorSolucionManufacturada factorSolucionManufacturada_suave,
    H01_le_W12 (psiGraph_mem_H01 _ _)⟩

def candidatoSobolev326 {D : ℕ} (a : Coeficientes324 D) :
    W12 (volume : Measure Plano) cuadrado :=
  ⟨psiGraph (polinomioPlano326 a) (polinomioPlano326_suave a),
    H01_le_W12 (psiGraph_mem_H01 _ _)⟩

theorem solucionSobolevManufacturada_ae :
    ⇑(fnL (solucionSobolevManufacturada : H1Graph volume cuadrado)) =ᵐ[volumenPoisson]
      solucionManufacturada := by
  rw [show solucionManufacturada = _ from funext solucionManufacturada_factorizada]
  exact psiGraph_fnL_ae factorSolucionManufacturada factorSolucionManufacturada_suave

theorem candidatoSobolev326_ae {D : ℕ} (a : Coeficientes324 D) :
    ⇑(fnL (candidatoSobolev326 a : H1Graph volume cuadrado)) =ᵐ[volumenPoisson] candidato326 D a := by
  rw [show candidato326 D a = _ from funext (candidato326_eq a)]
  exact psiGraph_fnL_ae (polinomioPlano326 a) (polinomioPlano326_suave a)

theorem trazasManufacturadas_iguales {D : ℕ} (a : Coeficientes324 D) :
    trazaSobolevCuadrado (candidatoSobolev326 a) = trazaSobolevCuadrado solucionSobolevManufacturada := by
  rw [trazaSobolevCuadrado_cero_de_H01 _ (psiGraph_mem_H01 (polinomioPlano326 a) (polinomioPlano326_suave a)),
    trazaSobolevCuadrado_cero_de_H01 _ (psiGraph_mem_H01 factorSolucionManufacturada factorSolucionManufacturada_suave)]

def errorSobolevManufacturado {D : ℕ} (a : Coeficientes324 D) :
    H01 (volume : Measure Plano) cuadrado :=
  ⟨(candidatoSobolev326 a : H1Graph volume cuadrado) - solucionSobolevManufacturada,
    diferencia_mem_H01_de_trazas_iguales _ _ (trazasManufacturadas_iguales a)⟩

def fuenteLpManufacturada : Lp ℝ 2 volumenPoisson :=
  laplacianoLp solucionManufacturada (datosPoisson325_regulares.1.of_le le_top)

def laplacianoLp326 {D : ℕ} (a : Coeficientes324 D) : Lp ℝ 2 volumenPoisson :=
  laplacianoLp (candidato326 D a) (candidato326_suave a)

theorem laplaciano_solucionSobolevManufacturada :
    laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL (solucionSobolevManufacturada :
        H1Graph volume cuadrado)) volume ⊤) =
        Distribution.ofFun cuadradoOpens fuenteLpManufacturada volume ⊤ := by
  rw [Distribution.ofFun_congr_ae solucionSobolevManufacturada_ae]
  exact laplaciano_distribucional_eq_laplacianoLp _ _

theorem laplaciano_candidatoSobolev326 {D : ℕ} (a : Coeficientes324 D) :
    laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL (candidatoSobolev326 a :
        H1Graph volume cuadrado)) volume ⊤) =
        Distribution.ofFun cuadradoOpens (laplacianoLp326 a) volume ⊤ := by
  rw [Distribution.ofFun_congr_ae (candidatoSobolev326_ae a)]
  exact laplaciano_distribucional_eq_laplacianoLp _ _

def residuoManufacturado326 {D : ℕ} (a : Coeficientes324 D) : Lp ℝ 2 volumenPoisson :=
  laplacianoLp326 a - fuenteLpManufacturada

theorem laplaciano_errorSobolevManufacturado {D : ℕ} (a : Coeficientes324 D) :
    HasDistributionalLaplacian cuadradoOpens volume (errorSobolevManufacturado a)
      (residuoManufacturado326 a) :=
  laplaciano_diferencia323 _ _ _ _ _ (laplaciano_candidatoSobolev326 a)
    laplaciano_solucionSobolevManufacturada

theorem residuoManufacturado326_ae {D : ℕ} (a : Coeficientes324 D) :
    ⇑(residuoManufacturado326 a) =ᵐ[volumenPoisson] (laplaciano326 D a - fuenteManufacturada) := by
  have hf : ⇑fuenteLpManufacturada =ᵐ[volumenPoisson] fuenteManufacturada :=
    (laplacianoLp_ae _ _).trans (Filter.EventuallyEq.of_eq (funext laplaciano_solucionManufacturada))
  exact (Lp.coeFn_sub _ _).trans ((laplacianoLp_ae _ _).sub hf)

theorem norma_residuoManufacturado326 {D : ℕ} (a : Coeficientes324 D) :
    ‖residuoManufacturado326 a‖ =
      2 * Real.sqrt (perdidaPoissonInterior (laplaciano326 D a) fuenteManufacturada) :=
  norma_residuo323_de_perdida_escalar _ _ _ (residuoManufacturado326_ae a)

set_option maxHeartbeats 800000 in
/-- Ambas cotas espectrales, con el factor dos de la normalización de la pérdida.
El representante continuo de P3.22 coincide con el error clásico en la clausura. -/
theorem estimacion_simultanea_manufacturada {D : ℕ} (a : Coeficientes324 D) :
    let e := (errorSobolevManufacturado a : H1Graph volume cuadrado)
    let E := perdidaPoissonInterior (laplaciano326 D a) fuenteManufacturada
    ‖e‖ + normaEsencial323 e ≤ (2 * constanteSimultanea323) * Real.sqrt E ∧
    supResiduo (closure cuadrado) (candidato326 D a - solucionManufacturada) = normaEsencial323 e := by
  obtain ⟨_, _, hsum, g, hg, hgae, _, hsup⟩ := cotas_simultaneas323 _ _
    (laplaciano_errorSobolevManufacturado a)
  have he : ⇑(fnL (errorSobolevManufacturado a : H1Graph volume cuadrado))
      =ᵐ[volumenPoisson] (candidato326 D a - solucionManufacturada) := by
    change ⇑(fnL ((candidatoSobolev326 a : H1Graph volume cuadrado) -
      (solucionSobolevManufacturada : H1Graph volume cuadrado))) =ᵐ[volumenPoisson] _
    rw [map_sub]
    exact (Lp.coeFn_sub _ _).trans ((candidatoSobolev326_ae a).sub solucionSobolevManufacturada_ae)
  have hsame := representante323_coincide _ (candidato326_suave a).continuous.continuousOn
    datosPoisson325_regulares.1.continuous.continuousOn hg.continuousOn he hgae
  refine ⟨?_, (supResiduo_congr hsame.symm).trans hsup⟩
  rw [norma_residuoManufacturado326, ← mul_assoc, mul_comm constanteSimultanea323 2] at hsum
  exact hsum

/-- Evaluación de la red cuadrática de L3.24 en coordenadas euclidianas. -/
def redManufacturada326 {m : ℕ} (hm : 1 ≤ m) (a : Coeficientes324 (4 * m - 1)) (x : Plano) : ℝ :=
  (red324 (show 2 ≤ 4 * m - 1 by omega)).salida (pesoSalida324 a)
    (fun b => if b then x 0 else x 1)

theorem redManufacturada326_eq {m : ℕ} (hm : 1 ≤ m) (a : Coeficientes324 (4 * m - 1)) :
    redManufacturada326 hm a = candidato326 (4 * m - 1) a := by
  funext x
  exact red324_salida _ a _

/-- Convergencia de la familia de redes seleccionada en el mismo evento casi
seguro de pérdida de P3.15. -/
theorem convergencia_neuronal_manufacturada {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Muestreo38 P medidaUniformeCuadrado) :
    ∃ a : ∀ m : ℕ, (Fin m → Plano) → Coeficientes324 (4 * m - 1),
      (∀ m, Measurable (a m) ∧ Measurable (fun s => pesoSalida324 (a m s))) ∧
      (∀ m (hm : 1 ≤ m) (s : Fin m → Plano),
        EqOn (redManufacturada326 hm (a m s)) 0 (frontier cuadrado)) ∧
      (∀ m (hm : 310 ≤ m) (s : Fin m → Plano),
        IsMinOn (fun h : Plano → ℝ => funcionalPoissonInterior s
          (laplacianoClásico h) fuenteManufacturada) (range (candidato326 (4 * m - 1)))
          (redManufacturada326 (show 1 ≤ m by omega) (a m s))) ∧
      ∀ᵐ ω ∂P,
        let b := fun m => a m (prefijoPoisson P Z m ω)
        let e := fun m => errorSobolevManufacturado (b m)
        (fun m => perdidaPoissonInterior (laplaciano326 (4 * m - 1) (b m)) fuenteManufacturada)
          =O[atTop] escalaPerdida315 ∧
        (fun m => ‖(e m : H1Graph volume cuadrado)‖ + normaEsencial323 (e m)) =O[atTop]
          (fun m : ℕ => (Real.log (m : ℝ) / m) ^ (1 / 4 : ℝ)) ∧
        Tendsto (fun m => (candidatoSobolev326 (b m) : H1Graph volume cuadrado))
          atTop (𝓝 (solucionSobolevManufacturada : H1Graph volume cuadrado)) ∧
        Tendsto (fun m => normaEsencial323 (e m)) atTop (𝓝 0) := by
  obtain ⟨a, hmeas, hmin, hrate⟩ := perdida_minimizadores326_logaritmica P Z
  refine ⟨a, fun m => ⟨hmeas m, (pesosSalida324_continuos _).measurable.comp (hmeas m)⟩,
    ?_, ?_, ?_⟩
  · intro m hm s x hx
    simp [redManufacturada326_eq, candidato326_eq, psiCuadrado_cero_frontera _ hx]
  · intro m hm s
    rw [redManufacturada326_eq]
    exact (minimo326_equiv_clase s (pesoLogInterior m) (a m s)).mp (hmin m hm s)
  · filter_upwards [hrate] with ω hω
    let b := fun m => a m (prefijoPoisson P Z m ω)
    let e := fun m => errorSobolevManufacturado (b m)
    obtain ⟨hjoint, hH, hInf⟩ := transferencia_simultanea323 e
      (fun m => residuoManufacturado326 (b m)) _
      (fun m => laplaciano_errorSobolevManufacturado (b m))
      (fun _ => perdidaInterior_nonneg _ _ _)
      (fun m => norma_residuoManufacturado326 (b m)) hω
    exact ⟨hω, hjoint, tendsto_iff_norm_sub_tendsto_zero.mpr hH, hInf⟩

#check convergencia_neuronal_manufacturada
#print axioms estimacion_simultanea_manufacturada
#print axioms convergencia_neuronal_manufacturada

end TesisPINN

