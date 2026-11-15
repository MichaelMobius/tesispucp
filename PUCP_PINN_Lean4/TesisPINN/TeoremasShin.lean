import TesisPINN.Lema31
import TesisPINN.Teorema38Evento
import TesisPINN.Teorema318
import TesisPINN.DirichletLevantamiento
import TesisPINN.GeometriaMuestreoCuadrado

/-!
# Capítulo III: índice de los resultados que proceden de Shin–Darbon–Karniadakis

Correspondencia entre el artículo `shin2020convergence`, la numeración de la
tesis y las declaraciones Lean. Las redes del Lema 3.1 tienen dimensión de
entrada arbitraria. Las cotas de ocupación son abstractas. Los resultados
conjuntos de los Teoremas 3.4 y 3.8 usan exponentes de masa 2 en el interior
y 1 en la frontera.

| Shin et al.      | Tesis          | Declaración Lean                                   |
|------------------|----------------|----------------------------------------------------|
| Lemma 2.1 (afín) | Lema 3.1       | `lema31_regularidad`, `lema31_cotas`,              |
|                  |                | `lema31_equicontinuidad`, `lema31_precompacidad`   |
| Assumption 3.1   | Hipótesis 3.2  | `DatosMasa38`, `Muestreo38`                        |
| (consecuencia)   | Lema 3.3       | `masa_bola_inferior_de_particiones`                |
| Theorem 3.1      | Teorema 3.4    | `teorema34_dim2`                                   |
| Lemma B.1        | Lema 3.5       | `lema35_dim2`                                      |
| Lemma B.2        | Lema 3.6       | `lema36_probabilidad_cobertura`,                   |
|                  |                | `lema36_fallo_parametro`, `lema36_shin`,           |
|                  |                | `lema36_radio_dim2`, `lema36_radio_shin_dim2`      |
| Assumption 3.2   | Hipótesis 3.7  | `ProblemaPINN.EsMinimizadorGlobal`,                |
|                  |                | `ProblemaPINN.ComparadorExacto` (premisas)         |
| Theorem 3.2      | Teorema 3.8    | `teorema38_apartado1_dim2` (muestra finita, en el  |
|                  |                | evento de cobertura) y `teorema38_dim2` (casi      |
|                  |                | seguro: tasa, convergencia uniforme y tasas)       |
| (ruta propia)    | Lema 3.9       | `supResiduo_le_radio_truncado`,                    |
|                  |                | `tasa_supResiduo_de_integral`                      |
| Lemma D.1        | Lema 3.17      | `lema317_estabilidad_uniforme`                     |
| Theorem 3.3      | Teorema 3.18   | `teorema318_dim2`                                  |
| (Appendix E)     | Lema 3.19      | `energia_sobolev_de_laplaciano_de_prueba`          |
| Theorem 3.4      | Teorema 3.20   | `teorema320_poisson_de_teorema38`,                 |
|                  |                | `teorema320_levantado_de_teorema38`                |

No están formalizados: los casos unidimensionales de los Teoremas 3.4 y 3.8 y
las versiones en dimensión general `d ≥ 2` de los resultados de muestreo.

Este archivo solo reúne los enunciados y audita sus axiomas; no añade
matemática, salvo la instancia `datosMasa38_interior_cuadrado`.
-/

noncomputable section

namespace TesisPINN

open MeasureTheory

/-- Mitad interior de la Hipótesis 3.2 para el ejemplo de la tesis: la ley
uniforme en el cuadrado `(-1,1)²` la satisface con `ε₀ = 1`, `c_r = 1/9` y
`C_r = π/4`, las constantes del ejemplo que sigue al Lema 3.3. Los datos
de frontera se construyen en `GeometriaFronteraCuadrado.lean`. -/
def datosMasa38_interior_cuadrado :
    DatosMasa38 medidaUniformeCuadrado cuadrado 2 1 where
  c := 1 / 9
  C := Real.pi / 4
  c_pos := by norm_num
  C_pos := by positivity
  medible := cuadrado_abierto.measurableSet
  acotado := cuadrado_acotado
  concentrada := medidaUniformeCuadrado_concentrada
  superior := masa_bola_uniforme_cuadrado
  particiones := particiones_uniformes_cuadrado

-- Shin, Lemma 2.1.
#check @lema31_regularidad
#check @lema31_cotas
#check @lema31_equicontinuidad
#check @lema31_precompacidad
-- Shin, Theorem 3.1 y Appendix B.
#check @teorema34_dim2
#check @lema35_dim2
#check @lema36_probabilidad_cobertura
#check @lema36_fallo_parametro
#check @lema36_shin
#check @lema36_radio_shin_dim2
-- Shin, Theorem 3.2.
#check @teorema38_apartado1_dim2
#check @teorema38_dim2
-- Shin, Lemma D.1 y Theorem 3.3.
#check @lema317_estabilidad_uniforme
#check @teorema318_dim2
-- Shin, Theorem 3.4 y Appendix E.
#check @energia_sobolev_de_laplaciano_de_prueba
#check @teorema320_poisson_de_teorema38
#check @teorema320_levantado_de_teorema38

#print axioms TesisPINN.lema31_regularidad
#print axioms TesisPINN.lema31_cotas
#print axioms TesisPINN.lema31_equicontinuidad
#print axioms TesisPINN.lema31_precompacidad
#print axioms TesisPINN.teorema34_dim2
#print axioms TesisPINN.lema35_dim2
#print axioms TesisPINN.lema36_shin
#print axioms TesisPINN.teorema38_apartado1_dim2
#print axioms TesisPINN.teorema38_dim2
#print axioms TesisPINN.lema317_estabilidad_uniforme
#print axioms TesisPINN.teorema318_dim2
#print axioms TesisPINN.energia_sobolev_de_laplaciano_de_prueba
#print axioms TesisPINN.teorema320_poisson_de_teorema38
#print axioms TesisPINN.teorema320_levantado_de_teorema38
#print axioms TesisPINN.datosMasa38_interior_cuadrado

end TesisPINN
