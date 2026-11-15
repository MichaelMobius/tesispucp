import TesisPINN.Lema31
import TesisPINN.Teorema38Evento
import TesisPINN.Teorema318
import TesisPINN.DirichletLevantamiento
import TesisPINN.GeometriaMuestreoCuadrado
import TesisPINN.Proposicion314Dimensional
import TesisPINN.Proposicion310Dimensional
import TesisPINN.Teorema38Unidimensional

/-!
# Capítulo III: índice de los resultados que proceden de Shin–Darbon–Karniadakis

Correspondencia entre el artículo `shin2020convergence`, la numeración de la
tesis y las declaraciones Lean. Las redes del Lema 3.1 tienen dimensión de
entrada arbitraria. Los Teoremas 3.4 y 3.8 para d ≥ 2 usan exponentes de
masa d y d−1 y diámetro √d. La aplicación a dominios concretos requiere
verificar los datos del registro `DatosMasaDimensional`.

| Shin et al.      | Tesis          | Declaración Lean                                   |
|------------------|----------------|----------------------------------------------------|
| Lemma 2.1 (afín) | Lema 3.1       | `lema31_regularidad`, `lema31_cotas`,              |
|                  |                | `lema31_equicontinuidad`, `lema31_precompacidad`   |
| Assumption 3.1   | Hipótesis 3.2  | `DatosMasaDimensional`, `Muestreo38`                 |
| (consecuencia)   | Lema 3.3       | `masa_bola_inferior_dimensional`                   |
| Theorem 3.1      | Teorema 3.4, d≥2 | `teorema34_dimensional`, `teorema34_dim2_de_dimensional` |
| Theorem 3.1      | Teorema 3.4, d=1 | `teorema34_unidimensional` (3.12) |
| Lemma B.1        | Lema 3.5       | `perdidaPoblacional_le_sumas_dimensional`          |
| Lemma B.2        | Lema 3.6       | `lema36_probabilidad_cobertura`,                   |
|                  |                | `lema36_fallo_parametro`, `lema36_shin`,           |
|                  |                | `lema36_cobertura_dimensional`                    |
| Assumption 3.2   | Hipótesis 3.7  | `ProblemaPINN.EsMinimizadorGlobal`,                |
|                  |                | `ProblemaPINN.ComparadorExacto` (premisas)         |
| Theorem 3.2      | Teorema 3.8, d≥2 | `teorema38_evento_dimensional` (muestra finita)     |
|                  |                | `teorema38_dimension_ge_dos` (tasas casi seguras)  |
| Theorem 3.2      | Teorema 3.8, d=1 | `teorema38_unidimensional_evento`, `teorema38_unidimensional` |
| (ruta propia)    | Lema 3.9       | `lema39_global_acotado`, `lema39_tasa`             |
| (ruta propia)    | Prop. 3.10     | `proposicion310_dimension_ge_dos`, `cotas310_dimensional_bajo_cobertura` |
| (ruta propia)    | Prop. 3.14     | `proposicion314_evento_dimensional`, `proposicion314_dimensional` |
| Lemma D.1        | Lema 3.17      | `lema317_estabilidad_uniforme`                     |
| Theorem 3.3      | Teorema 3.18   | `teorema318_dim2`                                  |
| (Appendix E)     | Lema 3.19      | `energia_sobolev_de_laplaciano_de_prueba`          |
| Theorem 3.4      | Teorema 3.20   | `teorema320_poisson_de_teorema38`,                 |
|                  |                | `teorema320_levantado_de_teorema38`                |

T3.4 cuantifica sobre todos los candidatos admisibles dentro de un mismo
evento medible. Las ramas de T3.8 cuantifican sobre selecciones de mínimos
y comparadores exactos. En d=1 se emplea un solo prefijo aleatorio y los
dos valores deterministas de frontera. P3.10 usa comparadores y mínimos
aproximados con tolerancias explícitas. P3.14 usa el funcional logarítmico.

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
#check @teorema34_dimensional
#check @teorema34_unidimensional
#check @lema35_dim2
#check @lema36_probabilidad_cobertura
#check @lema36_fallo_parametro
#check @lema36_shin
#check @lema36_radio_shin_dim2
-- Shin, Theorem 3.2.
#check @teorema38_apartado1_dim2
#check @teorema38_dim2
#check @teorema38_evento_dimensional
#check @teorema38_dimension_ge_dos
#check @teorema38_unidimensional_evento
#check @teorema38_unidimensional
#check @proposicion310_dimension_ge_dos
#check @proposicion314_dimensional
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
#print axioms TesisPINN.teorema34_unidimensional
#print axioms TesisPINN.teorema38_unidimensional
#print axioms TesisPINN.proposicion310_dimension_ge_dos

end TesisPINN
