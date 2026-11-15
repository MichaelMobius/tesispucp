import TesisPINN.GeometriaFronteraCuadrado
import Mathlib.Probability.Independence.InfinitePi

/-! Espacio común para las dos sucesiones independientes de la Hipótesis 3.2. -/

noncomputable section

namespace TesisPINN

open MeasureTheory ProbabilityTheory

abbrev EspacioMuestrasCuadrado := (ℕ → Plano) × (ℕ → Plano)

def probabilidadMuestrasCuadrado : Measure EspacioMuestrasCuadrado :=
  (Measure.infinitePi fun _ : ℕ => medidaUniformeCuadrado).prod
    (Measure.infinitePi fun _ : ℕ => medidaUniformeFrontera)

instance : IsProbabilityMeasure probabilidadMuestrasCuadrado := by
  unfold probabilidadMuestrasCuadrado
  infer_instance

def muestreoInteriorCuadrado : Muestreo38 probabilidadMuestrasCuadrado medidaUniformeCuadrado where
  Z i ω := ω.1 i
  medible i := (measurable_pi_apply i).comp measurable_fst
  ley i := by
    change (probabilidadMuestrasCuadrado.map ((fun f : ℕ → Plano => f i) ∘ Prod.fst)) = _
    rw [← Measure.map_map (measurable_pi_apply i) measurable_fst, probabilidadMuestrasCuadrado,
      Measure.map_fst_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]
  indep := by
    have hz (i : ℕ) : Measurable (fun ω : EspacioMuestrasCuadrado => ω.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map hz).2
    have hfst : probabilidadMuestrasCuadrado.map (Prod.fst : EspacioMuestrasCuadrado → ℕ → Plano) =
        Measure.infinitePi (fun _ : ℕ => medidaUniformeCuadrado) := by
      rw [probabilidadMuestrasCuadrado, Measure.map_fst_prod, measure_univ, one_smul]
    change probabilidadMuestrasCuadrado.map Prod.fst = _
    rw [hfst]
    congr 1
    funext i
    rw [show (fun ω : EspacioMuestrasCuadrado => ω.1 i) =
      (fun f : ℕ → Plano => f i) ∘ Prod.fst from rfl, ← Measure.map_map (measurable_pi_apply i)
      measurable_fst, hfst, Measure.infinitePi_map_eval]

def muestreoFronteraCuadrado : Muestreo38 probabilidadMuestrasCuadrado medidaUniformeFrontera where
  Z i ω := ω.2 i
  medible i := (measurable_pi_apply i).comp measurable_snd
  ley i := by
    change (probabilidadMuestrasCuadrado.map ((fun f : ℕ → Plano => f i) ∘ Prod.snd)) = _
    rw [← Measure.map_map (measurable_pi_apply i) measurable_snd, probabilidadMuestrasCuadrado,
      Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]
  indep := by
    have hz (i : ℕ) : Measurable (fun ω : EspacioMuestrasCuadrado => ω.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map hz).2
    have hsnd : probabilidadMuestrasCuadrado.map (Prod.snd : EspacioMuestrasCuadrado → ℕ → Plano) =
        Measure.infinitePi (fun _ : ℕ => medidaUniformeFrontera) := by
      rw [probabilidadMuestrasCuadrado, Measure.map_snd_prod, measure_univ, one_smul]
    change probabilidadMuestrasCuadrado.map Prod.snd = _
    rw [hsnd]
    congr 1
    funext i
    rw [show (fun ω : EspacioMuestrasCuadrado => ω.2 i) =
      (fun f : ℕ → Plano => f i) ∘ Prod.snd from rfl, ← Measure.map_map (measurable_pi_apply i)
      measurable_snd, hsnd, Measure.infinitePi_map_eval]

/-- Independencia de las sucesiones completas, además de i.i.d. dentro de cada una. -/
theorem muestreosCuadrado_independientes :
    IndepFun (fun ω i => muestreoInteriorCuadrado.Z i ω)
      (fun ω i => muestreoFronteraCuadrado.Z i ω) probabilidadMuestrasCuadrado := by
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

theorem muestreosCuadrado_en_soportes :
    ∀ᵐ ω ∂probabilidadMuestrasCuadrado, ∀ i : ℕ,
      muestreoInteriorCuadrado.Z i ω ∈ cuadrado ∧
      muestreoFronteraCuadrado.Z i ω ∈ frontier cuadrado := by
  have hr := muestras_en_soporte_ae probabilidadMuestrasCuadrado medidaUniformeCuadrado
    muestreoInteriorCuadrado.Z _ medidaUniformeCuadrado_concentrada
    muestreoInteriorCuadrado.medible muestreoInteriorCuadrado.ley
  have hb := muestras_en_soporte_ae probabilidadMuestrasCuadrado medidaUniformeFrontera
    muestreoFronteraCuadrado.Z _ medidaUniformeFrontera_concentrada
    muestreoFronteraCuadrado.medible muestreoFronteraCuadrado.ley
  filter_upwards [hr, hb] with ω hωr hωb
  exact fun i => ⟨hωr i, hωb i⟩

#check muestreoInteriorCuadrado
#check muestreoFronteraCuadrado
#check muestreosCuadrado_independientes
#print axioms muestreoInteriorCuadrado
#print axioms muestreoFronteraCuadrado
#print axioms muestreosCuadrado_independientes
#print axioms muestreosCuadrado_en_soportes

end TesisPINN
