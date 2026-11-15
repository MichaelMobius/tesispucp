import TesisPINN.GeometriaFronteraCuadrado
import TesisPINN.Teorema34Dimensional
import TesisPINN.Proposicion311
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

theorem radioFronteraCuadrado_raiz (m : ℕ) (hm : 0 < m) :
    radio34 (1 / 12) 1 m = 12 * Real.sqrt 2 / Real.sqrt (m : ℝ) := by
  have h := escalaAuxiliarRaiz_masa (1 / 12) 1 m (by norm_num) (by norm_num) hm
  rw [Real.rpow_one] at h
  rw [radio34, show escalaAuxiliarRaiz (1 / 12) 1 m = (1 / Real.sqrt m) / (1 / 12) from
    (eq_div_iff (by norm_num)).2 (by simpa [mul_comm] using h)]
  ring

theorem radioFronteraCuadrado_le_uno (m : ℕ) (hm : 288 ≤ m) :
    radio34 (1 / 12) 1 m ≤ 1 := by
  have hmp : 0 < m := by omega
  have hpos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hmp)
  rw [radioFronteraCuadrado_raiz m hmp, div_le_iff₀ hpos, one_mul]
  apply (sq_le_sq₀ (by positivity) hpos.le).1
  rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (Nat.cast_nonneg _)]
  norm_num
  exact hm

/-- T3.4 para las dos leyes del cuadrado y sus prefijos en el espacio producto. -/
theorem teorema34_cuadrado_dos_familias {H : Type*}
    (op : Operadores38 H Plano Plano) (Hm : Set H)
    (mr mb : ℕ) (hr : 324 ≤ mr) (hb : 288 ≤ mb)
    (lr lb α Sf Sg : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (hHolder : op.CotasHolder34 Hm cuadrado (frontier cuadrado) α Sf Sg) :
    let Pω := fun ω : EspacioMuestrasCuadrado =>
      op.problema34 medidaUniformeCuadrado medidaUniformeFrontera mr mb
        (by omega) (by omega) (Real.pi / 4) 1 (1 / 9) (1 / 12) lr lb α
        (by positivity) (by norm_num) (by norm_num) hlr hlb
        (fun i => muestreoInteriorCuadrado.Z i ω) (fun i => muestreoFronteraCuadrado.Z i ω)
    ∃ A : Set EspacioMuestrasCuadrado, MeasurableSet A ∧
      1 - falloRaiz34 mr - falloRaiz34 mb ≤ probabilidadMuestrasCuadrado.real A ∧
      ∀ ω ∈ A, ∀ h ∈ Hm, (Pω ω).perdidaPoblacional h ≤
        factor34 mr mb (Real.pi / 4) 1 (1 / 9) (1 / 12) * (Pω ω).funcionalRegularizado h +
        constante34 lr lb (1 / 9) (1 / 12) α Sf Sg * ((mr : ℝ) ^ (-(α / 2)) + (mb : ℝ) ^ (-α)) := by
  have hmr : 0 < mr := by omega
  have hmb : 0 < mb := by omega
  exact teorema34_dim2_de_dimensional probabilidadMuestrasCuadrado
    medidaUniformeCuadrado medidaUniformeFrontera cuadrado (frontier cuadrado) 1
    datosMasa38_interior_cuadrado datosMasa38_frontera_cuadrado muestreoInteriorCuadrado
    muestreoFronteraCuadrado op Hm mr mb hmr hmb lr lb α Sf Sg hlr hlb hα
    ((radioRaizCuadrado_le_uno_iff mr hmr).2 hr) (radioFronteraCuadrado_le_uno mb hb) hHolder

#check muestreoInteriorCuadrado
#check muestreoFronteraCuadrado
#check muestreosCuadrado_independientes
#print axioms muestreoInteriorCuadrado
#print axioms muestreoFronteraCuadrado
#print axioms muestreosCuadrado_independientes
#print axioms muestreosCuadrado_en_soportes
#check teorema34_cuadrado_dos_familias
#print axioms teorema34_cuadrado_dos_familias

end TesisPINN
