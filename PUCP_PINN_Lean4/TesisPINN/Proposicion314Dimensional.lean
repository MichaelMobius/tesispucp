import TesisPINN.Teorema38Dimensional
import TesisPINN.Proposicion314

/-! Generalización logarítmica con ambas dimensiones de masa parametrizadas. -/

noncomputable section

namespace TesisPINN

open Set MeasureTheory Filter Asymptotics
open scoped Topology

private def radioLogPositivo (D c s κ : ℝ) (m : ℕ) : ℝ :=
  if 3 ≤ m then radioCoberturaLog D c s κ m else 1

private theorem radioLogPositivo_pos (D c s κ : ℝ) (m : ℕ)
    (hD : 0 < D) (hc : 0 < c) (hκ : 0 < κ) :
    0 < radioLogPositivo D c s κ m := by
  unfold radioLogPositivo
  split
  next hm =>
    have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
    have hl : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    unfold radioCoberturaLog escalaAuxiliarLog
    positivity
  next _ => norm_num

def Operadores38.problemaLogDimensional
    {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (op : Operadores38 H X Y) (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] {mr mb : ℕ} (hmr : 0 < mr) (hmb : 0 < mb)
    (D sr sb Cr Cb cr cb κ lr lb α : ℝ)
    (hD : 0 < D) (hCr : 0 < Cr) (hcr : 0 < cr) (hcb : 0 < cb)
    (hκ : 0 < κ) (hlr : 0 < lr) (hlb : 0 < lb)
    (xr : Fin mr → X) (xb : Fin mb → Y) : ProblemaPINN H X Y mr mb :=
  let rr := radioLogPositivo D cr sr κ mr
  let rb := radioLogPositivo D cb sb κ mb
  let F := factorCoberturaDimensional mr mb Cr Cb rr rb sr sb
  have hr : 0 < rr := radioLogPositivo_pos _ _ _ _ _ hD hcr hκ
  have hb : 0 < rb := radioLogPositivo_pos _ _ _ _ _ hD hcb hκ
  op.problemaDimensional μr μb hmr hmb lr lb α rr rb F hlr hlb hr hb
    (factorCoberturaDimensional_pos _ _ _ _ _ _ _ _ hmr hCr hr) true xr xb

private theorem problemaLogDimensional_eq
    {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (op : Operadores38 H X Y) (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] {mr mb : ℕ} (hmr : 0 < mr) (hmb : 0 < mb)
    (D sr sb Cr Cb cr cb κ lr lb α : ℝ)
    (hD : 0 < D) (hCr : 0 < Cr) (hcr : 0 < cr) (hcb : 0 < cb)
    (hκ : 0 < κ) (hlr : 0 < lr) (hlb : 0 < lb)
    (xr : Fin mr → X) (xb : Fin mb → Y)
    (hr : 3 ≤ mr ∧ 0 < radioCoberturaLog D cr sr κ mr)
    (hb : 3 ≤ mb ∧ 0 < radioCoberturaLog D cb sb κ mb) :
    let rr := radioCoberturaLog D cr sr κ mr
    let rb := radioCoberturaLog D cb sb κ mb
    have hrr : 0 < rr := hr.2
    op.problemaLogDimensional μr μb hmr hmb D sr sb Cr Cb cr cb κ lr lb α
      hD hCr hcr hcb hκ hlr hlb xr xb =
    op.problemaDimensional μr μb hmr hmb lr lb α rr rb
      (factorCoberturaDimensional mr mb Cr Cb rr rb sr sb) hlr hlb hrr hb.2
      (factorCoberturaDimensional_pos _ _ _ _ _ _ _ _ hmr hCr hrr) true xr xb := by
  simp [Operadores38.problemaLogDimensional, radioLogPositivo, hr.1, hb.1]

/-- (3.61)–(3.62) para ambos prefijos. -/
theorem proposicion314_evento_dimensional
    {Ω H X Y : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] (U : Set X) (Γ : Set Y) (D sr sb ε₀ : ℝ)
    (dr : DatosMasaDimensional μr U D sr ε₀) (db : DatosMasaDimensional μb Γ D sb ε₀)
    (Zr : Muestreo38 P μr) (Zb : Muestreo38 P μb) (op : Operadores38 H X Y) (Hm : Set H)
    (hD : 0 < D) (hsr : 0 < sr) (hsb : 0 < sb) (hε : 0 < ε₀)
    (mr mb : ℕ) (κ lr lb α Sf Sg : ℝ) (hκ : 2 < κ) (hlr : 0 < lr) (hlb : 0 < lb)
    (hα : 0 < α) (hr : RadioLogAdmisible D dr.c sr κ ε₀ ε₀ mr)
    (hb : RadioLogAdmisible D db.c sb κ ε₀ ε₀ mb) (hHolder : op.CotasHolder34 Hm U Γ α Sf Sg) :
    let rr := radioCoberturaLog D dr.c sr κ mr
    let rb := radioCoberturaLog D db.c sb κ mb
    let F := factorCoberturaDimensional mr mb dr.C db.C rr rb sr sb
    let Pω := fun ω => op.problemaLogDimensional μr μb
      (show 0 < mr by have := hr.1; omega) (show 0 < mb by have := hb.1; omega)
      D sr sb dr.C db.C dr.c db.c κ lr lb α
      hD dr.C_pos dr.c_pos db.c_pos (by linarith) hlr hlb
      (fun i => Zr.Z i ω) (fun i => Zb.Z i ω)
    ∃ A : Set Ω, MeasurableSet A ∧
      1 - mayoranteFalloLog κ mr - mayoranteFalloLog κ mb ≤ P.real A ∧
      ∀ ω ∈ A, ∀ h ∈ Hm, (Pω ω).perdidaPoblacional h ≤ F * (Pω ω).funcionalRegularizado h +
        3 * lr * rr ^ (2 * α) * Sf ^ 2 + 3 * lb * rb ^ (2 * α) * Sg ^ 2 := by
  intro rr rb F Pω
  obtain ⟨Kr, cr, hAr, hpR, hcR⟩ := (lema313_cobertura_logaritmica P μr Zr.Z Zr.medible Zr.indep
    Zr.ley U D dr.c sr κ ε₀ ε₀ hD dr.c_pos hsr hκ hε hε dr.particiones id
    (Eventually.of_forall fun _ => le_rfl)).1 mr hr
  obtain ⟨Kb, cb, hAb, hpB, hcB⟩ := (lema313_cobertura_logaritmica P μb Zb.Z Zb.medible Zb.indep
    Zb.ley Γ D db.c sb κ ε₀ ε₀ hD db.c_pos hsb hκ hε hε db.particiones id
    (Eventually.of_forall fun _ => le_rfl)).1 mb hb
  let Ar := todasCeldasOcupadas Zr.Z mr cr
  let Ab := todasCeldasOcupadas Zb.Z mb cb
  let Sr := muestrasEnSoporte Zr.Z mr U
  let Sb := muestrasEnSoporte Zb.Z mb Γ
  have hAr' : MeasurableSet Ar := MeasurableSet.of_compl hAr
  have hAb' : MeasurableSet Ab := MeasurableSet.of_compl hAb
  have hSr := muestrasEnSoporte_measurable Zr.Z mr U dr.medible Zr.medible
  have hSb := muestrasEnSoporte_measurable Zb.Z mb Γ db.medible Zb.medible
  have hS0r : P.real Srᶜ = 0 := medidaReal_fallo_soporte P μr Zr.Z mr U dr.concentrada Zr.medible Zr.ley
  have hS0b : P.real Sbᶜ = 0 := medidaReal_fallo_soporte P μb Zb.Z mb Γ db.concentrada Zb.medible Zb.ley
  have hp := probReal_inter_cuatro_ge P Ar Ab Sr Sb hAr' hAb' hSr hSb
  change P.real Arᶜ ≤ _ at hpR
  change P.real Abᶜ ≤ _ at hpB
  refine ⟨(Ar ∩ Ab) ∩ (Sr ∩ Sb), (hAr'.inter hAb').inter (hSr.inter hSb), by linarith, ?_⟩
  rintro ω ⟨⟨hωr, hωb⟩, hsrω, hsbω⟩ h hh
  have hmr : 0 < mr := by have := hr.1; omega
  have hmb : 0 < mb := by have := hb.1; omega
  have heq := problemaLogDimensional_eq op μr μb hmr hmb D sr sb dr.C db.C dr.c db.c κ lr lb α
    hD dr.C_pos dr.c_pos db.c_pos (by linarith) hlr hlb
    (fun i => Zr.Z i ω) (fun i => Zb.Z i ω) ⟨hr.1, hr.2.2.2.2.1⟩
    ⟨hb.1, hb.2.2.2.2.1⟩
  change (Pω ω).perdidaPoblacional h ≤ _
  unfold Pω
  rw [heq]
  exact cota34_dimensional_bajo_cobertura μr μb U Γ D sr sb ε₀ dr db op Hm hmr hmb
    lr lb α Sf Sg rr rb hlr hlb hα hr.2.2.2.2.1 hb.2.2.2.2.1 hr.2.2.2.2.2 hb.2.2.2.2.2
    true _ _ hHolder ⟨hsrω, hsbω, hcR ω hωr, hcB ω hωb⟩ h hh

/-- (3.63) para comparadores exactos y mínimos del funcional logarítmico. -/
theorem proposicion314_dimensional
    {Ω H X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    [PseudoMetricSpace X] [PseudoMetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] (U : Set X) (Γ : Set Y) (D sr sb ε₀ : ℝ)
    (dr : DatosMasaDimensional μr U D sr ε₀) (db : DatosMasaDimensional μb Γ D sb ε₀)
    (Zr : Muestreo38 P μr) (Zb : Muestreo38 P μb) (op : Operadores38 H X Y)
    (hD : 0 < D) (hsr : 0 < sr) (hsb : 0 < sb) (hε : 0 < ε₀)
    (mr mb : ℕ → ℕ) (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (hgr : ∀ᶠ n in atTop, n ≤ mr n) (hgb : ∀ᶠ n in atTop, n ≤ mb n)
    (κ lr lb α Sf Sg : ℝ) (hκ : 2 < κ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (Hm : ℕ → Set H) (h v : ∀ n, Ω → Hm n)
    (_hh : ∀ n, Measurable (fun ω => (h n ω : H)))
    (_hv : ∀ n, Measurable (fun ω => (v n ω : H)))
    (hHolder : ∀ n, op.CotasHolder34 (Hm n) U Γ α Sf Sg) :
    let Pn := fun ω n => op.problemaLogDimensional μr μb (hmr n) (hmb n) D sr sb dr.C db.C
      dr.c db.c κ lr lb α hD dr.C_pos dr.c_pos db.c_pos (by linarith) hlr hlb
      (fun i => Zr.Z i ω) (fun i => Zb.Z i ω)
    (∀ᵐ ω ∂P, ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n in atTop,
      (Pn ω n).EsMinimizadorGlobal (Hm n) (h n ω : H) ∧
      (Pn ω n).ComparadorExacto (Hm n) (v n ω : H) ∧
      (Pn ω n).regularidadTotal (v n ω : H) ≤ R) →
    ∀ᵐ ω ∂P, (fun n => (Pn ω n).perdidaPoblacional (h n ω : H)) =O[atTop]
      (fun n => (Real.log (mr n : ℝ) / mr n) ^ (2 * α / sr) +
        (Real.log (mb n : ℝ) / mb n) ^ (2 * α / sb)) := by
  intro Pn hvar
  have hcr := dr.c_pos
  have hcb := db.c_pos
  have hκp : 0 < κ := by linarith
  have hcovR := (lema313_cobertura_logaritmica P μr Zr.Z Zr.medible Zr.indep
    Zr.ley U D dr.c sr κ ε₀ ε₀ hD hcr hsr hκ hε hε dr.particiones mr hgr).2
  have hcovB := (lema313_cobertura_logaritmica P μb Zb.Z Zb.medible Zb.indep
    Zb.ley Γ D db.c sb κ ε₀ ε₀ hD hcb hsb hκ hε hε db.particiones mb hgb).2
  have hsuR := muestras_en_soporte_ae P μr Zr.Z U dr.concentrada Zr.medible Zr.ley
  have hsuB := muestras_en_soporte_ae P μb Zb.Z Γ db.concentrada Zb.medible Zb.ley
  filter_upwards [hvar, hcovR, hcovB, hsuR, hsuB] with ω hvarω hcR hcB hsrω hsbω
  obtain ⟨R, hR, hvω⟩ := hvarω
  let Ar := 3 * lr * (D ^ (2 * α) * (κ / dr.c) ^ (2 * α / sr)) * (R + Sf ^ 2)
  let Ab := 3 * lb * (D ^ (2 * α) * (κ / db.c) ^ (2 * α / sb)) * (R + Sg ^ 2)
  apply isBigO_de_cota_eventual _ _ (max Ar Ab)
  filter_upwards [hcR, hcB, hvω] with n hr hb hn
  have hr' := hr.1
  have hb' := hb.1
  let rr := radioCoberturaLog D dr.c sr κ (mr n)
  let rb := radioCoberturaLog D db.c sb κ (mb n)
  let F := factorCoberturaDimensional (mr n) (mb n) dr.C db.C rr rb sr sb
  have hrr : 0 < rr := hr'.2.2.2.2.1
  have hrb : 0 < rb := hb'.2.2.2.2.1
  have hF : 0 < F := factorCoberturaDimensional_pos _ _ _ _ _ _ _ _ (hmr n) dr.C_pos hrr
  let Q := op.problemaDimensional μr μb (hmr n) (hmb n) lr lb α rr rb F hlr hlb hrr hrb
    hF true (fun i => Zr.Z i ω) (fun i => Zb.Z i ω)
  have heq : Pn ω n = Q := problemaLogDimensional_eq op μr μb (hmr n) (hmb n)
    D sr sb dr.C db.C dr.c db.c κ lr lb α hD dr.C_pos hcr hcb hκp hlr hlb _ _
    ⟨hr'.1, hrr⟩ ⟨hb'.1, hrb⟩
  rw [heq] at hn ⊢
  obtain ⟨hmin, hcomp, hreg⟩ := hn
  let a := max (pesoCobertura lr rr α F) (pesoCobertura lb rb α F)
  have ha : 0 ≤ a := Q.regularizadorR_nonneg
  have hJ := (Q.comparacion_con_interpolador (Hm n) _ _ hmin hcomp a rfl rfl).trans
    (mul_le_mul_of_nonneg_left hreg ha)
  rw [← Q.funcional_pesos_iguales _ a rfl rfl] at hJ
  have hJa := mul_le_mul_of_nonneg_left hJ hF.le
  rw [← mul_assoc, producto_peso_igual_dimensional _ _ _ _ _ _ hF] at hJa
  have hsmallMax : max (3 * lr * rr ^ (2 * α)) (3 * lb * rb ^ (2 * α)) ≤
      3 * lr * rr ^ (2 * α) + 3 * lb * rb ^ (2 * α) :=
    max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
  have hJb := hJa.trans (mul_le_mul_of_nonneg_right hsmallMax hR)
  have hbound := cota34_dimensional_bajo_cobertura μr μb U Γ D sr sb ε₀ dr db op (Hm n)
    (hmr n) (hmb n) lr lb α Sf Sg rr rb hlr hlb hα hrr hrb hr'.2.2.2.2.2 hb'.2.2.2.2.2
    true _ _ (hHolder n) ⟨fun i => hsrω i, fun i => hsbω i, hr.2, hb.2⟩ _ (h n ω).2
  change Q.perdidaPoblacional _ ≤ F * Q.funcionalRegularizado _ +
    3 * lr * rr ^ (2 * α) * Sf ^ 2 + 3 * lb * rb ^ (2 * α) * Sg ^ 2 at hbound
  have hsum : Q.perdidaPoblacional (h n ω : H) ≤
      3 * lr * rr ^ (2 * α) * (R + Sf ^ 2) + 3 * lb * rb ^ (2 * α) * (R + Sg ^ 2) := by
    linarith only [hbound, hJb]
  have hnon : 0 ≤ Q.perdidaPoblacional (h n ω : H) := by
    unfold ProblemaPINN.perdidaPoblacional
    exact add_nonneg (mul_nonneg hlr.le (integral_nonneg fun _ => sq_nonneg _))
      (mul_nonneg hlb.le (integral_nonneg fun _ => sq_nonneg _))
  let tr := (Real.log (mr n : ℝ) / mr n) ^ (2 * α / sr)
  let tb := (Real.log (mb n : ℝ) / mb n) ^ (2 * α / sb)
  have htR : 0 ≤ tr := Real.rpow_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) _
  have htB : 0 ≤ tb := Real.rpow_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) _
  refine ⟨hnon, add_nonneg htR htB, ?_⟩
  calc
    _ ≤ 3 * lr * rr ^ (2 * α) * (R + Sf ^ 2) + 3 * lb * rb ^ (2 * α) * (R + Sg ^ 2) := hsum
    _ = Ar * tr + Ab * tb := by
      dsimp [rr, rb, Ar, Ab, tr, tb]
      rw [potencia_radioLog _ _ _ _ _ _ hD.le hcr hκp.le, potencia_radioLog _ _ _ _ _ _ hD.le hcb hκp.le]
      ring
    _ ≤ max Ar Ab * (tr + tb) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) htR)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) htB)

#check proposicion314_evento_dimensional
#check proposicion314_dimensional
#print axioms proposicion314_evento_dimensional
#print axioms proposicion314_dimensional

end TesisPINN
