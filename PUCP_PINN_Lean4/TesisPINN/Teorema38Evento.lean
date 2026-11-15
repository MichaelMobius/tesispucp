import TesisPINN.Teorema34

/-!
# Teorema 3.8, apartado 1 (Shin, Theorem 3.2): tasa (3.26) en el evento de cobertura

`teorema38_dim2` da la forma casi segura y asintótica de (3.26)–(3.28). El
apartado 1 del enunciado de la tesis es, además, una afirmación de muestra
finita: *en el evento de cobertura del Teorema 3.4*, el minimizador global
del funcional con pesos iguales `a_m` de (3.23) verifica
`LossPINN(h_m; λ) = O(m_r^{-α/2})`, con una constante explícita.

* `tasa38_de_cobertura_dim2` es la parte determinista, para una realización
  del evento de cobertura.
* `teorema38_apartado1_dim2` reúne, sobre **un mismo** evento `Ω_m` con la
  probabilidad (3.10), la desigualdad (3.11) del Teorema 3.4 para todo
  candidato y la tasa (3.26) para todo minimizador con comparador exacto.

El comparador `g` y la cota `R` de su regularidad (Hipótesis 3.7) se
cuantifican dentro del evento, de modo que pueden depender de la muestra.
-/

noncomputable section

namespace TesisPINN

open MeasureTheory ProbabilityTheory

/-- Problema PINN con los pesos iguales `a_m` de (3.23) para una realización
`(xr, xb)` de las muestras. Es el mismo objeto que `problemaMuestral` aplicado
a `Operadores38.base` (véase `problemaMuestral_eq_problemaIgual`). -/
def Operadores38.problemaIgual {H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Operadores38 H X Y)
    (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (Cr Cb cr cb lr lb α : ℝ) (hCr : 0 < Cr) (hcr : 0 < cr)
    (hlr : 0 < lr) (hlb : 0 < lb)
    (xr : Fin mr → X) (xb : Fin mb → Y) : ProblemaPINN H X Y mr mb :=
  { D.base μr μb mr mb hmr hmb Cr Cb cr cb lr lb α hCr hcr hlr hlb with
    xr := xr
    xb := xb }

/-- La familia de prefijos que usa `teorema38_dim2` es, índice a índice, el
problema de pesos iguales evaluado en las muestras realizadas. -/
theorem problemaMuestral_eq_problemaIgual
    {Ω H X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Operadores38 H X Y)
    (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (mr mb : ℕ → ℕ) (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (Cr Cb cr cb lr lb α : ℝ) (hCr : 0 < Cr) (hcr : 0 < cr)
    (hlr : 0 < lr) (hlb : 0 < lb)
    (Zr : ℕ → Ω → X) (Zb : ℕ → Ω → Y) (ω : Ω) (n : ℕ) :
    problemaMuestral mr mb
        (fun n => D.base μr μb (mr n) (mb n) (hmr n) (hmb n)
          Cr Cb cr cb lr lb α hCr hcr hlr hlb) Zr Zb ω n =
      D.problemaIgual μr μb (mr n) (mb n) (hmr n) (hmb n)
        Cr Cb cr cb lr lb α hCr hcr hlr hlb
        (fun i => Zr i ω) (fun j => Zb j ω) :=
  rfl

/-- Constante explícita de la tasa (3.26) en dimensión dos; `K` es la constante
de la relación `m_r ≤ K m_b²` y `R` la cota de la regularidad del comparador. -/
def constante38 (lr lb cr cb α K R Sf Sg : ℝ) : ℝ :=
  3 * (lr * (Real.sqrt 2 * cr ^ (-(1 / (2 : ℝ)))) ^ (2 * α) +
       lb * (Real.sqrt 2 * cb ^ (-(1 / (1 : ℝ)))) ^ (2 * α) * K ^ (α / 2)) *
    (R + Sf ^ 2 + Sg ^ 2)

/-- **Parte determinista del apartado 1 del Teorema 3.8.** En una realización
del evento de cobertura del Teorema 3.4, todo minimizador global del funcional
con pesos iguales que admita un comparador exacto de regularidad a lo sumo `R`
verifica `LossPINN(h_m; λ) ≤ C m_r^{-α/2}`. -/
theorem tasa38_de_cobertura_dim2
    {Ω H X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (U : Set X) (Γ : Set Y) (ε₀ : ℝ)
    (dr : DatosMasa38 μr U 2 ε₀) (db : DatosMasa38 μb Γ 1 ε₀)
    (Zr : ℕ → Ω → X) (Zb : ℕ → Ω → Y)
    (D : Operadores38 H X Y) (Hm : Set H)
    (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (lr lb α Sf Sg K : ℝ) (hlr : 0 < lr) (hlb : 0 < lb)
    (hα : 0 < α) (hK : 0 < K)
    (hrel : (mr : ℝ) ≤ K * (mb : ℝ) ^ 2)
    (hradR : radio34 dr.c 2 mr ≤ ε₀) (hradB : radio34 db.c 1 mb ≤ ε₀)
    (hHolder : D.CotasHolder34 Hm U Γ α Sf Sg)
    (ω : Ω) (hω : CoberturaMuestral34 Zr Zb U Γ dr.c db.c mr mb ω)
    (hm g : H) (R : ℝ) (hR : 0 ≤ R)
    (hmin : (D.problemaIgual μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
      dr.C_pos dr.c_pos hlr hlb
      (fun i => Zr i ω) (fun j => Zb j ω)).EsMinimizadorGlobal Hm hm)
    (hg : (D.problemaIgual μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
      dr.C_pos dr.c_pos hlr hlb
      (fun i => Zr i ω) (fun j => Zb j ω)).ComparadorExacto Hm g)
    (hgR : (D.problemaIgual μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
      dr.C_pos dr.c_pos hlr hlb
      (fun i => Zr i ω) (fun j => Zb j ω)).regularidadTotal g ≤ R) :
    (D.problemaIgual μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
        dr.C_pos dr.c_pos hlr hlb
        (fun i => Zr i ω) (fun j => Zb j ω)).perdidaPoblacional hm ≤
      constante38 lr lb dr.c db.c α K R Sf Sg * (mr : ℝ) ^ (-(α / 2)) := by
  obtain ⟨hsuR, hsuB, hcoverR, hcoverB⟩ := hω
  have hεr : 0 < radio34 dr.c 2 mr := radio34_pos dr.c 2 mr dr.c_pos hmr
  have hεb : 0 < radio34 db.c 1 mb := radio34_pos db.c 1 mb db.c_pos hmb
  have hhm : hm ∈ Hm := hmin.1
  have hContL : ContinuousOn (D.L hm) U :=
    continuo_de_cota_holder U _ _ α hα (hHolder.2.2.1 hm hhm).2.2.1
  have hContB : ContinuousOn (D.B hm) Γ :=
    continuo_de_cota_holder Γ _ _ α hα (hHolder.2.2.1 hm hhm).2.2.2
  have hContF : ContinuousOn D.f U :=
    continuo_de_cota_holder U _ Sf α hα hHolder.2.2.2.1
  have hContG : ContinuousOn D.g Γ :=
    continuo_de_cota_holder Γ _ Sg α hα hHolder.2.2.2.2
  let Pω := D.problemaIgual μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
    dr.C_pos dr.c_pos hlr hlb (fun i => Zr i ω) (fun j => Zb j ω)
  change Pω.perdidaPoblacional hm ≤
    constante38 lr lb dr.c db.c α K R Sf Sg * (mr : ℝ) ^ (-(α / 2))
  have hHolderP : CotasHolder Pω Hm U Γ α Sf Sg := hHolder
  have hint : Pω.PoblacionIntegrable hm :=
    poblacionIntegrable_de_holder_acotado Pω Hm U Γ
      dr.acotado db.acotado (soporte_no_vacio μr U dr.concentrada)
      (soporte_no_vacio μb Γ db.concentrada) dr.concentrada db.concentrada
      α Sf Sg hα hHolderP hm hhm
      (aestronglyMeasurable_residuo_sq_de_continuidad μr U dr.medible
        dr.concentrada _ _ hContL hContF)
      (aestronglyMeasurable_residuo_sq_de_continuidad μb Γ db.medible
        db.concentrada _ _ hContB hContG)
  have hineq := perdidaPoblacional_minimizador_bajo_cobertura Pω Hm U Γ
    dr.medible db.medible dr.concentrada db.concentrada
    α (radio34 dr.c 2 mr) (radio34 db.c 1 mb) ε₀ ε₀ dr.C db.C Sf Sg R
    hα hεr hεb hradR hradB dr.C_pos db.C_pos hsuR hsuB hcoverR hcoverB
    dr.superior db.superior hHolderP hm g hmin hg hgR hint rfl rfl
  have hineq' : Pω.perdidaPoblacional hm ≤
      factorCoberturaCuadrado mr mb dr.C db.C
        (Real.sqrt 2 * escalaAuxiliarRaiz dr.c 2 mr)
        (Real.sqrt 2 * escalaAuxiliarRaiz db.c 1 mb) *
      (pesoRegularizacionIgual lr lb
        (Real.sqrt 2 * escalaAuxiliarRaiz dr.c 2 mr)
        (Real.sqrt 2 * escalaAuxiliarRaiz db.c 1 mb) α
        (factorCoberturaCuadrado mr mb dr.C db.C
          (Real.sqrt 2 * escalaAuxiliarRaiz dr.c 2 mr)
          (Real.sqrt 2 * escalaAuxiliarRaiz db.c 1 mb)) * R) +
      3 * lr * (Real.sqrt 2 * escalaAuxiliarRaiz dr.c 2 mr) ^ (2 * α) * Sf ^ 2 +
      3 * lb * (Real.sqrt 2 * escalaAuxiliarRaiz db.c 1 mb) ^ (2 * α) * Sg ^ 2 :=
    hineq
  exact tasa_de_cota_cobertura mr mb dr.C db.C dr.c db.c lr lb α Sf Sg R K
    (Pω.perdidaPoblacional hm) hmr hmb dr.C_pos dr.c_pos db.c_pos hlr hlb hα
    hR hK hrel hineq'

/-- **Teorema 3.8, apartado 1 (Shin, Theorem 3.2), dimensión dos, junto con el
Teorema 3.4.** Bajo la Hipótesis 3.2, con `m_r ≤ K m_b²` y radios (3.5) en
`(0, ε₀]`, existe un evento medible `Ω_m` de probabilidad al menos
`1 - √m_r (1 - 1/√m_r)^{m_r} - √m_b (1 - 1/√m_b)^{m_b}` sobre el cual:

1. todo candidato admisible verifica la desigualdad (3.11) del Teorema 3.4;
2. todo minimizador global `h_m` del funcional con pesos iguales `a_m` que
   admita un comparador exacto `g` de regularidad a lo sumo `R` (Hipótesis 3.7)
   verifica `LossPINN(h_m; λ) ≤ C(R) m_r^{-α/2}`, que es (3.26).

Ambas conclusiones se obtienen en el mismo evento. -/
theorem teorema38_apartado1_dim2
    {Ω H X Y : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb]
    (U : Set X) (Γ : Set Y) (ε₀ : ℝ)
    (dr : DatosMasa38 μr U 2 ε₀) (db : DatosMasa38 μb Γ 1 ε₀)
    (sr : Muestreo38 P μr) (sb : Muestreo38 P μb)
    (D : Operadores38 H X Y) (Hm : Set H)
    (mr mb : ℕ) (hmr : 0 < mr) (hmb : 0 < mb)
    (lr lb α Sf Sg K : ℝ) (hlr : 0 < lr) (hlb : 0 < lb)
    (hα : 0 < α) (hK : 0 < K)
    (hrel : (mr : ℝ) ≤ K * (mb : ℝ) ^ 2)
    (hradR : radio34 dr.c 2 mr ≤ ε₀) (hradB : radio34 db.c 1 mb ≤ ε₀)
    (hHolder : D.CotasHolder34 Hm U Γ α Sf Sg) :
    ∃ Ωm : Set Ω, MeasurableSet Ωm ∧
      1 - Real.sqrt (mr : ℝ) * (1 - 1 / Real.sqrt (mr : ℝ)) ^ mr
        - Real.sqrt (mb : ℝ) * (1 - 1 / Real.sqrt (mb : ℝ)) ^ mb ≤ P.real Ωm ∧
      ∀ ω ∈ Ωm,
        (∀ h ∈ Hm,
          (D.problema34 μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
              dr.C_pos dr.c_pos db.c_pos hlr hlb
              (fun i => sr.Z i ω) (fun j => sb.Z j ω)).perdidaPoblacional h ≤
            factor34 mr mb dr.C db.C dr.c db.c *
              (D.problema34 μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
                dr.C_pos dr.c_pos db.c_pos hlr hlb
                (fun i => sr.Z i ω) (fun j => sb.Z j ω)).funcionalRegularizado h +
            constante34 lr lb dr.c db.c α Sf Sg *
              ((mr : ℝ) ^ (-(α / 2)) + (mb : ℝ) ^ (-α))) ∧
        (∀ hm g : H, ∀ R : ℝ, 0 ≤ R →
          (D.problemaIgual μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
            dr.C_pos dr.c_pos hlr hlb
            (fun i => sr.Z i ω) (fun j => sb.Z j ω)).EsMinimizadorGlobal Hm hm →
          (D.problemaIgual μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
            dr.C_pos dr.c_pos hlr hlb
            (fun i => sr.Z i ω) (fun j => sb.Z j ω)).ComparadorExacto Hm g →
          (D.problemaIgual μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
            dr.C_pos dr.c_pos hlr hlb
            (fun i => sr.Z i ω) (fun j => sb.Z j ω)).regularidadTotal g ≤ R →
          (D.problemaIgual μr μb mr mb hmr hmb dr.C db.C dr.c db.c lr lb α
              dr.C_pos dr.c_pos hlr hlb
              (fun i => sr.Z i ω) (fun j => sb.Z j ω)).perdidaPoblacional hm ≤
            constante38 lr lb dr.c db.c α K R Sf Sg * (mr : ℝ) ^ (-(α / 2))) := by
  obtain ⟨Ωm, hmeas, hprob, hcob⟩ := evento_cobertura34_dim2 P μr μb U Γ ε₀
    dr db sr sb mr mb hmr hmb hradR hradB
  refine ⟨Ωm, hmeas, hprob, fun ω hω => ⟨fun h hh => ?_, fun hm g R hR hmin hg hgR => ?_⟩⟩
  · exact cota34_de_cobertura_dim2 μr μb U Γ ε₀ dr db sr.Z sb.Z D Hm mr mb
      hmr hmb lr lb α Sf Sg hlr hlb hα hradR hradB hHolder ω (hcob ω hω) h hh
  · exact tasa38_de_cobertura_dim2 μr μb U Γ ε₀ dr db sr.Z sb.Z D Hm mr mb
      hmr hmb lr lb α Sf Sg K hlr hlb hα hK hrel hradR hradB hHolder ω
      (hcob ω hω) hm g R hR hmin hg hgR

#print axioms TesisPINN.problemaMuestral_eq_problemaIgual
#print axioms TesisPINN.tasa38_de_cobertura_dim2
#print axioms TesisPINN.teorema38_apartado1_dim2

end TesisPINN
