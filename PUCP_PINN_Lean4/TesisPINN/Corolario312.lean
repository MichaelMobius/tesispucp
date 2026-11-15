import TesisPINN.Proposicion310
import TesisPINN.Proposicion327
import TesisPINN.ProblemaInterior

/-! Criterio fuerte de C3.12: las normas de los espacios de llegada controlan
la evaluación puntual y la seminorma Hölder exacta sobre el soporte. -/

noncomputable section

namespace TesisPINN

open Set Filter MeasureTheory Asymptotics
open scoped Topology

/-- Interfaz de un espacio normado de funciones Hölder reales. La evaluación
es lineal y la norma domina las dos componentes de la norma Hölder usual. -/
structure RealizacionHolder312 (F X : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace X] (U : Set X) (α : ℝ) where
  eval : F →ₗ[ℝ] (X → ℝ)
  valores : ∀ w x, x ∈ U → |eval w x| ≤ ‖w‖
  holder : ∀ w, ‖w‖ ∈ constantesHolderInterior U α (eval w)

namespace RealizacionHolder312

variable {F H X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [PseudoMetricSpace X] {U : Set X} {α : ℝ}

theorem seminorma_le (E : RealizacionHolder312 F X U α) (w : F) :
    0 ≤ seminormaInterior U α (E.eval w) ∧ seminormaInterior U α (E.eval w) ≤ ‖w‖ :=
  ⟨seminormaInterior_nonneg _ _ _ ⟨_, E.holder w⟩,
    csInf_le ⟨0, fun _ h => h.1⟩ (E.holder w)⟩

theorem cota_residuo (E : RealizacionHolder312 F X U α) (L : H →L[ℝ] F)
    (v u : H) (f : X → ℝ) (hf : EqOn (E.eval (L u)) f U)
    (t : ℝ) (hv : ‖v - u‖ ≤ t) :
    (∀ x ∈ U, |E.eval (L v) x - f x| ≤ ‖L‖ * t) ∧
    ‖L‖ * t ∈ constantesHolderInterior U α (E.eval (L v) - f) ∧
    (0 ≤ seminormaInterior U α (E.eval (L v)) ∧
      seminormaInterior U α (E.eval (L v)) ≤ ‖L u‖ + ‖L‖ * t) := by
  have hdiff : ∀ x ∈ U, E.eval (L (v - u)) x = E.eval (L v) x - f x := by
    intro x hx
    simp only [map_sub, Pi.sub_apply, hf hx]
  have hnorm : ‖L (v - u)‖ ≤ ‖L‖ * t :=
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
  refine ⟨fun x hx => ?_, ⟨(norm_nonneg _).trans hnorm, ?_⟩,
    (E.seminorma_le (L v)).1, (E.seminorma_le (L v)).2.trans ?_⟩
  · rw [← hdiff x hx]
    exact (E.valores _ _ hx).trans hnorm
  · intro x hx y hy
    simp only [Pi.sub_apply]
    rw [← hdiff x hx, ← hdiff y hy]
    exact ((E.holder (L (v - u))).2 x hx y hy).trans
      (mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg dist_nonneg _))
  · have he : L v = L u + L (v - u) := by
      rw [map_sub]
      abel
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add_right hnorm _)

end RealizacionHolder312

private theorem promedio_cuadrados312 {m : ℕ} (hm : 0 < m)
    (l M a : ℝ) (hl : 0 ≤ l) (ha : 0 ≤ a) (r : Fin m → ℝ)
    (hr : ∀ i, |r i| ≤ M * Real.sqrt a) :
    l / (m : ℝ) * ∑ i, (r i) ^ 2 ≤ l * M ^ 2 * a := by
  have hm' : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  calc
    _ ≤ l / (m : ℝ) * ∑ _i : Fin m, (M * Real.sqrt a) ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => by
        rw [← sq_abs (r i)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hr i) _) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_pow, Real.sq_sqrt ha]
      field_simp

section General

variable {H F G X Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [PseudoMetricSpace X] [PseudoMetricSpace Y] {U : Set X} {Γ : Set Y} {α : ℝ}

/-- Los comparadores de (3.56) satisfacen (3.36)–(3.37). El cuantificador
sobre tamaños y puntos mantiene las constantes independientes del muestreo. -/
theorem corolario312
    (Er : RealizacionHolder312 F X U α) (Eb : RealizacionHolder312 G Y Γ α)
    (L : H →L[ℝ] F) (B : H →L[ℝ] G) (u : H) (f : X → ℝ) (g : Y → ℝ)
    (hf : EqOn (Er.eval (L u)) f U) (hg : EqOn (Eb.eval (B u)) g Γ)
    (lr lb : ℝ) (hlr : 0 ≤ lr) (hlb : 0 ≤ lb)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hlim : Tendsto a atTop (𝓝 0))
    (v : ℕ → H) (A : ℝ) (hA : 0 ≤ A) (hv : ∀ n, ‖v n - u‖ ≤ A * Real.sqrt (a n)) :
    ∃ K R : ℝ, 0 ≤ K ∧ 0 ≤ R ∧ ∀ n, ∀ {mr mb : ℕ}, 0 < mr → 0 < mb →
      ∀ (xr : Fin mr → X) (xb : Fin mb → Y), (∀ i, xr i ∈ U) → (∀ i, xb i ∈ Γ) →
      (lr / (mr : ℝ) * ∑ i, (Er.eval (L (v n)) (xr i) - f (xr i)) ^ 2) +
        (lb / (mb : ℝ) * ∑ i, (Eb.eval (B (v n)) (xb i) - g (xb i)) ^ 2) ≤ K * a n ∧
      seminormaInterior U α (Er.eval (L (v n))) ^ 2 +
        seminormaInterior Γ α (Eb.eval (B (v n))) ^ 2 ≤ R := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto a hlim).bddAbove
  have haM (n : ℕ) : a n ≤ M := hM (mem_range_self n)
  let Cr := ‖L u‖ + ‖L‖ * (A * Real.sqrt M)
  let Cb := ‖B u‖ + ‖B‖ * (A * Real.sqrt M)
  let K := lr * (‖L‖ * A) ^ 2 + lb * (‖B‖ * A) ^ 2
  refine ⟨K, Cr ^ 2 + Cb ^ 2, by dsimp [K]; positivity, by positivity, ?_⟩
  intro n mr mb hmr hmb xr xb hxr hxb
  have hr := Er.cota_residuo L (v n) u f hf _ (hv n)
  have hb := Eb.cota_residuo B (v n) u g hg _ (hv n)
  have hmeanR := promedio_cuadrados312 hmr lr (‖L‖ * A) (a n) hlr (ha n)
    (fun i => Er.eval (L (v n)) (xr i) - f (xr i))
    (fun i => by simpa only [mul_assoc] using hr.1 (xr i) (hxr i))
  have hmeanB := promedio_cuadrados312 hmb lb (‖B‖ * A) (a n) hlb (ha n)
    (fun i => Eb.eval (B (v n)) (xb i) - g (xb i))
    (fun i => by simpa only [mul_assoc] using hb.1 (xb i) (hxb i))
  have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (haM n)) hA
  refine ⟨(add_le_add hmeanR hmeanB).trans_eq (by dsimp [K]; ring), add_le_add ?_ ?_⟩
  · exact pow_le_pow_left₀ hr.2.2.1
      (hr.2.2.2.trans (add_le_add_right (mul_le_mul_of_nonneg_left hs (norm_nonneg L)) _)) _
  · exact pow_le_pow_left₀ hb.2.2.1
      (hb.2.2.2.trans (add_le_add_right (mul_le_mul_of_nonneg_left hs (norm_nonneg B)) _)) _

/-- Los operadores y las seminormas exactas que recibe P3.10. Los datos
prescritos se identifican con la solución exacta mediante igualdades locales. -/
def operadores312
    (Er : RealizacionHolder312 F X U α) (Eb : RealizacionHolder312 G Y Γ α)
    (L : H →L[ℝ] F) (B : H →L[ℝ] G) (f : X → ℝ) (g : Y → ℝ) :
    Operadores38 H X Y where
  L v := Er.eval (L v)
  B v := Eb.eval (B v)
  f := f
  g := g
  seminormaL v := seminormaInterior U α (Er.eval (L v))
  seminormaB v := seminormaInterior Γ α (Eb.eval (B v))

/-- C3.12 descarga las hipótesis Hölder, de comparación y de tolerancias
de P3.10 para los problemas muestrales que usan estos mismos operadores. -/
theorem corolario312_premisas310
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure Ω) (μr : Measure X) [IsProbabilityMeasure μr]
    (μb : Measure Y) [IsProbabilityMeasure μb] (ε₀ : ℝ)
    (dr : DatosMasa38 μr U 2 ε₀) (db : DatosMasa38 μb Γ 1 ε₀)
    (sr : Muestreo38 P μr) (sb : Muestreo38 P μb)
    (Er : RealizacionHolder312 F X U α) (Eb : RealizacionHolder312 G Y Γ α)
    (L : H →L[ℝ] F) (B : H →L[ℝ] G) (u : H) (f : X → ℝ) (g : Y → ℝ)
    (hf : EqOn (Er.eval (L u)) f U) (hg : EqOn (Eb.eval (B u)) g Γ)
    (lr lb : ℝ) (hlr : 0 < lr) (hlb : 0 < lb) (hα : 0 < α)
    (mr mb : ℕ → ℕ) (hmr : ∀ n, 0 < mr n) (hmb : ∀ n, 0 < mb n)
    (Hm : ℕ → Set H) (h : ∀ n, Ω → Hm n) (v : ∀ n, Hm n)
    (A : ℝ) (hA : 0 ≤ A) (δ : ℕ → ℝ) (Kδ : ℝ) :
    let D := operadores312 Er Eb L B f g
    let base := fun n => D.base μr μb (mr n) (mb n) (hmr n) (hmb n)
      dr.C db.C dr.c db.c lr lb α dr.C_pos dr.c_pos hlr hlb
    let Pn := problemaMuestral mr mb base sr.Z sb.Z
    let a := fun n => (base n).regularizadorR
    Tendsto a atTop (𝓝 0) →
    (∀ n, ‖(v n : H) - u‖ ≤ A * Real.sqrt (a n)) →
    (∀ᵐ ω ∂P, ∀ᶠ n in atTop, (Pn ω n).EsMinimizadorAproximado (Hm n) (h n ω : H) (δ n)) →
    (∀ᶠ n in atTop, δ n ≤ Kδ * a n) →
    ∃ K R, 0 ≤ K ∧ 0 ≤ R ∧
      (∀ n, CotasHolder (base n) (Hm n) U Γ α ‖L u‖ ‖B u‖) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        (Pn ω n).perdidaEmpirica (v n : H) ≤ K * a n ∧
        (Pn ω n).regularidadTotal (v n : H) ≤ R ∧
        (Pn ω n).EsMinimizadorAproximado (Hm n) (h n ω : H) (δ n)) ∧
      (∀ᶠ n in atTop, K * a n + δ n ≤ (K + Kδ) * a n) := by
  intro D base Pn a ha hv hmin hδ
  obtain ⟨K, R, hK, hR, hb⟩ := corolario312 Er Eb L B u f g hf hg lr lb hlr.le hlb.le
    a (fun n => (base n).regularizadorR_nonneg) ha (fun n => v n) A hA hv
  refine ⟨K, R, hK, hR, ?_, ?_, hδ.mono fun n hn => ?_⟩
  · intro n
    refine ⟨norm_nonneg _, norm_nonneg _, fun w _ => ?_, ?_, ?_⟩
    · exact ⟨(Er.seminorma_le (L w)).1, (Eb.seminorma_le (B w)).1,
        seminormaInterior_cota U α _ ⟨_, Er.holder (L w)⟩ hα,
        seminormaInterior_cota Γ α _ ⟨_, Eb.holder (B w)⟩ hα⟩
    · intro x hx y hy
      change |f x - f y| ≤ ‖L u‖ * dist x y ^ α
      rw [← hf hx, ← hf hy]
      exact (Er.holder (L u)).2 x hx y hy
    · intro x hx y hy
      change |g x - g y| ≤ ‖B u‖ * dist x y ^ α
      rw [← hg hx, ← hg hy]
      exact (Eb.holder (B u)).2 x hx y hy
  · have hr := muestras_en_soporte_ae P μr sr.Z U dr.concentrada sr.medible sr.ley
    have hb' := muestras_en_soporte_ae P μb sb.Z Γ db.concentrada sb.medible sb.ley
    filter_upwards [hmin, hr, hb'] with ω hω hsr hsb
    filter_upwards [hω] with n hn
    obtain ⟨hE, hR⟩ := hb n (hmr n) (hmb n) (Pn ω n).xr (Pn ω n).xb
      (fun i => hsr i) (fun i => hsb i)
    exact ⟨hE, hR, hn⟩
  · rw [add_mul]
    exact add_le_add_right hn _

end General

/-- Instancia interior de (3.36)–(3.37) para Taylor. Vale para los dos pesos
y conserva la pertenencia a la clase y Dirichlet fuerte. -/
theorem corolario312_taylor :
    ∃ K R : ℝ, 0 ≤ K ∧ 0 ≤ R ∧ ∀ m, 3 ≤ m →
      comparadorTaylor327 m ∈ range (candidato326 (4 * m - 1)) ∧
      EqOn (comparadorTaylor327 m) 0 (frontier cuadrado) ∧
      seminormaInterior cuadrado (1 / 2) (laplacianoClásico (comparadorTaylor327 m)) ^ 2 ≤ R ∧
      ∀ s : Fin m → Plano, (∀ i, s i ∈ cuadrado) →
        let E := perdidaEmpiricaInterior s (laplacianoClásico (comparadorTaylor327 m)) fuenteManufacturada
        E ≤ K * pesoRaizInterior (1 / 2) m ∧ E ≤ K * pesoLogInterior m := by
  obtain ⟨K, hK, hEmp⟩ := comparadorTaylor327_tolerancia_empirica
  obtain ⟨_, S, _, _, hS⟩ := comparadorTaylor327_cotas_Poisson
  obtain ⟨_, _, _, _, hclass⟩ := proposicion327
  refine ⟨K, S ^ 2, hK, sq_nonneg _, fun m hm => ?_⟩
  obtain ⟨_, hc, htr, _⟩ := hclass m hm
  obtain ⟨_, _, hHolder, hsemi⟩ := hS m (by omega)
  exact ⟨hc, htr, pow_le_pow_left₀ (seminormaInterior_nonneg _ _ _ hHolder) hsemi 2, hEmp m hm⟩

#check corolario312
#check corolario312_premisas310
#check corolario312_taylor
#print axioms corolario312
#print axioms corolario312_premisas310
#print axioms corolario312_taylor

end TesisPINN
