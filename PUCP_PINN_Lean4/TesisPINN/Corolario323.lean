import TesisPINN.PoincareEspectralCuadrado
import TesisPINN.Proposicion315
import TesisPINN.TrazaCuadrado
import TesisPINN.NucleoTrazaCuadrado

/-! Cotas simultáneas de Poisson y transferencia de la tasa de pérdida de P3.15. -/

noncomputable section

namespace TesisPINN

open MeasureTheory Filter Set Asymptotics EllipticPdes EllipticPdes.H1Graph
open scoped Topology Asymptotics Distributions RealInnerProductSpace

def constanteH1323 : ℝ := (Real.sqrt 2 / Real.pi) * Real.sqrt (1 + 2 / Real.pi ^ 2)

def constanteSimultanea323 : ℝ := constanteH1323 + 26404 / 100000

def normaEsencial323 (e : H1Graph (volume : Measure Plano) cuadrado) : ℝ :=
  (eLpNormEssSup (fnL e) volumenPoisson).toReal

/-- (3.81) y (3.82) para un error en el grafo con condición de Dirichlet. -/
theorem cotas_simultaneas323
    (e : H01 (volume : Measure Plano) cuadrado) (r : Lp ℝ 2 volumenPoisson)
    (hr : HasDistributionalLaplacian cuadradoOpens volume e r) :
    ‖(e : H1Graph volume cuadrado)‖ ≤ constanteH1323 * ‖r‖ ∧
    normaEsencial323 e ≤ (26404 / 100000 : ℝ) * ‖r‖ ∧
    ‖(e : H1Graph volume cuadrado)‖ + normaEsencial323 e ≤ constanteSimultanea323 * ‖r‖ ∧
    ∃ g : Plano → ℝ, Continuous g ∧
      (⇑(fnL (e : H1Graph volume cuadrado)) =ᵐ[volumenPoisson] g) ∧
      EqOn g 0 (frontier cuadrado) ∧ supResiduo (closure cuadrado) g = normaEsencial323 e := by
  have hH := energia_cuadrado_poincare_optima e r hr
  obtain ⟨g, hc, hae, hfr, hsup, _, hnum, _, _⟩ := proposicion322_espectral_completa e r hr
  have hN : normaEsencial323 e ≤ (26404 / 100000 : ℝ) * ‖r‖ := by
    rw [normaEsencial323, ← hsup]
    exact hnum
  refine ⟨hH, hN, ?_, g, hc, hae, hfr, hsup⟩
  rw [constanteSimultanea323, add_mul]
  exact add_le_add hH hN

/-- Un representante continuo dado coincide con el espectral hasta la frontera. -/
theorem representante323_coincide
    (e : H1Graph (volume : Measure Plano) cuadrado) {h u g : Plano → ℝ}
    (hh : ContinuousOn h (closure cuadrado)) (hu : ContinuousOn u (closure cuadrado))
    (hg : ContinuousOn g (closure cuadrado))
    (he : ⇑(fnL e) =ᵐ[volumenPoisson] (h - u))
    (hae : ⇑(fnL e) =ᵐ[volumenPoisson] g) :
    EqOn g (h - u) (closure cuadrado) := by
  have heq := Measure.eqOn_open_of_ae_eq (hae.symm.trans he) cuadrado_abierto
    (hg.mono subset_closure) ((hh.sub hu).mono subset_closure)
  exact heq.of_subset_closure hg (hh.sub hu) subset_closure subset_rfl

/-- El signo de (3.81)–(3.82) para dos grafos con laplacianos
distribucionales representados en L². -/
theorem laplaciano_diferencia323
    (h u : H1Graph (volume : Measure Plano) cuadrado)
    (hh : h - u ∈ H01 (volume : Measure Plano) cuadrado)
    (d f : Lp ℝ 2 volumenPoisson)
    (hΔ : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL h) volume ⊤) =
      Distribution.ofFun cuadradoOpens d volume ⊤)
    (uΔ : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens f volume ⊤) :
    HasDistributionalLaplacian cuadradoOpens volume ⟨h - u, hh⟩ (d - f) := by
  have hsub (a b : Lp ℝ 2 volumenPoisson) :
      Distribution.ofFun cuadradoOpens (a - b) volume ⊤ =
        Distribution.ofFun cuadradoOpens a volume ⊤ -
          Distribution.ofFun cuadradoOpens b volume ⊤ := by
    rw [Distribution.ofFun_congr_ae (Lp.coeFn_sub a b)]
    change Distribution.ofFun cuadradoOpens ((a : Plano → ℝ) + -(b : Plano → ℝ)) volume ⊤ = _
    rw [Distribution.ofFun_add (locallyIntegrableOn_lp a) (locallyIntegrableOn_lp b).neg,
      Distribution.ofFun_neg, sub_eq_add_neg]
  unfold HasDistributionalLaplacian
  change laplacianoDistribucional cuadradoOpens
    (Distribution.ofFun cuadradoOpens (fnL (h - u)) volume ⊤) = _
  rw [map_sub, hsub, map_sub, hΔ, uΔ]
  exact (hsub d f).symm

theorem cotas_simultaneas323_frontera_puntual
    (h u : H1Graph (volume : Measure Plano) cuadrado)
    (hh : h ∈ W12 volume cuadrado) (hu : u ∈ W12 volume cuadrado)
    {hc uc : Plano → ℝ}
    (hcont : ContinuousOn hc (closure cuadrado)) (ucont : ContinuousOn uc (closure cuadrado))
    (hrep : ⇑(fnL h) =ᵐ[volumenPoisson] hc) (urep : ⇑(fnL u) =ᵐ[volumenPoisson] uc)
    (hfr : EqOn hc uc (frontier cuadrado)) (d f : Lp ℝ 2 volumenPoisson)
    (hΔ : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL h) volume ⊤) =
      Distribution.ofFun cuadradoOpens d volume ⊤)
    (uΔ : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens f volume ⊤) :
    ‖h - u‖ ≤ constanteH1323 * ‖d - f‖ ∧
    supResiduo (closure cuadrado) (hc - uc) = normaEsencial323 (h - u) ∧
    supResiduo (closure cuadrado) (hc - uc) ≤ (26404 / 100000 : ℝ) * ‖d - f‖ ∧
    ‖h - u‖ + supResiduo (closure cuadrado) (hc - uc) ≤ constanteSimultanea323 * ‖d - f‖ := by
  have he := frontera_puntual_igual_implica_error_H01 h u hh hu hcont ucont hrep urep hfr
  have hd := laplaciano_diferencia323 h u he d f hΔ uΔ
  obtain ⟨hH, hInf, hsum, g, hg, hgae, _, hsup⟩ := cotas_simultaneas323 _ _ hd
  have hdiff : ⇑(fnL (h - u)) =ᵐ[volumenPoisson] (hc - uc) := by
    rw [map_sub]
    exact (Lp.coeFn_sub _ _).trans (hrep.sub urep)
  have hsame := representante323_coincide (h - u) hcont ucont hg.continuousOn hdiff hgae
  have heq : supResiduo (closure cuadrado) (hc - uc) = normaEsencial323 (h - u) :=
    (supResiduo_congr hsame.symm).trans hsup
  exact ⟨hH, heq, heq.trans_le hInf, by rw [heq]; exact hsum⟩

theorem norma_residuo323_de_perdida
    (G q : CandidatoPoisson) (f : Plano → ℝ) (hf : MemLp f 2 volumenPoisson) :
    ‖residuoLevantado G q (datoPoissonLp f hf)‖ =
      2 * Real.sqrt (perdidaPoissonInterior (laplacianoClásico (aproximacionLevantada G q)) f) := by
  rw [perdidaPoissonInterior_eq_norma_residuo G q f hf, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (norm_nonneg _),
    show Real.sqrt (1 / 4 : ℝ) = 1 / 2 by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  ring

/-- Normalización para cualquier operador escalar cuyo residuo tiene representante en L². -/
theorem norma_residuo323_de_perdida_escalar
    (L f : Plano → ℝ) (r : Lp ℝ 2 volumenPoisson)
    (hr : ⇑r =ᵐ[volumenPoisson] (L - f)) :
    ‖r‖ = 2 * Real.sqrt (perdidaPoissonInterior L f) := by
  have heq : perdidaPoissonInterior L f = (1 / 4) * ‖r‖ ^ 2 := by
    rw [perdidaPoissonInterior_eq, ← real_inner_self_eq_norm_sq r, MeasureTheory.L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards [hr] with x hx
    change r x = L x - f x at hx
    simp [hx, pow_two, RCLike.inner_apply]
  rw [heq, Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _),
    show Real.sqrt (1 / 4 : ℝ) = 1 / 2 by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  ring

private theorem tasa_raiz323 (E : ℕ → ℝ) (hE : ∀ m, 0 ≤ E m)
    (h : E =O[atTop] escalaPerdida315) :
    (fun m => Real.sqrt (E m)) =O[atTop] escalaEnergia315 := by
  obtain ⟨C, hC, hbound⟩ := isBigO_iff'.mp h
  refine isBigO_de_cota_eventual _ _ (Real.sqrt C) ?_
  filter_upwards [hbound] with m hm
  have ht : 0 ≤ escalaPerdida315 m := Real.sqrt_nonneg _
  have he : E m ≤ C * escalaPerdida315 m := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hE m), abs_of_nonneg ht] using hm
  refine ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_⟩
  exact (Real.sqrt_le_sqrt he).trans_eq (Real.sqrt_mul hC.le _)

/-- Transferencia trayectoria por trayectoria, con las dos normas y el factor
dos de la normalización de la ley uniforme. -/
theorem transferencia_simultanea323 (e : ℕ → H01 (volume : Measure Plano) cuadrado)
    (r : ℕ → Lp ℝ 2 volumenPoisson) (E : ℕ → ℝ)
    (hr : ∀ m, HasDistributionalLaplacian cuadradoOpens volume (e m) (r m))
    (hE : ∀ m, 0 ≤ E m) (hres : ∀ m, ‖r m‖ = 2 * Real.sqrt (E m))
    (hRate : E =O[atTop] escalaPerdida315) :
    (fun m => ‖(e m : H1Graph volume cuadrado)‖ + normaEsencial323 (e m)) =O[atTop]
      (fun m : ℕ => (Real.log (m : ℝ) / m) ^ (1 / 4 : ℝ)) ∧
    Tendsto (fun m => ‖(e m : H1Graph volume cuadrado)‖) atTop (𝓝 0) ∧
    Tendsto (fun m => normaEsencial323 (e m)) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun m => ‖(e m : H1Graph volume cuadrado)‖
  let b : ℕ → ℝ := fun m => normaEsencial323 (e m)
  have hb (m : ℕ) : 0 ≤ b m := ENNReal.toReal_nonneg
  have ha (m : ℕ) : 0 ≤ a m := norm_nonneg _
  obtain ⟨C, hC, hbound⟩ := isBigO_iff'.mp (tasa_raiz323 E hE hRate)
  let K := constanteSimultanea323 * 2 * C
  have hK : 0 ≤ constanteSimultanea323 := by
    unfold constanteSimultanea323 constanteH1323
    positivity
  have hsum : ∀ᶠ m in atTop, a m + b m ≤ K * escalaEnergia315 m := by
    filter_upwards [hbound] with m hm
    have hscale : 0 ≤ escalaEnergia315 m := Real.sqrt_nonneg _
    have hs : Real.sqrt (E m) ≤ C * escalaEnergia315 m := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (E m)),
        abs_of_nonneg hscale] using hm
    calc
      a m + b m ≤ constanteSimultanea323 * ‖r m‖ := (cotas_simultaneas323 _ _ (hr m)).2.2.1
      _ = (constanteSimultanea323 * 2) * Real.sqrt (E m) := by rw [hres, mul_assoc]
      _ ≤ K * escalaEnergia315 m := by
        rw [show K * escalaEnergia315 m =
          (constanteSimultanea323 * 2) * (C * escalaEnergia315 m) by simp [K, mul_assoc]]
        exact mul_le_mul_of_nonneg_left hs (by positivity)
  have ht : Tendsto (fun m => K * escalaEnergia315 m) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul escalaEnergia315_tendsto
  constructor
  · simp_rw [← escalaEnergia315_eq]
    exact isBigO_de_cota_eventual _ _ K
      (hsum.mono fun m hm => ⟨add_nonneg (ha m) (hb m), Real.sqrt_nonneg _, hm⟩)
  · exact ⟨squeeze_zero' (Eventually.of_forall ha)
        (hsum.mono fun m hm => (le_add_of_nonneg_right (hb m)).trans hm) ht,
      squeeze_zero' (Eventually.of_forall hb)
        (hsum.mono fun m hm => (le_add_of_nonneg_left (ha m)).trans hm) ht⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Instancia escalar de (3.83) para errores de Dirichlet ya representados
en el grafo. El operador de pérdida se identifica con el residuo en L². -/
theorem corolario323_escalar
    {H : Type*} [MeasurableSpace H] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Muestreo38 P medidaUniformeCuadrado) (L : H → Plano → ℝ) (f : Plano → ℝ)
    (Hm : ℕ → Set H) (hf : EsHolderInterior cuadrado (1 / 2) f)
    (hHolder : ∀ m w, w ∈ Hm m → EsHolderInterior cuadrado (1 / 2) (L w))
    (sel : Selecciones315 P Z L f Hm)
    (e : H → H01 (volume : Measure Plano) cuadrado) (r : H → Lp ℝ 2 volumenPoisson)
    (hΔ : ∀ w, HasDistributionalLaplacian cuadradoOpens volume (e w) (r w))
    (hr : ∀ w, ⇑(r w) =ᵐ[volumenPoisson] (L w - f)) :
    ∀ᵐ ω ∂P,
      let w := fun m => sel.h m (prefijoPoisson P Z m ω)
      (fun m => ‖(e (w m) : H1Graph volume cuadrado)‖ + normaEsencial323 (e (w m))) =O[atTop]
        (fun m : ℕ => (Real.log (m : ℝ) / m) ^ (1 / 4 : ℝ)) ∧
      Tendsto (fun m => ‖(e (w m) : H1Graph volume cuadrado)‖) atTop (𝓝 0) ∧
      Tendsto (fun m => normaEsencial323 (e (w m))) atTop (𝓝 0) := by
  obtain ⟨_, _, hrate⟩ := proposicion315_perdida P Z L f Hm hf hHolder
  filter_upwards [hrate sel] with ω hω
  let w := fun m => sel.h m (prefijoPoisson P Z m ω)
  exact transferencia_simultanea323 (fun m => e (w m)) (fun m => r (w m))
    (fun m => perdidaPoissonInterior (L (w m)) f)
    (fun m => hΔ (w m)) (fun _ => perdidaInterior_nonneg _ _ _)
    (fun m => norma_residuo323_de_perdida_escalar _ _ _ (hr (w m))) hω

/-- Instancia con Dirichlet puntual para cualquier familia de candidatos
con representantes continuos en la clausura. -/
theorem corolario323_frontera_puntual
    {H : Type*} [MeasurableSpace H] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Muestreo38 P medidaUniformeCuadrado) (L : H → Plano → ℝ) (f : Plano → ℝ)
    (Hm : ℕ → Set H) (hf : EsHolderInterior cuadrado (1 / 2) f)
    (hHolder : ∀ m w, w ∈ Hm m → EsHolderInterior cuadrado (1 / 2) (L w))
    (sel : Selecciones315 P Z L f Hm)
    (h : H → H1Graph (volume : Measure Plano) cuadrado)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (hh : ∀ w, h w ∈ W12 volume cuadrado) (hu : u ∈ W12 volume cuadrado)
    (hc : H → Plano → ℝ) (uc : Plano → ℝ)
    (hcont : ∀ w, ContinuousOn (hc w) (closure cuadrado))
    (ucont : ContinuousOn uc (closure cuadrado))
    (hrep : ∀ w, ⇑(fnL (h w)) =ᵐ[volumenPoisson] hc w)
    (urep : ⇑(fnL u) =ᵐ[volumenPoisson] uc)
    (hfr : ∀ w, EqOn (hc w) uc (frontier cuadrado))
    (d : H → Lp ℝ 2 volumenPoisson) (F : Lp ℝ 2 volumenPoisson)
    (hd : ∀ w, ⇑(d w) =ᵐ[volumenPoisson] L w) (hF : ⇑F =ᵐ[volumenPoisson] f)
    (hΔ : ∀ w, laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL (h w)) volume ⊤) =
      Distribution.ofFun cuadradoOpens (d w) volume ⊤)
    (uΔ : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens F volume ⊤) :
    ∀ᵐ ω ∂P,
      let w := fun m => sel.h m (prefijoPoisson P Z m ω)
      (fun m => ‖h (w m) - u‖ + supResiduo (closure cuadrado) (hc (w m) - uc)) =O[atTop]
        (fun m : ℕ => (Real.log (m : ℝ) / m) ^ (1 / 4 : ℝ)) ∧
      Tendsto (fun m => ‖h (w m) - u‖) atTop (𝓝 0) ∧
      Tendsto (fun m => supResiduo (closure cuadrado) (hc (w m) - uc)) atTop (𝓝 0) := by
  have h0 (w : H) : h w - u ∈ H01 (volume : Measure Plano) cuadrado :=
    frontera_puntual_igual_implica_error_H01 _ _ (hh w) hu (hcont w) ucont
      (hrep w) urep (hfr w)
  have hnorm (w : H) : supResiduo (closure cuadrado) (hc w - uc) = normaEsencial323 (h w - u) :=
    (cotas_simultaneas323_frontera_puntual _ _ (hh w) hu (hcont w) ucont
      (hrep w) urep (hfr w) (d w) F (hΔ w) uΔ).2.1
  have ht := corolario323_escalar P Z L f Hm hf hHolder sel
    (fun w => ⟨h w - u, h0 w⟩) (fun w => d w - F)
    (fun w => laplaciano_diferencia323 _ _ (h0 w) (d w) F (hΔ w) uΔ)
    (fun w => (Lp.coeFn_sub _ _).trans ((hd w).sub hF))
  filter_upwards [ht] with ω hω
  dsimp only at hω ⊢
  simp_rw [hnorm]
  exact hω

/-- Instancia de (3.83) para la clase levantada. Usa directamente el evento de P3.15. -/
theorem corolario323_poisson_levantado
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Muestreo38 P medidaUniformeCuadrado) [MeasurableSpace CandidatoPoisson]
    (G : CandidatoPoisson) (f : Plano → ℝ) (Hm : ℕ → Set CandidatoPoisson)
    (hf : EsHolderInterior cuadrado (1 / 2) f)
    (sel : Selecciones315 P Z (fun q => laplacianoClásico (aproximacionLevantada G q)) f Hm)
    (u : H1Graph (volume : Measure Plano) cuadrado)
    (hu : u - grafoSuaveCuadrado G ∈ H01 (volume : Measure Plano) cuadrado)
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens (datoPoissonLp f (dato315_memLp f hf)) volume ⊤) :
    ∀ᵐ ω ∂P,
      let e := fun m => grafoLevantado G (sel.h m (prefijoPoisson P Z m ω)) - u
      (fun m => ‖e m‖ + normaEsencial323 (e m)) =O[atTop]
        (fun m : ℕ => (Real.log (m : ℝ) / m) ^ (1 / 4 : ℝ)) ∧
      Tendsto (fun m => ‖e m‖) atTop (𝓝 0) ∧
      Tendsto (fun m => normaEsencial323 (e m)) atTop (𝓝 0) := by
  obtain ⟨_, _, hrate⟩ := proposicion315_perdida P Z
    (fun q => laplacianoClásico (aproximacionLevantada G q)) f Hm hf
    (fun _ q _ => laplacianoLevantado_holder315 G q)
  filter_upwards [hrate sel] with ω hω
  let q := fun m => sel.h m (prefijoPoisson P Z m ω)
  let e : ℕ → H01 (volume : Measure Plano) cuadrado := fun m =>
    ⟨grafoLevantado G (q m) - u, errorLevantado_mem_H01 G (q m) u hu⟩
  exact transferencia_simultanea323 e (fun m => residuoLevantado G (q m) _)
    (fun m => perdidaPoissonInterior (laplacianoClásico (aproximacionLevantada G (q m))) f)
    (fun m => laplaciano_errorLevantado G (q m) u _ hsol)
    (fun _ => perdidaInterior_nonneg _ _ _)
    (fun m => norma_residuo323_de_perdida G (q m) f (dato315_memLp f hf)) hω

/-- La versión levantada con valores de frontera de un representante continuo.
La solución exacta puede tener solo regularidad Sobolev y continuidad. -/
theorem corolario323_poisson_levantado_frontera
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Muestreo38 P medidaUniformeCuadrado) [MeasurableSpace CandidatoPoisson]
    (G : CandidatoPoisson) (f : Plano → ℝ) (Hm : ℕ → Set CandidatoPoisson)
    (hf : EsHolderInterior cuadrado (1 / 2) f)
    (sel : Selecciones315 P Z (fun q => laplacianoClásico (aproximacionLevantada G q)) f Hm)
    (u : H1Graph (volume : Measure Plano) cuadrado) (hu : u ∈ W12 volume cuadrado)
    (uc : Plano → ℝ) (huc : ContinuousOn uc (closure cuadrado))
    (hurep : ⇑(fnL u) =ᵐ[volumenPoisson] uc) (hfr : EqOn uc G.val (frontier cuadrado))
    (hsol : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL u) volume ⊤) =
      Distribution.ofFun cuadradoOpens (datoPoissonLp f (dato315_memLp f hf)) volume ⊤) :
    ∀ᵐ ω ∂P,
      let e := fun m => grafoLevantado G (sel.h m (prefijoPoisson P Z m ω)) - u
      (fun m => ‖e m‖ + normaEsencial323 (e m)) =O[atTop]
        (fun m : ℕ => (Real.log (m : ℝ) / m) ^ (1 / 4 : ℝ)) ∧
      Tendsto (fun m => ‖e m‖) atTop (𝓝 0) ∧
      Tendsto (fun m => normaEsencial323 (e m)) atTop (𝓝 0) := by
  have hzero := frontera_puntual_igual_implica_error_H01 u (grafoSuaveCuadrado G)
    hu (grafoSuaveCuadrado_mem_W12 G) huc G.property.continuous.continuousOn
    hurep (grafoSuaveCuadrado_fnL_ae G) hfr
  exact corolario323_poisson_levantado P Z G f Hm hf sel u hzero hsol

#check cotas_simultaneas323
#check corolario323_escalar
#check corolario323_frontera_puntual
#check corolario323_poisson_levantado
#print axioms cotas_simultaneas323
#print axioms representante323_coincide
#print axioms laplaciano_diferencia323
#print axioms cotas_simultaneas323_frontera_puntual
#print axioms norma_residuo323_de_perdida
#print axioms transferencia_simultanea323
#print axioms corolario323_escalar
#print axioms corolario323_frontera_puntual
#print axioms corolario323_poisson_levantado
#print axioms corolario323_poisson_levantado_frontera

set_option maxHeartbeats 800000 in
/-- Cotas de (3.81)–(3.82) para dos elementos Sobolev arbitrarios de igual
traza. La continuidad del representante se deduce para el error. -/
theorem cotas_simultaneas323_traza
    (h u : W12 (volume : Measure Plano) cuadrado)
    (htr : trazaSobolevCuadrado h = trazaSobolevCuadrado u)
    (d f : Lp ℝ 2 volumenPoisson)
    (hΔ : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL (h : H1Graph volume cuadrado)) volume ⊤) =
      Distribution.ofFun cuadradoOpens d volume ⊤)
    (uΔ : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL (u : H1Graph volume cuadrado)) volume ⊤) =
      Distribution.ofFun cuadradoOpens f volume ⊤) :
    let e : H1Graph (volume : Measure Plano) cuadrado := (h : H1Graph volume cuadrado) - u
    ‖e‖ ≤ constanteH1323 * ‖d - f‖ ∧
      normaEsencial323 e ≤ (26404 / 100000 : ℝ) * ‖d - f‖ ∧
      ‖e‖ + normaEsencial323 e ≤ constanteSimultanea323 * ‖d - f‖ ∧
      ∃ g : Plano → ℝ, Continuous g ∧ ⇑(fnL e) =ᵐ[volumenPoisson] g ∧
        EqOn g 0 (frontier cuadrado) ∧ supResiduo (closure cuadrado) g = normaEsencial323 e := by
  have he := diferencia_mem_H01_de_trazas_iguales h u htr
  exact cotas_simultaneas323 _ _ (laplaciano_diferencia323 h u he d f hΔ uΔ)

/-- Tasa (3.83) para las selecciones de P3.15 y Dirichlet exacto en el
sentido de las trazas Sobolev. -/
theorem corolario323_traza
    {H : Type*} [MeasurableSpace H] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Muestreo38 P medidaUniformeCuadrado) (L : H → Plano → ℝ) (f : Plano → ℝ)
    (Hm : ℕ → Set H) (hf : EsHolderInterior cuadrado (1 / 2) f)
    (hHolder : ∀ m w, w ∈ Hm m → EsHolderInterior cuadrado (1 / 2) (L w))
    (sel : Selecciones315 P Z L f Hm)
    (h : H → W12 (volume : Measure Plano) cuadrado) (u : W12 (volume : Measure Plano) cuadrado)
    (htr : ∀ w, trazaSobolevCuadrado (h w) = trazaSobolevCuadrado u)
    (d : H → Lp ℝ 2 volumenPoisson) (F : Lp ℝ 2 volumenPoisson)
    (hd : ∀ w, ⇑(d w) =ᵐ[volumenPoisson] L w) (hF : ⇑F =ᵐ[volumenPoisson] f)
    (hΔ : ∀ w, laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL (h w : H1Graph volume cuadrado)) volume ⊤) =
      Distribution.ofFun cuadradoOpens (d w) volume ⊤)
    (uΔ : laplacianoDistribucional cuadradoOpens
      (Distribution.ofFun cuadradoOpens (fnL (u : H1Graph volume cuadrado)) volume ⊤) =
      Distribution.ofFun cuadradoOpens F volume ⊤) :
    ∀ᵐ ω ∂P,
      let w := fun m => sel.h m (prefijoPoisson P Z m ω)
      let e := fun m => (h (w m) : H1Graph volume cuadrado) - u
      (fun m => ‖e m‖ + normaEsencial323 (e m)) =O[atTop]
        (fun m : ℕ => (Real.log (m : ℝ) / m) ^ (1 / 4 : ℝ)) ∧
      Tendsto (fun m => ‖e m‖) atTop (𝓝 0) ∧
      Tendsto (fun m => normaEsencial323 (e m)) atTop (𝓝 0) := by
  have he (w : H) := diferencia_mem_H01_de_trazas_iguales (h w) u (htr w)
  exact corolario323_escalar P Z L f Hm hf hHolder sel
    (fun w => ⟨(h w : H1Graph volume cuadrado) - u, he w⟩) (fun w => d w - F)
    (fun w => laplaciano_diferencia323 (h w) u (he w) (d w) F (hΔ w) uΔ)
    (fun w => (Lp.coeFn_sub _ _).trans ((hd w).sub hF))

#check cotas_simultaneas323_traza
#check corolario323_traza
#print axioms cotas_simultaneas323_traza
#print axioms corolario323_traza

end TesisPINN
