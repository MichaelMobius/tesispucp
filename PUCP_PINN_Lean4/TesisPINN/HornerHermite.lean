import TesisPINN.Proposicion325

/-! Realización particular de Hermite por Horner con cuatro registros. -/

noncomputable section

namespace TesisPINN

open Polynomial
open scoped Polynomial

private abbrev RegHorner := Fin 4

/-- Un bloque aplica una polarización y luego codifica la transformación
afín de cada registro decodificado. -/
private def bloqueAfinHorner (r : CapasCuadraticas Bool (RegHorner × Bool))
    (op : RegHorner → OperacionRegistro RegHorner) (c b : RegHorner → ℝ) :
    CapasCuadraticas Bool (RegHorner × Bool) :=
  (r.agregar (capaPolarizar op)).agregar
    (desdeRegistros (codificarCapa (fun j i => c j * filaRegistro j i) b))

private theorem bloqueAfinHorner_eval (r : CapasCuadraticas Bool (RegHorner × Bool))
    (op : RegHorner → OperacionRegistro RegHorner) (c b : RegHorner → ℝ)
    (x : Bool → ℝ) (v : RegHorner → ℝ) (h : r.eval x = banco v) :
    (bloqueAfinHorner r op c b).eval x = banco (fun j => b j + c j * (op j).valor v) := by
  simp only [bloqueAfinHorner, CapasCuadraticas.eval]
  rw [h, capaPolarizar_eval, desdeRegistros_eval, codificarCapa_eval]
  simp_rw [OperacionRegistro.decodificar_polarizar, mul_assoc, ← Finset.mul_sum, suma_filaRegistro]

private theorem bloqueAfinHorner_dim (r : CapasCuadraticas Bool (RegHorner × Bool))
    (op : RegHorner → OperacionRegistro RegHorner) (c b : RegHorner → ℝ) :
    (bloqueAfinHorner r op c b).dimensiones = r.dimensiones ++ [8, 8] := by
  norm_num [bloqueAfinHorner, CapasCuadraticas.dimensiones, Fintype.card_prod]

private def hornerParcial (p : ℝ[X]) (L : ℕ) (x : ℝ) : ℕ → ℝ
  | 0 => p.coeff L
  | k + 1 => x * hornerParcial p L x k + p.coeff (L - (k + 1))

private theorem hornerParcial_suma (p : ℝ[X]) (L : ℕ) (x : ℝ) (k : ℕ) (hk : k ≤ L) :
    hornerParcial p L x k = ∑ j ∈ Finset.range (k + 1), p.coeff (L - k + j) * x ^ j := by
  induction k with
  | zero => simp [hornerParcial]
  | succ k ih =>
    rw [hornerParcial, ih (by omega)]
    conv_rhs => rw [Finset.sum_range_succ']
    rw [Finset.mul_sum]
    simp only [Nat.add_zero, pow_zero, mul_one]
    apply congrArg (fun y : ℝ => y + p.coeff (L - (k + 1)))
    apply Finset.sum_congr rfl
    intro j _
    rw [show L - k + j = L - (k + 1) + (j + 1) by omega, pow_succ]
    ring

private theorem hornerParcial_eval (p : ℝ[X]) (L : ℕ) (x : ℝ) (hL : p.natDegree ≤ L) :
    hornerParcial p L x L = p.eval x := by
  rw [hornerParcial_suma p L x L le_rfl, Nat.sub_self]
  simpa only [zero_add] using (eval_eq_sum_range' (Nat.lt_succ_of_le hL) x).symm

private def estadoHorner (p q : ℝ[X]) (L k : ℕ) (x : Bool → ℝ) : RegHorner → ℝ :=
  ![x true, x false, hornerParcial p L (x true) k, hornerParcial q L (x false) k]

private def inicialHorner (p q : ℝ[X]) (L : ℕ) : CapaCuadratica Bool (RegHorner × Bool) :=
  codificarCapa
    (fun i b => ![(if b then (1 : ℝ) else 0), (if b then 0 else 1), 0, 0] i)
    ![0, 0, p.coeff L, q.coeff L]

private theorem inicialHorner_eval (p q : ℝ[X]) (L : ℕ) (x : Bool → ℝ) :
    (inicialHorner p q L).eval x = banco (estadoHorner p q L 0 x) := by
  rw [inicialHorner, codificarCapa_eval]
  congr 1
  funext j
  fin_cases j <;> simp [Fintype.sum_bool, estadoHorner, hornerParcial]

private def operacionesHorner : RegHorner → OperacionRegistro RegHorner :=
  ![.copiar 0, .copiar 1, .producto 0 2, .producto 1 3]

private def capasHorner (p q : ℝ[X]) (L : ℕ) : ℕ → CapasCuadraticas Bool (RegHorner × Bool)
  | 0 => (CapasCuadraticas.vacia Bool).agregar (inicialHorner p q L)
  | k + 1 => bloqueAfinHorner (capasHorner p q L k) operacionesHorner (fun _ => 1)
      ![0, 0, p.coeff (L - (k + 1)), q.coeff (L - (k + 1))]

private theorem capasHorner_eval (p q : ℝ[X]) (L k : ℕ) (x : Bool → ℝ) :
    (capasHorner p q L k).eval x = banco (estadoHorner p q L k x) := by
  induction k with
  | zero => exact inicialHorner_eval p q L x
  | succ k ih =>
    rw [capasHorner, bloqueAfinHorner_eval _ _ _ _ _ _ ih]
    congr 1
    funext j
    fin_cases j <;> simp [operacionesHorner, OperacionRegistro.valor, estadoHorner,
      hornerParcial, add_comm]

private theorem capasHorner_dim (p q : ℝ[X]) (L k : ℕ) :
    (capasHorner p q L k).dimensiones = List.replicate (1 + 2 * k) 8 := by
  induction k with
  | zero => norm_num [capasHorner, CapasCuadraticas.dimensiones, Fintype.card_prod]
  | succ k ih =>
    rw [capasHorner, bloqueAfinHorner_dim, ih, show 1 + 2 * (k + 1) = (1 + 2 * k) + 2 by omega]
    exact (List.replicate_add (1 + 2 * k) 2 8).symm

private def opFactoresHorner : RegHorner → OperacionRegistro RegHorner :=
  ![.producto 0 0, .producto 1 1, .producto 2 3, .copiar 0]

private def opFronteraHorner : RegHorner → OperacionRegistro RegHorner :=
  ![.producto 0 1, .copiar 2, .copiar 2, .copiar 2]

private def opSalidaHorner : RegHorner → OperacionRegistro RegHorner :=
  ![.producto 0 1, .copiar 1, .copiar 2, .copiar 3]

/-- Los dos Horner se ejecutan en paralelo con el mayor grado, completando
los coeficientes de la otra proyección con ceros. -/
def redHorner325 (p q : ℝ[X]) (L : ℕ) : CapasCuadraticas Bool (RegHorner × Bool) :=
  let r := bloqueAfinHorner (capasHorner p q L L) opFactoresHorner ![-1, -1, 1, 1] ![1, 1, 0, 0]
  (bloqueRegistros r opFronteraHorner).agregar (capaPolarizar opSalidaHorner)

def lecturaHorner325 (j : RegHorner × Bool) : ℝ :=
  if j.1 = 0 then coefRegistro j.2 else 0

theorem redHorner325_dimensiones (p q : ℝ[X]) (L : ℕ) :
    (redHorner325 p q L).dimensiones = List.replicate (2 * L + 6) 8 := by
  simp only [redHorner325, CapasCuadraticas.dimensiones]
  rw [bloqueRegistros_dimensiones, bloqueAfinHorner_dim, capasHorner_dim]
  rw [show 2 * L + 6 = ((1 + 2 * L) + 2 + 2) + 1 by omega]
  simp [List.replicate_add]

theorem redHorner325_salida (p q : ℝ[X]) (L : ℕ)
    (hp : p.natDegree ≤ L) (hq : q.natDegree ≤ L) (x : Bool → ℝ) :
    (redHorner325 p q L).salida lecturaHorner325 x =
      factor324 x * (p.eval (x true) * q.eval (x false)) := by
  let r := bloqueAfinHorner (capasHorner p q L L) opFactoresHorner ![-1, -1, 1, 1] ![1, 1, 0, 0]
  have hr : r.eval x =
      banco ![1 - x true ^ 2, 1 - x false ^ 2, p.eval (x true) * q.eval (x false), x true] := by
    rw [show r = bloqueAfinHorner (capasHorner p q L L) opFactoresHorner
        ![-1, -1, 1, 1] ![1, 1, 0, 0] from rfl,
      bloqueAfinHorner_eval _ _ _ _ _ _ (capasHorner_eval p q L L x)]
    congr 1
    funext j
    fin_cases j <;> simp [opFactoresHorner, OperacionRegistro.valor, estadoHorner,
      hornerParcial_eval, hp, hq, pow_two, sub_eq_add_neg]
  unfold CapasCuadraticas.salida
  change (∑ j, lecturaHorner325 j *
    ((bloqueRegistros r opFronteraHorner).agregar (capaPolarizar opSalidaHorner)).eval x j) = _
  rw [CapasCuadraticas.eval, bloqueRegistros_eval _ _ _ _ hr, capaPolarizar_eval,
    Fintype.sum_prod_type, Finset.sum_eq_single (0 : RegHorner)]
  · simp only [lecturaHorner325, ite_true, suma_coefRegistro]
    rw [OperacionRegistro.decodificar_polarizar]
    simp [opSalidaHorner, opFronteraHorner, OperacionRegistro.valor, factor324]
  · intro i _ hi
    simp [lecturaHorner325, hi]
  · simp

/-- La red específica del comparador de P3.25 tiene anchura ocho y
exactamente `8 * max rx ry + 4` capas ocultas. -/
theorem comparador325_horner {m : ℕ} (hm : 1 ≤ m) (s : Fin m → Plano) :
    let rx := (nodosDistintosHermite (fun i => s i 0)).card
    let ry := (nodosDistintosHermite (fun i => s i 1)).card
    ∃ r : CapasCuadraticas Bool (RegHorner × Bool),
      r.dimensiones = List.replicate (8 * max rx ry + 4) 8 ∧
      ∀ x : Plano, r.salida lecturaHorner325 (fun b => if b then x 0 else x 1) = comparador325 s x := by
  dsimp only
  let n (j : Fin 2) := (nodosDistintosHermite (fun i => s i j)).card
  let R := max (n 0) (n 1)
  let L := 4 * R - 1
  have hn (j : Fin 2) : 0 < n j := by
    apply Finset.card_pos.mpr
    exact ⟨s ⟨0, hm⟩ j, Finset.mem_image.mpr ⟨⟨0, hm⟩, Finset.mem_univ _, rfl⟩⟩
  have hR : 0 < R := (hn 0).trans_le (le_max_left _ _)
  have hdeg (j : Fin 2) : (factorHermite325 s j).natDegree ≤ L := by
    by_cases hz : factorHermite325 s j = 0
    · simp [hz]
    · have hd : (factorHermite325 s j).natDegree < 4 * n j :=
        (natDegree_lt_iff_degree_lt hz).mpr
          (mem_degreeLT.mp (hermiteMuestra (fun i => s i j) datosManufacturados).property)
      have hle : n j ≤ R := by fin_cases j; exact le_max_left _ _; exact le_max_right _ _
      dsimp [L]
      omega
  refine ⟨redHorner325 (factorHermite325 s 0) (factorHermite325 s 1) L, ?_, fun x => ?_⟩
  · rw [redHorner325_dimensiones]
    change List.replicate (2 * L + 6) 8 = List.replicate (8 * R + 4) 8
    congr 1
    dsimp [L]
    omega
  · rw [redHorner325_salida _ _ _ (hdeg 0) (hdeg 1), factor324_eq_psiCuadrado]
    rfl

#check comparador325_horner
#print axioms redHorner325_salida
#print axioms comparador325_horner

end TesisPINN

