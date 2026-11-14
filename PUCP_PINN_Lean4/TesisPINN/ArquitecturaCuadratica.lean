import TesisPINN.RedCuadratica
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

/-! Capas afines con activación cuadrática y bloques de registros. -/

noncomputable section

namespace TesisPINN

open scoped BigOperators

structure CapaCuadratica (I J : Type) where
  peso : J → I → ℝ
  sesgo : J → ℝ

def CapaCuadratica.eval {I J : Type} [Fintype I] (c : CapaCuadratica I J)
    (x : I → ℝ) (j : J) : ℝ :=
  (c.sesgo j + ∑ i, c.peso j i * x i) ^ 2

/-- Una cadena tipada de capas. La entrada de cada capa es la salida
inmediata de la anterior. El tipo final no incluye la lectura lineal. -/
inductive CapasCuadraticas : Type → Type → Type 1
  | vacia (I : Type) : CapasCuadraticas I I
  | agregar {I J K : Type} [Fintype J] [Fintype K] :
      CapasCuadraticas I J → CapaCuadratica J K → CapasCuadraticas I K

namespace CapasCuadraticas

def eval {I J : Type} : CapasCuadraticas I J → (I → ℝ) → J → ℝ
  | .vacia _, x => x
  | @agregar _ K L instK _ q c, x => @CapaCuadratica.eval K L instK c (q.eval x)

def dimensiones {I J : Type} : CapasCuadraticas I J → List ℕ
  | .vacia _ => []
  | @agregar _ _ K _ _ q _ => q.dimensiones ++ [Fintype.card K]

def profundidad {I J : Type} (r : CapasCuadraticas I J) : ℕ := r.dimensiones.length

def salida {I J : Type} [Fintype J] (r : CapasCuadraticas I J) (a : J → ℝ)
    (x : I → ℝ) : ℝ := ∑ j, a j * r.eval x j

end CapasCuadraticas

def signoRegistro (s : Bool) : ℝ := if s then 1 else -1

def codificar (v : ℝ) (s : Bool) : ℝ := (v + signoRegistro s) ^ 2

def decodificar (z : Bool → ℝ) : ℝ := (z true - z false) / 4

theorem decodificar_codificar (v : ℝ) : decodificar (codificar v) = v := by
  simpa [decodificar, codificar, signoRegistro, sub_eq_add_neg] using decodificar_registro v

def banco {I : Type} (v : I → ℝ) (j : I × Bool) : ℝ := codificar (v j.1) j.2

def coefRegistro (s : Bool) : ℝ := signoRegistro s / 4

theorem suma_coefRegistro (z : Bool → ℝ) :
    (∑ s, coefRegistro s * z s) = decodificar z := by
  simp [coefRegistro, signoRegistro, decodificar]
  ring

/-- Precomposición de una fila afín con la decodificación de los registros. -/
def desdeRegistros {I J : Type} (c : CapaCuadratica I J) :
    CapaCuadratica (I × Bool) J where
  peso j i := c.peso j i.1 * coefRegistro i.2
  sesgo := c.sesgo

theorem desdeRegistros_eval {I J : Type} [Fintype I] (c : CapaCuadratica I J)
    (x : I × Bool → ℝ) :
    (desdeRegistros c).eval x = c.eval (fun i => decodificar (fun s => x (i, s))) := by
  funext j
  unfold CapaCuadratica.eval desdeRegistros
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum, suma_coefRegistro]

/-- Dos neuronas cuadráticas por fila afín. -/
def codificarCapa {I J : Type} (w : J → I → ℝ) (b : J → ℝ) :
    CapaCuadratica I (J × Bool) where
  peso j := w j.1
  sesgo j := b j.1 + signoRegistro j.2

theorem codificarCapa_eval {I J : Type} [Fintype I] (w : J → I → ℝ) (b : J → ℝ)
    (x : I → ℝ) :
    (codificarCapa w b).eval x = banco (fun j => b j + ∑ i, w j i * x i) := by
  funext j
  simp only [CapaCuadratica.eval, codificarCapa, banco, codificar]
  congr 1
  ring

def filaRegistro {I : Type} [DecidableEq I] (i : I) (j : I) : ℝ :=
  if j = i then 1 else 0

@[simp] theorem suma_filaRegistro {I : Type} [Fintype I] [DecidableEq I]
    (i : I) (v : I → ℝ) : (∑ j, filaRegistro i j * v j) = v i := by
  simp [filaRegistro]

/-- Una salida lógica se transporta o se forma por polarización. -/
inductive OperacionRegistro (I : Type)
  | copiar (i : I)
  | producto (a b : I)

def OperacionRegistro.valor {I : Type} (op : OperacionRegistro I) (v : I → ℝ) : ℝ :=
  match op with
  | .copiar i => v i
  | .producto a b => v a * v b

def OperacionRegistro.polarizar {I : Type} (op : OperacionRegistro I)
    (v : I → ℝ) (s : Bool) : ℝ :=
  match op with
  | .copiar i => codificar (v i) s
  | .producto a b => (v a + signoRegistro s * v b) ^ 2

theorem OperacionRegistro.decodificar_polarizar {I : Type}
    (op : OperacionRegistro I) (v : I → ℝ) :
    decodificar (op.polarizar v) = op.valor v := by
  cases op with
  | copiar i => exact decodificar_codificar (v i)
  | producto a b =>
    simpa [OperacionRegistro.polarizar, OperacionRegistro.valor, decodificar,
      signoRegistro, sub_eq_add_neg] using multiplicacion_cuadratica (v a) (v b)

def capaPolarizar {I J : Type} [DecidableEq I] (op : J → OperacionRegistro I) :
    CapaCuadratica (I × Bool) (J × Bool) :=
  desdeRegistros {
    peso := fun j i => match op j.1 with
      | .copiar a => filaRegistro a i
      | .producto a b => filaRegistro a i + signoRegistro j.2 * filaRegistro b i
    sesgo := fun j => match op j.1 with
      | .copiar _ => signoRegistro j.2
      | .producto _ _ => 0 }

theorem capaPolarizar_eval {I J : Type} [Fintype I] [DecidableEq I]
    (op : J → OperacionRegistro I) (v : I → ℝ) :
    (capaPolarizar op).eval (banco v) = fun j => (op j.1).polarizar v j.2 := by
  rw [capaPolarizar, desdeRegistros_eval]
  simp only [banco, decodificar_codificar]
  funext j
  unfold CapaCuadratica.eval
  cases hj : op j.1 with
  | copiar i => simp [hj, OperacionRegistro.polarizar, codificar, add_comm]
  | producto a b =>
    simp only [hj, OperacionRegistro.polarizar, zero_add, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum, suma_filaRegistro]

def capaTransporte {I : Type} [DecidableEq I] : CapaCuadratica (I × Bool) (I × Bool) :=
  desdeRegistros (codificarCapa filaRegistro (fun _ => 0))

theorem capaTransporte_eval {I : Type} [Fintype I] [DecidableEq I] (x : I × Bool → ℝ) :
    capaTransporte.eval x = banco (fun i => decodificar (fun s => x (i, s))) := by
  rw [capaTransporte, desdeRegistros_eval, codificarCapa_eval]
  simp only [suma_filaRegistro, zero_add]

theorem capaTransporte_banco {I : Type} [Fintype I] [DecidableEq I] (v : I → ℝ) :
    capaTransporte.eval (banco v) = banco v := by
  rw [capaTransporte_eval]
  simp only [banco, decodificar_codificar]

def bloqueRegistros {X I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (r : CapasCuadraticas X (I × Bool)) (op : J → OperacionRegistro I) :
    CapasCuadraticas X (J × Bool) :=
  (r.agregar (capaPolarizar op)).agregar capaTransporte

theorem bloqueRegistros_eval {X I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (r : CapasCuadraticas X (I × Bool))
    (op : J → OperacionRegistro I) (x : X → ℝ) (v : I → ℝ) (hx : r.eval x = banco v) :
    (bloqueRegistros r op).eval x = banco (fun j => (op j).valor v) := by
  simp only [bloqueRegistros, CapasCuadraticas.eval]
  rw [hx, capaPolarizar_eval, capaTransporte_eval]
  simp only [OperacionRegistro.decodificar_polarizar]

theorem bloqueRegistros_dimensiones {X I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (r : CapasCuadraticas X (I × Bool))
    (op : J → OperacionRegistro I) :
    (bloqueRegistros r op).dimensiones = r.dimensiones ++
      [2 * Fintype.card J, 2 * Fintype.card J] := by
  simp [bloqueRegistros, CapasCuadraticas.dimensiones, Fintype.card_prod, Nat.mul_comm]

#check CapasCuadraticas
#print axioms capaTransporte_banco
#print axioms bloqueRegistros_eval
#print axioms bloqueRegistros_dimensiones

end TesisPINN
