import Foundation.Crypto.Semantics.Oracle.StatefulDiagramHorizontal

/-! Two local schedule edits separated by an operation that reads all slots.
The edits do not move any operation across that intervening dependency. -/
namespace Foundation.Examples.StatefulDiagramHorizontal
open CryptoOracle.StatefulDiagram

def signature (op : Fin 5) : Interface (Fin 5) := ⟨if op = 2 then Finset.univ else ∅, {op}⟩

def leftSwap : Exchange signature [0, 1, 2] [1, 0, 2] := .swap [] [2] 0 1 (by decide_cbv)

def rightSwap : Exchange signature [3, 4] [4, 3] := .swap [] [] 3 4 (by decide_cbv)

def leftFirst : Exchange signature [0, 1, 2, 3, 4] [1, 0, 2, 4, 3] := horizontalLeft signature leftSwap rightSwap

def rightFirst : Exchange signature [0, 1, 2, 3, 4] [1, 0, 2, 4, 3] := horizontalRight signature leftSwap rightSwap

/-- The new root handles the separated pair without crossing operation 2. -/
def separatedCell : HorizontalCoherence signature leftFirst rightFirst := horizontalInterchange signature leftSwap rightSwap

def leftWithBacktrack : Exchange signature [0, 1, 2] [1, 0, 2] := (leftSwap.trans leftSwap.symm).trans leftSwap

def rightWithInverses : Exchange signature [3, 4] [4, 3] := (Exchange.refl [3, 4]).trans rightSwap.symm.symm

/-- Exercise generated composition and inverse cases, not only the root. -/
def compositeCell : HorizontalCoherence signature
    (horizontalLeft signature leftWithBacktrack rightWithInverses)
    (horizontalRight signature leftWithBacktrack rightWithInverses) :=
  horizontalInterchange signature leftWithBacktrack rightWithInverses

theorem root_count : separatedCell.squareCount signature = 1 := by rfl

theorem composite_count : compositeCell.squareCount signature = 3 := by
  simpa only [compositeCell, leftWithBacktrack, rightWithInverses, leftSwap, rightSwap, Exchange.swapCount] using
    horizontalInterchange_count signature leftWithBacktrack rightWithInverses

theorem blocker_not_crossed : checkExchange signature 1 2 = false ∧ checkExchange signature 2 3 = false := by decide_cbv

theorem actual_shared_store_law {Value : Type} (world : Kernels signature Value) (store : Store (Fin 5) Value) :
    execute signature world [0, 1, 2, 3, 4] store = execute signature world [1, 0, 2, 4, 3] store :=
  leftFirst.sound signature world store

/-- info: (2, 2, 4, 4, 1, 3, false, false) -/
#guard_msgs in
#eval (leftFirst.swapCount signature, rightFirst.swapCount signature,
  (horizontalLeft signature leftWithBacktrack rightWithInverses).swapCount signature,
  (horizontalRight signature leftWithBacktrack rightWithInverses).swapCount signature,
  separatedCell.squareCount signature, compositeCell.squareCount signature,
  checkExchange signature 1 2, checkExchange signature 2 3)

end Foundation.Examples.StatefulDiagramHorizontal
