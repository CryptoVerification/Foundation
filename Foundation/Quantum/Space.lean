import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin

/-! Finite basis types for wire interfaces, including dimension zero. -/
namespace Foundation.Quantum

inductive Space where
  | unit | bit | register : Nat → Space | tensor : Space → Space → Space
  deriving DecidableEq

namespace Space

@[reducible] def Basis : Space → Type
  | .unit => Unit
  | .bit => Fin 2
  | .register n => Fin n
  | .tensor a b => Basis a × Basis b

instance basisFintype : (a : Space) → Fintype a.Basis
  | .unit => inferInstanceAs (Fintype Unit)
  | .bit => inferInstanceAs (Fintype (Fin 2))
  | .register n => inferInstanceAs (Fintype (Fin n))
  | .tensor a b => @instFintypeProd _ _ (basisFintype a) (basisFintype b)

instance basisDecidableEq : (a : Space) → DecidableEq a.Basis
  | .unit => inferInstanceAs (DecidableEq Unit)
  | .bit => inferInstanceAs (DecidableEq (Fin 2))
  | .register n => inferInstanceAs (DecidableEq (Fin n))
  | .tensor a b => @instDecidableEqProd _ _ (basisDecidableEq a) (basisDecidableEq b)

end Space
end Foundation.Quantum
