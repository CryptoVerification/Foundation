import Foundation.Crypto.Semantics.Resource.FiniteProgram
import Foundation.Examples.ProgramResource

namespace Foundation.Examples.FiniteProgram

open Foundation.Examples.UniformAdversary
  (goal family model uniform_secure)
open Foundation.Examples.ProgramResource
  (observed)

universe u v

/-- Unary coding demonstrates finite description without an efficiency claim. -/
def description : model.FiniteDescription where
  encode := fun _ prog => List.replicate (show Nat from prog) true
  encode_injective := by
    intro F p q h
    have hlen := congrArg List.length h
    change (List.replicate (show Nat from p) true).length =
      (List.replicate (show Nat from q) true).length at hlen
    change (show Nat from p) = (show Nat from q)
    rw [List.length_replicate, List.length_replicate] at hlen
    exact hlen

example : description.encode family (3 : Nat) = [true, true, true] := by rfl

example : (description.encode family (3 : Nat)).length = 3 := by rfl

example {P : CryptoGoal.{u}} (M : UniformAdversaryModel.{u, v} P)
    (D : M.FiniteDescription) (F : InstanceFamily P)
    (p q : M.Program F) (h : D.encode F p = D.encode F q) : p = q :=
  D.encode_injective F h

/-- Program `3` realizes the family, has a finite code, and has a
polynomially bounded abstract resource profile. The realization and
resource proofs use that same program object. -/
example : model.Realizable family (model.realize family (3 : Nat)) ∧
    (model.polynomialProgramClass observed).admissible
      family (model.realize family (3 : Nat)) ∧
    description.encode family (3 : Nat) = [true, true, true] := by
  have hPoly : PolynomiallyBounded (observed.profile family (3 : Nat)) := by
    exact PolynomiallyBounded.add
      (PolynomiallyBounded.add
        (PolynomiallyBounded.add
          (PolynomiallyBounded.const 3)
          (PolynomiallyBounded.mul PolynomiallyBounded.id PolynomiallyBounded.id))
        (PolynomiallyBounded.mul (PolynomiallyBounded.const 3)
          PolynomiallyBounded.id))
      (PolynomiallyBounded.const 7)
  exact ⟨⟨(3 : Nat), rfl⟩, ⟨(3 : Nat), rfl, hPoly⟩, rfl⟩

/-- Finite description remains an external model-level witness; security
continues to use the existing adversary class. -/
example : SecureOnWithin goal (model.polynomialProgramClass observed) family := by
  apply SecureOnWithin.monoClass
    (C := model.uniformClass) (D := model.polynomialProgramClass observed)
    (F := family) ?_ uniform_secure
  intro F A hA
  rcases hA with ⟨prog, hRealize, _⟩
  exact ⟨prog, hRealize⟩

end Foundation.Examples.FiniteProgram
