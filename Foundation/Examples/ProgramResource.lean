import Foundation.Resource.ProgramMeasure
import Foundation.Examples.UniformAdversary

namespace Foundation.Examples.ProgramResource

open Foundation.Examples.UniformAdversary
  (goal family model constantZero_not_realizable uniform_secure)

universe u v

example {P : CryptoGoal.{u}} (M : UniformAdversaryModel.{u, v} P)
    (C : ProgramResourceMeasure M) (F : InstanceFamily P)
    (A : AdversaryFamily P F) :
    (M.polynomialProgramClass C).admissible F A ↔
      ∃ prog : M.Program F,
        M.realize F prog = A ∧ PolynomiallyBounded (C.profile F prog) := by
  rfl

example (F : InstanceFamily goal) (prog : model.Program F) :
    PolynomiallyBounded ((ProgramResourceMeasure.zero model).profile F prog) :=
  PolynomiallyBounded.zero

example (F : InstanceFamily goal) (A : AdversaryFamily goal F) :
    (model.polynomialProgramClass (ProgramResourceMeasure.zero model)).admissible F A ↔
      model.Realizable F A := by
  constructor
  · rintro ⟨prog, hReal, _⟩
    exact ⟨prog, hReal⟩
  · rintro ⟨prog, hReal⟩
    exact ⟨prog, hReal, PolynomiallyBounded.zero⟩

/-- A synthetic program-dependent resource observation. It measures the
program parameter together with a quadratic function of the security
parameter; it does not measure concrete execution. -/
def observed : ProgramResourceMeasure model where
  profile := fun _ prog n => (show Nat from prog) + n * n + 3 * n + 7

private theorem observed_polynomiallyBounded (F : InstanceFamily goal)
    (prog : model.Program F) :
    PolynomiallyBounded (observed.profile F prog) := by
  exact PolynomiallyBounded.add
    (PolynomiallyBounded.add
      (PolynomiallyBounded.add
        (PolynomiallyBounded.const (show Nat from prog))
        (PolynomiallyBounded.mul PolynomiallyBounded.id PolynomiallyBounded.id))
      (PolynomiallyBounded.mul (PolynomiallyBounded.const 3)
        PolynomiallyBounded.id))
    (PolynomiallyBounded.const 7)

/-- The same program `3` supplies both the realization equality and the
polynomial resource proof. -/
example : (model.polynomialProgramClass observed).admissible
    family (model.realize family (3 : Nat)) := by
  refine ⟨(3 : Nat), rfl, ?_⟩
  exact observed_polynomiallyBounded family (3 : Nat)

example : ¬ (model.polynomialProgramClass observed).admissible
    family (fun _ => (0 : Nat)) := by
  rintro ⟨prog, hReal, _⟩
  exact constantZero_not_realizable ⟨prog, hReal⟩

example {P : CryptoGoal.{u}} (M : UniformAdversaryModel.{u, v} P)
    (C : ProgramResourceMeasure M) (F : InstanceFamily P)
    (A : AdversaryFamily P F)
    (h : (M.polynomialProgramClass C).admissible F A) :
    M.uniformClass.admissible F A := by
  rcases h with ⟨prog, hReal, _⟩
  exact ⟨prog, hReal⟩

/-- Zero advantage establishes security for the new class directly. -/
example : SecureOnWithin goal (model.polynomialProgramClass observed) family := by
  intro A _
  change Negligible (fun _ => 0)
  exact Negligible.zero

/-- The same security statement follows by narrowing the uniform class. -/
example : SecureOnWithin goal (model.polynomialProgramClass observed) family := by
  apply SecureOnWithin.monoClass
    (C := model.uniformClass) (D := model.polynomialProgramClass observed)
    (F := family) ?_ uniform_secure
  intro F A hA
  rcases hA with ⟨prog, hReal, _⟩
  exact ⟨prog, hReal⟩

end Foundation.Examples.ProgramResource
