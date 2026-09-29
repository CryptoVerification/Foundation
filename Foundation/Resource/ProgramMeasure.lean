import Foundation.Resource.Uniformity
import Foundation.Asymptotics.PolynomiallyBounded

universe u v

/-- An abstract scalar resource profile on program objects. For a fixed
`prog`, `profile F prog n` observes its resource at security parameter `n`.
This does not specify execution semantics or the meaning of the resource. -/
structure ProgramResourceMeasure {P : CryptoGoal.{u}}
    (M : UniformAdversaryModel.{u, v} P) where
  profile : ∀ (F : InstanceFamily P), M.Program F → Nat → Nat

namespace ProgramResourceMeasure

/-- The measure reporting zero for every program and parameter. -/
def zero {P : CryptoGoal.{u}} (M : UniformAdversaryModel.{u, v} P) :
    ProgramResourceMeasure M where
  profile := fun _ _ _ => 0

end ProgramResourceMeasure

namespace UniformAdversaryModel

/-- Admit a family when one and the same program realizes it and has a
polynomially bounded measured resource profile. The polynomial bound may
depend on that program; no common bound for all programs is required. -/
def polynomialProgramClass {P : CryptoGoal.{u}}
    (M : UniformAdversaryModel.{u, v} P) (C : ProgramResourceMeasure M) :
    AdversaryClass P where
  admissible := fun F A =>
    ∃ prog : M.Program F,
      M.realize F prog = A ∧ PolynomiallyBounded (C.profile F prog)

end UniformAdversaryModel
