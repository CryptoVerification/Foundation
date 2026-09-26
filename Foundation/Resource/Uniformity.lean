import Foundation.Resource.Adversary

universe u v

/-- An abstract realization of adversary families by program objects.
One object realizes the entire security-parameter-indexed family. The type
of program objects may depend on the instance family, and its universe is
independent of the goal's universe. This interface alone does not assert a
finite description, computability, or a runtime bound. -/
structure UniformAdversaryModel (P : CryptoGoal.{u}) where
  Program : InstanceFamily P → Type v
  realize : ∀ (F : InstanceFamily P), Program F → AdversaryFamily P F

namespace UniformAdversaryModel

/-- The entire adversary family `A` is realized by one program object in
`M`. -/
def Realizable {P : CryptoGoal.{u}} (M : UniformAdversaryModel.{u, v} P)
    (F : InstanceFamily P) (A : AdversaryFamily P F) : Prop :=
  ∃ prog : M.Program F, M.realize F prog = A

/-- Admit exactly the families realized by one program object of `M`. -/
def uniformClass {P : CryptoGoal.{u}} (M : UniformAdversaryModel.{u, v} P) :
    AdversaryClass P where
  admissible := fun F A => M.Realizable F A

end UniformAdversaryModel
