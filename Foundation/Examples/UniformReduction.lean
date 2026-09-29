import Foundation.Resource.UniformReduction
import Foundation.Security.Reduction

namespace Foundation.Examples.UniformReduction

/-- Separate dummy goals with zero advantage. -/
def P : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun _ _ => Nat
  advantage := fun _ _ _ => 0

def Q : CryptoGoal where
  Instance := fun _ => Bool
  Adversary := fun _ _ => Nat
  advantage := fun _ _ _ => 0

/-- The reduction increments each adversary, independently of the program
transformation below. -/
def R : Reduction P Q where
  mapInstance := fun _ => true
  reduce := fun _ a => (show Nat from a) + 1
  loss := AdvantageBound.id
  advantage_le := by
    intro _ _ _
    exact le_refl _

def sourceModel : UniformAdversaryModel P where
  Program := fun _ => Nat
  realize := fun _ prog n => prog + n

def targetModel : UniformAdversaryModel Q where
  Program := fun _ => Nat
  realize := fun _ prog n => prog + n

/-- Adding one to the program realizes the same family as incrementing
each adversary through `R`. The two transformations are separate data. -/
def T : R.ProgramTransformation sourceModel targetModel where
  transform := fun _ prog => (show Nat from prog) + 1
  realizes := by
    intro F prog
    funext n
    change ((show Nat from prog) + 1) + n =
      ((show Nat from prog) + n) + 1
    omega

example (F : InstanceFamily P) : T.transform F (3 : Nat) = (4 : Nat) := by
  rfl

example (F : InstanceFamily P) (prog : Nat) :
    sourceModel.Realizable F (sourceModel.realize F prog) := by
  exact ⟨prog, rfl⟩

example (F : InstanceFamily P) (prog : Nat) :
    targetModel.Realizable (R.mapFamily F)
      (R.mapAdversaryFamily F (sourceModel.realize F prog)) := by
  have hSource : sourceModel.uniformClass.admissible F
      (sourceModel.realize F prog) := ⟨prog, rfl⟩
  exact T.preservesAdmissibility.preserves F _ hSource

example : R.PreservesAdmissibility
    sourceModel.uniformClass targetModel.uniformClass :=
  T.preservesAdmissibility

/-- The existing security theorem accepts uniform-class preservation from
the program transformation and the identity advantage loss. -/
example (F : InstanceFamily P)
    (hQ : SecureOnWithin Q targetModel.uniformClass (R.mapFamily F)) :
    SecureOnWithin P sourceModel.uniformClass F := by
  exact R.secureOnWithin sourceModel.uniformClass targetModel.uniformClass F
    T.preservesAdmissibility AdvantageBound.id_preservesNegligible hQ

end Foundation.Examples.UniformReduction
