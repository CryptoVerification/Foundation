import Foundation.Core.SecurityBound
import Foundation.Notions.PKE.INDCCA2
import Foundation.Notions.PKE.Examples

open scoped ENNReal

namespace Foundation.Notions.PKE.CCAExamples

open Foundation.Notions.PKE.Examples (Plain)

/-- Reuse the PKE syntax instance from the IND-CPA example. -/
def dummyPKE : PKE Plain := Foundation.Notions.PKE.Examples.dummyPKE

def dummySemantics : INDCCA2Semantics Plain where
  advantage := fun _ _ _ => 0

def dummyGoal : CryptoGoal := INDCCA2 Plain dummySemantics

/-- The IND-CPA family is also an IND-CCA2 instance family. -/
def sharedFamily : InstanceFamily (INDCCA2 Plain dummySemantics) :=
  Foundation.Notions.PKE.Examples.fixedSchemeFamily

/-- Both stages can use the decryption capability, and the second receives state. -/
def dummyAdversary (n : Nat) : dummyGoal.Adversary n (sharedFamily n) where
  State := Bool
  choose := fun oracle _ =>
    (false, true, (oracle false).isSome)
  guess := fun oracle state challenge =>
    state && (oracle (!challenge)).isSome

theorem sharedFamilyBound :
    BoundedByOn (INDCCA2 Plain dummySemantics) sharedFamily (fun _ => 0) := by
  intro n A
  exact le_refl _

example (n : Nat) :
    dummyGoal.advantage n (sharedFamily n) (dummyAdversary n) = 0 := by
  rfl

end Foundation.Notions.PKE.CCAExamples
