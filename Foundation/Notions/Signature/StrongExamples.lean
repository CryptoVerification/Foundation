import Foundation.Core.SecurityBound
import Foundation.Notions.Signature.StrongEUFCMA
import Foundation.Notions.Signature.Examples

open scoped ENNReal

namespace Foundation.Notions.Signature.StrongExamples

open Foundation.Notions.Signature.Examples (Plain)

def dummySemantics : StrongEUFCMASemantics Plain where
  advantage := fun _ _ _ => 0

def dummyGoal : CryptoGoal := StrongEUFCMA Plain dummySemantics

/-- The same scheme family serves both EUF-CMA and strong EUF-CMA. -/
def dummyFamily : InstanceFamily (StrongEUFCMA Plain dummySemantics) :=
  Foundation.Notions.Signature.Examples.dummyFamily

example (n : Nat) :
    (EUFCMA Plain Foundation.Notions.Signature.Examples.dummySemantics).Instance n =
      (StrongEUFCMA Plain dummySemantics).Instance n := by
  rfl

example (n : Nat) (scheme : SignatureScheme Plain) :
    (EUFCMA Plain Foundation.Notions.Signature.Examples.dummySemantics).Adversary n scheme =
      (StrongEUFCMA Plain dummySemantics).Adversary n scheme := by
  rfl

/-- The existing EUF-CMA adversary value also inhabits the strong goal. -/
def dummyAdversary (n : Nat) : dummyGoal.Adversary n (dummyFamily n) :=
  Foundation.Notions.Signature.Examples.dummyAdversary n

example (n : Nat) :
    (EUFCMA Plain Foundation.Notions.Signature.Examples.dummySemantics).Adversary
      n (dummyFamily n) :=
  dummyAdversary n

theorem dummyFamilyBound :
    BoundedByOn (StrongEUFCMA Plain dummySemantics) dummyFamily (fun _ => 0) := by
  intro n A
  exact le_refl _

example (n : Nat) :
    dummyGoal.advantage n (dummyFamily n) (dummyAdversary n) = 0 := by
  rfl

end Foundation.Notions.Signature.StrongExamples
