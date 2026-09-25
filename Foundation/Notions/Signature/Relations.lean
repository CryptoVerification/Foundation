import Foundation.Notions.Signature.EUFtoStrong
import Foundation.Notions.Signature.Examples
import Foundation.Notions.Signature.StrongExamples

open scoped ENNReal

namespace Foundation.Notions.Signature.RelationExamples

open Foundation.Notions.Signature.Examples (Plain)

/-- A type-level example with a larger strong-EUF advantage. -/
def strongSemantics : StrongEUFCMASemantics Plain where
  advantage := fun _ _ _ => 1

theorem dummyCompatibility : EUFStrongCompatibility Plain
    Foundation.Notions.Signature.Examples.dummySemantics strongSemantics where
  advantage_le := by
    intro n scheme A
    exact zero_le

def dummyReduction : Reduction
    (EUFCMA Plain Foundation.Notions.Signature.Examples.dummySemantics)
    (StrongEUFCMA Plain strongSemantics) :=
  eufCMA_to_strongEUFCMA_reduction Plain
    Foundation.Notions.Signature.Examples.dummySemantics
    strongSemantics dummyCompatibility

theorem dummyReducesTo : ReducesTo
    (EUFCMA Plain Foundation.Notions.Signature.Examples.dummySemantics)
    (StrongEUFCMA Plain strongSemantics) :=
  ⟨dummyReduction⟩

def dummyFamily : InstanceFamily
    (EUFCMA Plain Foundation.Notions.Signature.Examples.dummySemantics) :=
  Foundation.Notions.Signature.Examples.dummyFamily

theorem mappedFamily_eq : dummyReduction.mapFamily dummyFamily = dummyFamily := by
  rfl

example : dummyReduction.mapFamily dummyFamily =
    Foundation.Notions.Signature.StrongExamples.dummyFamily := by
  rfl

theorem boundTransport (ε : Nat → ℝ≥0∞)
    (hStrong : BoundedByOn (StrongEUFCMA Plain strongSemantics)
      (dummyReduction.mapFamily dummyFamily) ε) :
    BoundedByOn
      (EUFCMA Plain Foundation.Notions.Signature.Examples.dummySemantics)
      dummyFamily ε :=
  dummyReduction.boundedByOn dummyFamily hStrong

theorem strongFamilyBound :
    BoundedByOn (StrongEUFCMA Plain strongSemantics)
      (dummyReduction.mapFamily dummyFamily) (fun _ => 1) := by
  intro n A
  exact le_refl _

theorem eufFamilyBoundViaStrong :
    BoundedByOn
      (EUFCMA Plain Foundation.Notions.Signature.Examples.dummySemantics)
      dummyFamily (fun _ => 1) :=
  boundTransport (fun _ => 1) strongFamilyBound

end Foundation.Notions.Signature.RelationExamples
