import Foundation.Notions.PKE.INDCCA2.FromINDCPA
import Foundation.Notions.PKE.INDCPA.Examples
import Foundation.Notions.PKE.INDCCA2.Examples

open scoped ENNReal

namespace Foundation.Notions.PKE.RelationExamples

open Foundation.Notions.PKE.Examples (Plain)

theorem dummyCompatibility : INDCPACCA2Compatibility Plain
    Foundation.Notions.PKE.Examples.dummySemantics
    Foundation.Notions.PKE.CCAExamples.dummySemantics where
  advantage_eq := by
    intro n scheme A
    rfl

def dummyReduction : Reduction
    (INDCPA Plain Foundation.Notions.PKE.Examples.dummySemantics)
    (INDCCA2 Plain Foundation.Notions.PKE.CCAExamples.dummySemantics) :=
  indCPA_to_indCCA2_reduction Plain
    Foundation.Notions.PKE.Examples.dummySemantics
    Foundation.Notions.PKE.CCAExamples.dummySemantics
    dummyCompatibility

theorem dummyReducesTo : ReducesTo
    (INDCPA Plain Foundation.Notions.PKE.Examples.dummySemantics)
    (INDCCA2 Plain Foundation.Notions.PKE.CCAExamples.dummySemantics) :=
  ⟨dummyReduction⟩

theorem mappedFamily_eq :
    dummyReduction.mapFamily Foundation.Notions.PKE.Examples.fixedSchemeFamily =
      Foundation.Notions.PKE.CCAExamples.sharedFamily := by
  rfl

theorem boundTransport (ε : Nat → ℝ≥0∞)
    (hCCA2 : BoundedByOn
      (INDCCA2 Plain Foundation.Notions.PKE.CCAExamples.dummySemantics)
      Foundation.Notions.PKE.CCAExamples.sharedFamily ε) :
    BoundedByOn
      (INDCPA Plain Foundation.Notions.PKE.Examples.dummySemantics)
      Foundation.Notions.PKE.Examples.fixedSchemeFamily ε := by
  have hMapped : BoundedByOn
      (INDCCA2 Plain Foundation.Notions.PKE.CCAExamples.dummySemantics)
      (dummyReduction.mapFamily Foundation.Notions.PKE.Examples.fixedSchemeFamily) ε := by
    rw [mappedFamily_eq]
    exact hCCA2
  exact dummyReduction.boundedByOn
    Foundation.Notions.PKE.Examples.fixedSchemeFamily hMapped

theorem dummyBoundViaCCA2 : BoundedByOn
    (INDCPA Plain Foundation.Notions.PKE.Examples.dummySemantics)
    Foundation.Notions.PKE.Examples.fixedSchemeFamily (fun _ => 0) :=
  boundTransport (fun _ => 0)
    Foundation.Notions.PKE.CCAExamples.sharedFamilyBound

end Foundation.Notions.PKE.RelationExamples
