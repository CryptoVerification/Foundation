import Foundation.Assumptions.DDH.Structured
import Foundation.Assumptions.DDH.Examples

open scoped ENNReal

namespace Foundation.Assumptions.DDH.StructuredExamples

open Foundation.Assumptions.DDH.Examples (Plain dummyParameters dummySemantics)

def dummyInstance : DDHParameterInstance where
  params := dummyParameters
  parameterId := 7

def specializedFamily : InstanceFamily (StructuredDDH Plain dummySemantics) :=
  fun n => { params := dummyParameters, parameterId := n }

def genericFamily : InstanceFamily (DDH Plain dummySemantics) :=
  fun n => (specializedFamily n).params

/-- The specialized goal uses exactly the original DDH adversary type. -/
example (M : Type → Type) (S : DDHSemantics M) (n : Nat)
    (I : DDHParameterInstance) :
    (StructuredDDH M S).Adversary n I =
      (DDH M S).Adversary n I.params := by
  rfl

def dummyAdversary : DDHAdversary Plain dummyInstance.params :=
  Foundation.Assumptions.DDH.Examples.dummyAdversary 0

example (n : Nat) :
    (StructuredDDH Plain dummySemantics).Adversary n dummyInstance :=
  dummyAdversary

example (n : Nat) :
    (DDH Plain dummySemantics).Adversary n dummyInstance.params :=
  dummyAdversary

/-- Reindexing also leaves the advantage at the underlying instance unchanged. -/
example (M : Type → Type) (S : DDHSemantics M) (n : Nat)
    (I : DDHParameterInstance) (A : DDHAdversary M I.params) :
    (StructuredDDH M S).advantage n I A =
      (DDH M S).advantage n I.params A := by
  rfl

example (ε : Nat → ℝ≥0∞) :
    BoundedByOn (StructuredDDH Plain dummySemantics) specializedFamily ε ↔
      BoundedByOn (DDH Plain dummySemantics) genericFamily ε := by
  exact CryptoGoal.boundedByOn_reindex_iff
    (DDH Plain dummySemantics) (fun _ => DDHParameterInstance)
    (fun _ I => I.params) specializedFamily ε

example : BoundedByOn (StructuredDDH Plain dummySemantics)
    specializedFamily (fun _ => 0) := by
  apply (CryptoGoal.boundedByOn_reindex_iff
    (DDH Plain dummySemantics) (fun _ => DDHParameterInstance)
    (fun _ I => I.params) specializedFamily (fun _ => 0)).mpr
  exact Foundation.Assumptions.DDH.Examples.dummyFamilyBound

end Foundation.Assumptions.DDH.StructuredExamples
