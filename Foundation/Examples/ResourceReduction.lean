import Foundation.Resource.Reduction
import Foundation.Security.Reduction
import Foundation.Examples.AsymptoticReduction

namespace Foundation.Examples.ResourceReduction

universe u

example (P : CryptoGoal.{u}) (RM : ResourceMeasure P) :
    (Reduction.id P).PreservesAdmissibility
      RM.polynomialClass RM.polynomialClass :=
  (Reduction.ResourceBound.id P RM).preservesAdmissibility

example (P : CryptoGoal.{u}) (RM : ResourceMeasure P) :
    (Reduction.id P).PreservesAdmissibility
      RM.polynomialClass RM.polynomialClass :=
  Reduction.id_preservesAdmissibility P RM.polynomialClass

abbrev P : CryptoGoal := Foundation.Examples.Relations.A
abbrev Q : CryptoGoal := Foundation.Examples.Relations.B

def R : Reduction P Q := Foundation.Examples.AsymptoticReduction.dummyReduction

def sourceMeasure : ResourceMeasure P where
  profile := fun _ _ n => n

def targetMeasure : ResourceMeasure Q where
  profile := fun _ _ n => (n + 1) ^ 2 * (n + 1)

/-- Here the target cost equals `(n + 1)^2 * (sourceCost + 1)`.
These profiles are synthetic; no execution cost is measured. -/
def dummyBound : R.ResourceBound sourceMeasure targetMeasure where
  coefficient := 1
  securityDegree := 2
  sourceDegree := 1
  bound := by
    intro F A n
    change (n + 1) ^ 2 * (n + 1) ≤
      1 * (n + 1) ^ 2 * (n + 1) ^ 1
    simp

theorem dummyPreserves : R.PreservesAdmissibility
    sourceMeasure.polynomialClass targetMeasure.polynomialClass :=
  dummyBound.preservesAdmissibility

/-- The existing security theorem accepts the preservation proof derived
from the quantitative bound. This dummy goal has zero advantage. -/
theorem dummyTargetSecure (F : InstanceFamily P) :
    SecureOnWithin Q targetMeasure.polynomialClass (R.mapFamily F) := by
  intro A _
  change Negligible (fun _ => 0)
  exact Negligible.zero

example (F : InstanceFamily P) :
    SecureOnWithin P sourceMeasure.polynomialClass F :=
  R.secureOnWithin _ _ F dummyPreserves
    AdvantageBound.id_preservesNegligible (dummyTargetSecure F)

end Foundation.Examples.ResourceReduction
