import Foundation.Resource.Measure
import Foundation.Security.Asymptotic
import Foundation.Examples.AdversaryFamily

namespace Foundation.Examples.ResourceMeasure

open Foundation.Examples.AdversaryFamily (goal family reindexedGoal reindexedFamily)

example (R : ResourceMeasure goal) (F : InstanceFamily goal)
    (A : AdversaryFamily goal F) : Nat → Nat :=
  R.profile F A

example (F : InstanceFamily goal) (A : AdversaryFamily goal F) :
    ((ResourceMeasure.zero goal).polynomialClass).admissible F A :=
  ResourceMeasure.zero_admissible goal F A

/-- A synthetic quadratic observation, with no claim about execution time. -/
def quadraticMeasure : ResourceMeasure goal where
  profile := fun _ _ n => n * n + 3 * n + 7

theorem quadratic_admissible (F : InstanceFamily goal)
    (A : AdversaryFamily goal F) :
    quadraticMeasure.polynomialClass.admissible F A := by
  exact PolynomiallyBounded.add
    (PolynomiallyBounded.add
      (PolynomiallyBounded.mul PolynomiallyBounded.id PolynomiallyBounded.id)
      (PolynomiallyBounded.mul (PolynomiallyBounded.const 3)
        PolynomiallyBounded.id))
    (PolynomiallyBounded.const 7)

example (F : InstanceFamily goal) (A : AdversaryFamily goal F) :
    quadraticMeasure.polynomialClass.admissible F A ↔
      PolynomiallyBounded (quadraticMeasure.profile F A) := by
  rfl

/-- Security here concerns the synthetic resource measure and a dummy goal
whose advantage is zero. It makes no claim about a computation model. -/
theorem quadratic_secure :
    SecureOnWithin goal quadraticMeasure.polynomialClass family := by
  intro A _
  change Negligible (fun _ => 0)
  exact Negligible.zero

example : ResourceMeasure reindexedGoal := ResourceMeasure.zero reindexedGoal

example : SecureOnWithin reindexedGoal
    (ResourceMeasure.zero reindexedGoal).polynomialClass
    reindexedFamily := by
  intro A _
  change Negligible (fun _ => 0)
  exact Negligible.zero

end Foundation.Examples.ResourceMeasure
