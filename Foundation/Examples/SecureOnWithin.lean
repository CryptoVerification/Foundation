import Foundation.Security.Asymptotic
import Foundation.Examples.AdversaryFamily

namespace Foundation.Examples.SecureOnWithin

open Foundation.Examples.AdversaryFamily
  (goal family allowed allowedFamilyBound familyBound
   reindexedGoal reindexedFamily)

/-- `all` admits every family, so this example checks unrestricted security
of a dummy goal whose advantage is always zero. -/
theorem allSecure : SecureOnWithin goal (AdversaryClass.all goal) family := by
  intro A _
  change Negligible (fun _ => 0)
  exact Negligible.zero

example : SecureOnWithin goal allowed family :=
  SecureOnWithin.of_boundedBy allowedFamilyBound Negligible.zero

example : SecureOnWithin goal allowed family :=
  SecureOnWithin.of_boundedByOn familyBound Negligible.zero allowed

/-- A dummy class that admits only families choosing `true` at parameter zero. -/
def chosen : AdversaryClass goal where
  admissible := fun _ A => A 0 = true

theorem chosenSecure : SecureOnWithin goal chosen family := by
  apply SecureOnWithin.monoClass (C := AdversaryClass.all goal)
    (D := chosen) (F := family) ?_ allSecure
  intro G A _
  trivial

example : SecureOnWithin reindexedGoal
    (AdversaryClass.all reindexedGoal) reindexedFamily := by
  intro A _
  change Negligible (fun _ => 0)
  exact Negligible.zero

end Foundation.Examples.SecureOnWithin
