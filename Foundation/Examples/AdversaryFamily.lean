import Foundation.Resource.Adversary
import Foundation.Asymptotics.Negligible

open scoped ENNReal

namespace Foundation.Examples.AdversaryFamily

def goal : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun _ _ => Bool
  advantage := fun _ _ _ => 0

def family : InstanceFamily goal := fun _ => ()

def adversary : AdversaryFamily goal family := fun _ => true

example : Nat → ℝ≥0∞ := advantageProfile goal family adversary

example : Negligible (advantageProfile goal family adversary) := by
  change Negligible (fun _ => 0)
  exact Negligible.zero

def allowed : AdversaryClass goal := AdversaryClass.all goal

theorem familyBound : BoundedByOn goal family (fun _ => 0) := by
  intro n A
  exact le_refl _

theorem allowedFamilyBound :
    BoundedByOnWithin goal allowed family (fun _ => 0) :=
  familyBound.within allowed

example : BoundedByOnWithin goal allowed family (fun _ => 1) := by
  apply allowedFamilyBound.mono
  intro _
  exact zero_le

/-- The same family abstraction works after a goal's instance domain is
reindexed. -/
def reindexedGoal : CryptoGoal :=
  goal.reindex (fun _ => Bool) (fun _ _ => ())

def reindexedFamily : InstanceFamily reindexedGoal := fun _ => true

def reindexedAdversary : AdversaryFamily reindexedGoal reindexedFamily :=
  fun _ => false

example : Nat → ℝ≥0∞ :=
  advantageProfile reindexedGoal reindexedFamily reindexedAdversary

end Foundation.Examples.AdversaryFamily
