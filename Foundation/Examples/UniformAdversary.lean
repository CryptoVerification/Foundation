import Foundation.Resource.Uniformity
import Foundation.Security.Asymptotic

namespace Foundation.Examples.UniformAdversary

/-- A dummy goal with zero advantage and natural-number adversaries. -/
def goal : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun _ _ => Nat
  advantage := fun _ _ _ => 0

def family : InstanceFamily goal := fun _ => ()

/-- One natural-number program parameter generates the whole family by
the rule `prog + n`. It cannot realize every arbitrary indexed family. -/
def model : UniformAdversaryModel goal where
  Program := fun _ => Nat
  realize := fun _ prog n => prog + n

example : model.Realizable family (model.realize family (3 : Nat)) := by
  exact ⟨(3 : Nat), rfl⟩

example : model.uniformClass.admissible family (model.realize family (3 : Nat)) := by
  exact ⟨(3 : Nat), rfl⟩

theorem constantZero_not_realizable :
    ¬ model.Realizable family (fun _ => (0 : Nat)) := by
  intro ⟨prog, h⟩
  have h1 := congrFun h 1
  change (show Nat from prog) + 1 = 0 at h1
  omega

/-- Security here quantifies only over families realized by `model`.
The zero advantage makes every such profile negligible. -/
theorem uniform_secure : SecureOnWithin goal model.uniformClass family := by
  intro A _
  change Negligible (fun _ => 0)
  exact Negligible.zero

/-- The same interface applies to a reindexed goal without special laws. -/
def reindexedGoal : CryptoGoal :=
  goal.reindex (fun _ => Bool) (fun _ _ => ())

example : UniformAdversaryModel reindexedGoal where
  Program := fun _ => Nat
  realize := fun _ prog n => prog + n

end Foundation.Examples.UniformAdversary
