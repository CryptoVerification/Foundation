import Foundation.Resource.ExecutionCost
import Foundation.Examples.ExecutionSemantics

namespace Foundation.Examples.ExecutionCost

open UniformAdversaryModel
open Foundation.Examples.UniformAdversary
  (goal family model)
open Foundation.Examples.ExecutionSemantics
  (execution)

private theorem increment_steps (k : Nat) :
    ExecutionSteps (fun s t : Nat => t = s + 1) k 0 k := by
  induction k with
  | zero => exact ExecutionSteps.zero 0
  | succ k ih =>
      exact ExecutionSteps.succ ih (by rfl)

/-- A toy unary run: state starts at zero, increments once per transition,
and stops at `prog + n`. Its cost is an actual count for this toy relation. -/
def toyCost : execution.ExecutionCost where
  State := fun _ _ _ => Nat
  initial := fun _ _ _ => 0
  step := fun _ _ _ s t => t = s + 1
  final := fun _ prog n => (show Nat from prog) + n
  runtime := fun _ prog n => (show Nat from prog) + n
  output := fun _ _ _ s => s
  valid := by
    intro F prog n
    exact increment_steps _
  output_eq := by
    intro F prog n
    rfl

example (n : Nat) : toyCost.runtime family (3 : Nat) n = 3 + n := by rfl

example (F : InstanceFamily goal) (prog : model.Program F) :
    PolynomiallyBounded
      ((toyCost.toProgramResourceMeasure).profile F prog) := by
  exact PolynomiallyBounded.add
    (PolynomiallyBounded.const (show Nat from prog)) PolynomiallyBounded.id

end Foundation.Examples.ExecutionCost
