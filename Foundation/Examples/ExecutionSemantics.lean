import Foundation.Resource.ExecutionSemantics
import Foundation.Examples.FiniteProgram

namespace Foundation.Examples.ExecutionSemantics

open Foundation.Examples.UniformAdversary
  (goal family model)
open Foundation.Examples.FiniteProgram
  (description)

/-- One natural-number program yields `prog + n` for every parameter `n`. -/
def execution : model.ExecutionSemantics where
  execute := fun _ prog n => (show Nat from prog) + n
  realizes := by
    intro F prog
    rfl

example : (fun n => execution.execute family (3 : Nat) n) =
    model.realize family (3 : Nat) :=
  execution.realizes family (3 : Nat)

example (n : Nat) :
    description.encode family (3 : Nat) = [true, true, true] ∧
      execution.execute family (3 : Nat) n = 3 + n := by
  constructor <;> rfl

end Foundation.Examples.ExecutionSemantics
