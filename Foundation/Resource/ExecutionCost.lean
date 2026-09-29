import Foundation.Resource.ExecutionSemantics
import Foundation.Resource.ProgramMeasure

universe u v w

namespace UniformAdversaryModel

/-- A finite run of exactly `k` transitions of an abstract step relation. -/
inductive ExecutionSteps {State : Type w} (step : State → State → Prop) :
    Nat → State → State → Prop where
  | zero (s : State) : ExecutionSteps step 0 s s
  | succ {k : Nat} {s t u : State}
      (prior : ExecutionSteps step k s t) (last : step t u) :
      ExecutionSteps step (k + 1) s u

/-- A run of the execution semantics with an explicit transition trace.
`runtime` is the number of transitions in that run, relative to the supplied
step relation. This interface does not fix a concrete machine or interpret
the finite program code. -/
structure ExecutionSemantics.ExecutionCost {P : CryptoGoal.{u}}
    {M : UniformAdversaryModel.{u, v} P}
    (E : M.ExecutionSemantics) where
  State : (F : InstanceFamily P) → M.Program F → Nat → Type w
  initial : ∀ (F : InstanceFamily P) (prog : M.Program F) (n : Nat),
    State F prog n
  step : ∀ (F : InstanceFamily P) (prog : M.Program F) (n : Nat),
    State F prog n → State F prog n → Prop
  final : ∀ (F : InstanceFamily P) (prog : M.Program F) (n : Nat),
    State F prog n
  runtime : ∀ (F : InstanceFamily P) (_prog : M.Program F), Nat → Nat
  output : ∀ (F : InstanceFamily P) (prog : M.Program F) (n : Nat),
    State F prog n → P.Adversary n (F n)
  valid : ∀ (F : InstanceFamily P) (prog : M.Program F) (n : Nat),
    ExecutionSteps (step F prog n) (runtime F prog n)
      (initial F prog n) (final F prog n)
  output_eq : ∀ (F : InstanceFamily P) (prog : M.Program F) (n : Nat),
    output F prog n (final F prog n) = E.execute F prog n

namespace ExecutionSemantics.ExecutionCost

/-- The resource measure that observes precisely the transition count of a
validated execution, rather than an arbitrary program resource. -/
def toProgramResourceMeasure {P : CryptoGoal.{u}}
    {M : UniformAdversaryModel.{u, v} P}
    {E : M.ExecutionSemantics} (C : E.ExecutionCost) :
    ProgramResourceMeasure M where
  profile := C.runtime

end ExecutionSemantics.ExecutionCost

end UniformAdversaryModel
