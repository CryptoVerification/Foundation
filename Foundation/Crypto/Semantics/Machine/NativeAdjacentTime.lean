import Foundation.Crypto.Semantics.Machine.NativeFirstArrival
import Foundation.Crypto.Semantics.BoundaryExactTime

/-! Exact first-halt laws from execution at adjacent horizons. An existing
termination certificate may have a larger upper bound than the exact time.
The rule preserves the full final state/time law and adds no code. -/
namespace Machine.NativeComponent
open Foundation.Probability TimedExecution
universe u v
variable {Input : Type u} {Output : Type v} (P : NativeComponent Input Output)

theorem firstArrival_costed_of_adjacent (input : Input) (before : Nat)
    (bounded : before + 1 ≤ P.procedure.execution.budget input)
    (active : ∀ state ∈ (eval (stepPMF P.procedure.code) before
      (P.procedure.execution.entry input)).support, state.halted = false)
    (complete : ∀ state ∈ (eval (stepPMF P.procedure.code) (before + 1)
      (P.procedure.execution.entry input)).support, state.halted = true) :
    P.firstArrival.procedure.execution.costed input =
      (eval (stepPMF P.procedure.code) (before + 1) (P.procedure.execution.entry input)).map
        (fun state => (state, before + 1)) := by
  rw [P.firstArrival_costed,
    runToBoundary_fuel_stable _ _ (before + 1) _ _ bounded
      (fun result hResult => runToBoundary_completes _ _ _ _ complete result hResult)]
  exact runToBoundary_joint_of_adjacent _ _ _ before
    (fun state hHalt => by simp [stepPMF, next, hHalt]) active complete

end Machine.NativeComponent
