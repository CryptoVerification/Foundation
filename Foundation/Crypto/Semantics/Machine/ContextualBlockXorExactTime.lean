import Foundation.Crypto.Semantics.Machine.ContextualBlockXorResources
import Foundation.Crypto.Semantics.Machine.NativeAdjacentTime

/-! Actual first-halt timing of contextual masking. Preserved context may
contain nonblank cells, so the result is proved from execution phases,
not from equivalence with the context-free entry. -/
namespace Machine.FlaggedBlockXor.Contextual
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

theorem firstArrival_joint (input : Input) :
    component.firstArrival.procedure.execution.costed input =
      PMF.pure (finish input, 24 * input.message.length + 8) := by
  have h := component.firstArrival_costed_of_adjacent input (24 * input.message.length + 7)
    (Nat.le_refl _)
    (by
      intro state hState
      rw [timed_eval_eq] at hState
      change state ∈ (evalConfigWithin code (initial input) (24 * input.message.length + 7)).support at hState
      rw [run_before_halt, PMF.mem_support_pure_iff] at hState
      subst state
      rfl)
    (by
      intro state hState
      rw [timed_eval_eq] at hState
      change state ∈ (evalConfigWithin code (initial input) (24 * input.message.length + 8)).support at hState
      rw [run, PMF.mem_support_pure_iff] at hState
      subst state
      rfl)
  rw [timed_eval_eq] at h
  change component.firstArrival.procedure.execution.costed input =
    (evalConfigWithin code (initial input) (24 * input.message.length + 8)).map _ at h
  rw [run, PMF.pure_map] at h
  exact h

theorem firstArrival_fixed_time (input : Input) (result : Configuration × Nat)
    (hResult : result ∈ (component.firstArrival.procedure.execution.costed input).support) :
    result.2 = 24 * input.message.length + 8 := by
  rw [firstArrival_joint, PMF.mem_support_pure_iff] at hResult
  subst result
  rfl

end Machine.FlaggedBlockXor.Contextual
