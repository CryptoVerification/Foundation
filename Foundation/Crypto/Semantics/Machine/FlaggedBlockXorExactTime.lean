import Foundation.Crypto.Semantics.Machine.FlaggedBlockXorComponent
import Foundation.Crypto.Semantics.Machine.NativeAdjacentTime

/-! The existing mask program stops at exactly 24n+8 transitions.
Reuse its phase execution laws at the immediately preceding active horizon,
rather than assuming that its old fixed-budget certificate is unpadded. -/
namespace Machine.FlaggedBlockXor.Component
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

theorem firstArrival_joint (input : Input) :
    component.firstArrival.procedure.execution.costed input =
      PMF.pure (final input.key input.message, 24 * input.message.length + 8) := by
  have h := component.firstArrival_costed_of_adjacent input (24 * input.message.length + 7)
    (Nat.le_refl _)
    (by
      intro state hState
      rw [timed_eval_eq] at hState
      change state ∈ (evalConfigWithin FlaggedBlockXor.code (initial input.key input.message)
        (24 * input.message.length + 7)).support at hState
      rw [run_before_halt _ _ input.sameLength, PMF.mem_support_pure_iff] at hState
      subst state
      rfl)
    (by
      intro state hState
      rw [timed_eval_eq] at hState
      change state ∈ (evalConfigWithin FlaggedBlockXor.code (initial input.key input.message)
        (24 * input.message.length + 8)).support at hState
      rw [run _ _ input.sameLength, PMF.mem_support_pure_iff] at hState
      subst state
      rfl)
  rw [timed_eval_eq] at h
  change component.firstArrival.procedure.execution.costed input =
    (evalConfigWithin FlaggedBlockXor.code (initial input.key input.message)
      (24 * input.message.length + 8)).map _ at h
  rw [run _ _ input.sameLength, PMF.pure_map] at h
  exact h

theorem firstArrival_fixed_time (input : Input) (result : Configuration × Nat)
    (hResult : result ∈ (component.firstArrival.procedure.execution.costed input).support) :
    result.2 = 24 * input.message.length + 8 := by
  rw [firstArrival_joint, PMF.mem_support_pure_iff] at hResult
  subst result
  rfl

end Machine.FlaggedBlockXor.Component
