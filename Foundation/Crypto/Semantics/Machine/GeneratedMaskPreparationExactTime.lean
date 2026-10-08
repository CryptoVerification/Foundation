import Foundation.Crypto.Semantics.Machine.GeneratedMaskPreparation
import Foundation.Crypto.Semantics.Machine.GeneratedRequestExactTime
import Foundation.Crypto.Semantics.Machine.BackwardErasureExactClock
import Foundation.Crypto.Semantics.Machine.NativeAppendFirstArrivalTime

/-! Exact first-halt times through plaintext erasure and packet rewind.
All stages run from their actual inherited tapes; canonical inputs are
used only to transfer the already proved first-arrival time. -/
namespace Machine.GeneratedMaskPreparation
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem erased_firstArrival_fixed_time (message : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (erased.component.firstArrival.procedure.execution.costed message).support) :
    result.2 = 19 * message.length + 16 := by
  have h : result.2 = (15 * message.length + 12) + (4 * message.length + 3) + 1 := by
    apply GeneratedRequest.link.appendEquivalent_firstArrival_fixed_time
      NativeBackwardErasure.inputComponent eraseInput erase_handoff
      (fun message => 4 * message.length + 3) (fun _ _ _ => Nat.le_refl _)
      message (15 * message.length + 12) (4 * message.length + 3) _ _ _ result hResult
    · rw [GeneratedRequest.budget]
    · intro original hOriginal
      rw [GeneratedRequest.firstArrival_joint, PMF.mem_support_map_iff] at hOriginal
      obtain ⟨state, _, rfl⟩ := hOriginal
      rfl
    · intro middle _ original hOriginal
      rw [NativeBackwardErasure.input_firstArrival_joint, PMF.mem_support_pure_iff] at hOriginal
      subst original
      rfl
  omega

theorem firstArrival_fixed_time (message : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (link.component.firstArrival.procedure.execution.costed message).support) :
    result.2 = 25 * message.length + 23 := by
  have h : result.2 = (19 * message.length + 16) + (6 * message.length + 6) + 1 := by
    apply erased.appendEquivalent_firstArrival_fixed_time
      NativeBitstringRewind.outputComponent rewindInput rewind_handoff
      (fun message => 6 * message.length + 6) (fun message middle _ => rewind_bounded message middle)
      message (19 * message.length + 16) (6 * message.length + 6) _ _ _ result hResult
    · rw [erased_budget]
    · exact erased_firstArrival_fixed_time message
    · intro middle _ original hOriginal
      rw [NativeBitstringRewind.output_firstArrival_joint, PMF.mem_support_pure_iff] at hOriginal
      subst original
      simp only [rewindInput, List.length_append, FlaggedBlockXor.request_length, Foundation.Symmetric.Bits.length_toList]
      omega
  omega

theorem firstArrival_joint (message : List Bool) :
    link.component.firstArrival.procedure.execution.costed message =
      (link.native.execution.semantics message).map (fun state => (state, 25 * message.length + 23)) := by
  have h := link.component.firstArrival_joint_of_fixed_time message
    (25 * message.length + 23) (firstArrival_fixed_time message)
  change _ = ((link.native.execution.semantics message).map id).map _ at h
  simpa only [PMF.map_id] using h

end Machine.GeneratedMaskPreparation
