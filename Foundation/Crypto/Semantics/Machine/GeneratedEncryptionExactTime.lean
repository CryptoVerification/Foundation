import Foundation.Crypto.Semantics.Machine.GeneratedMaskPreparationExactTime
import Foundation.Crypto.Semantics.Machine.FlaggedBlockXorExactTime
import Foundation.Crypto.Semantics.Machine.GeneratedEncryptionFirstArrival

/-! Actual first-halt time of fresh-key encryption, including preparation,
masking, cleanup, and every linker halt. Timing-aware secrecy below uses
the actual ciphertext/time joint distribution, without a joint-law premise. -/
namespace Machine.GeneratedBlockEncryption
open Foundation.Probability TimedExecution Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem masked_firstArrival_fixed_time (message : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (masked.component.firstArrival.procedure.execution.costed message).support) :
    result.2 = 49 * message.length + 32 := by
  have h : result.2 = (25 * message.length + 23) + (24 * message.length + 8) + 1 := by
    apply GeneratedMaskPreparation.link.appendEquivalent_firstArrival_fixed_time
      FlaggedBlockXor.Component.component.swapTapes maskInput mask_handoff
      (fun message => 24 * message.length + 8) (fun _ _ _ => Nat.le_refl _)
      message (25 * message.length + 23) (24 * message.length + 8) _ _ _ result hResult
    · rw [GeneratedMaskPreparation.budget]
    · exact GeneratedMaskPreparation.firstArrival_fixed_time message
    · intro middle _
      apply FlaggedBlockXor.Component.component.swapTapes_firstArrival_fixed_time
      exact FlaggedBlockXor.Component.firstArrival_fixed_time (maskInput message middle)
  omega

theorem arrival_fixed_time (message : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (arrival.procedure.execution.costed message).support) :
    result.2 = 61 * message.length + 40 := by
  have h : result.2 = (49 * message.length + 32) + (12 * message.length + 7) + 1 := by
    apply masked.appendEquivalent_firstArrival_fixed_time
      NativeBackwardErasure.component eraseInput erase_handoff
      (fun message => 12 * message.length + 7) (fun message middle _ => erase_bounded message middle)
      message (49 * message.length + 32) (12 * message.length + 7) _ _ _ result hResult
    · rw [masked_budget]
    · exact masked_firstArrival_fixed_time message
    · intro middle _ original hOriginal
      rw [NativeBackwardErasure.firstArrival_joint, PMF.mem_support_pure_iff] at hOriginal
      subst original
      simp only [eraseInput, List.length_append, FlaggedBlockXor.request_length, Bits.length_toList]
      omega
  omega

theorem arrival_joint (message : List Bool) :
    arrival.procedure.execution.costed message =
      (link.native.execution.semantics message).map (fun state => (state, 61 * message.length + 40)) := by
  change link.component.firstArrival.procedure.execution.costed message = _
  have h := link.component.firstArrival_joint_of_fixed_time message
    (61 * message.length + 40) (arrival_fixed_time message)
  change _ = ((link.native.execution.semantics message).map id).map _ at h
  simpa only [PMF.map_id] using h

theorem arrival_ciphertext_time_uniform {width : Nat} (message : Bits width) :
    (arrival.procedure.execution.costed message.toList).map
      (fun result => (result.1.inputTape.bits, result.2)) =
      ((uniform (Bits width)).map Bits.toList).map (fun ciphertext => (ciphertext, 61 * width + 40)) := by
  rw [arrival_joint, Bits.length_toList, PMF.map_comp, ← ciphertext_uniform message, PMF.map_comp]
  rfl

theorem arrival_time_perfect_secrecy {width : Nat} (left right : Bits width)
    {Observed : Type u} (context : Nat → Program) (horizon : Nat → Nat)
    (observe : Nat → Configuration → Observed)
    (invariant : ∀ time first second, first.Equivalent second → observe time first = observe time second) :
    (arrival.procedure.execution.costed left.toList).bind (fun result =>
      (evalConfigWithin (context result.2) (result.1.resumeAt 0) (horizon result.2)).map (observe result.2)) =
    (arrival.procedure.execution.costed right.toList).bind (fun result =>
      (evalConfigWithin (context result.2) (result.1.resumeAt 0) (horizon result.2)).map (observe result.2)) := by
  apply arrival_time_secrecy_of_joint_eq left right _ context horizon observe invariant
  rw [arrival_ciphertext_time_uniform, arrival_ciphertext_time_uniform]

theorem arrival_boundary_perfect_secrecy {width : Nat} (left right : Bits width)
    {Observed : Type u} (context : Nat → Program) (boundary : Nat → Configuration → Bool)
    (boundaryInvariant : ∀ time first second, first.Equivalent second → boundary time first = boundary time second)
    (fuel : Nat → Nat) (observe : Nat → Configuration × Nat → Observed)
    (invariant : ∀ time first second elapsed, first.Equivalent second →
      observe time (first, elapsed) = observe time (second, elapsed)) :
    (arrival.procedure.execution.costed left.toList).bind (fun result =>
      (runToBoundary (stepPMF (context result.2)) (boundary result.2) (fuel result.2)
        (result.1.resumeAt 0)).map (observe result.2)) =
    (arrival.procedure.execution.costed right.toList).bind (fun result =>
      (runToBoundary (stepPMF (context result.2)) (boundary result.2) (fuel result.2)
        (result.1.resumeAt 0)).map (observe result.2)) := by
  rw [arrival_boundary_continuation left.toList context boundary boundaryInvariant fuel observe invariant,
    arrival_boundary_continuation right.toList context boundary boundaryInvariant fuel observe invariant,
    arrival_ciphertext_time_uniform, arrival_ciphertext_time_uniform]

theorem run_arrival_ciphertext_time_uniform {width : Nat} (message : Bits width)
    (horizon : Nat) (bounded : 61 * width + 40 ≤ horizon) :
    (runToBoundary (stepPMF link.code) Configuration.halted horizon (Configuration.initial message.toList)).map
      (fun result => (result.1.inputTape.bits, result.2)) =
      ((uniform (Bits width)).map Bits.toList).map (fun ciphertext => (ciphertext, 61 * width + 40)) := by
  rw [arrival_costed_horizon message.toList horizon (by simpa only [Bits.length_toList] using bounded)]
  exact arrival_ciphertext_time_uniform message

end Machine.GeneratedBlockEncryption
