import Foundation.Crypto.Semantics.Machine.GeneratedRequest
import Foundation.Crypto.Semantics.Machine.RequestExactClock
import Foundation.Crypto.Semantics.Machine.RewindExactClock
import Foundation.Crypto.Semantics.Machine.SamplerExactClock
import Foundation.Crypto.Semantics.Machine.NativeLinkFirstArrivalTime

/-! Exact actual costs of request writing followed by native rewind.
The linked code and physical entry are unchanged. Actual component clocks
transfer through invocation and the typed linker, rather than adding up
only upper bounds or assuming uncharged control transfers. -/
namespace Machine.GeneratedRequest
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

private theorem first_stage_times (message : List Bool) :
    (∀ result, result ∈ (firstLink.first.costed message).support → result.2 = 8 * message.length + 4) ∧
    (∀ middle, middle ∈ (firstLink.first.costed message).support →
      ∀ result, result ∈ (firstLink.second.costed middle.1).support → result.2 = 2 * message.length + 4) := by
  have fixedFirst : ∀ result, result ∈ (firstLink.first.costed message).support → result.2 = 8 * message.length + 4 := by
    apply firstLink.first_fixed_time_of_arrival message (8 * message.length + 4)
    intro result hResult
    change result ∈ (writer.firstArrival.procedure.execution.costed message).support at hResult
    have h := writer.firstArrival_fixed_time_of_clock NativeFlaggedRequest.exactClock message
      (NativeFlaggedRequest.initial_clock_valid ⟨[], [], message⟩)
      (by
        change NativeFlaggedRequest.exactClock.remaining (NativeFlaggedRequest.initial ⟨[], [], message⟩) ≤ 8 * message.length + 4
        rw [NativeFlaggedRequest.initial_clock]) result hResult
    exact h.trans (NativeFlaggedRequest.initial_clock ⟨[], [], message⟩)
  have fixedSecond : ∀ middle, middle ∈ (firstLink.first.costed message).support →
      ∀ result, result ∈ (firstLink.second.costed middle.1).support → result.2 = 2 * message.length + 4 := by
    intro middle hMiddle
    have hLogical := firstLink.first.result_support message middle hMiddle
    rw [firstLink.first_semantics, PMF.mem_support_map_iff] at hLogical
    obtain ⟨output, _, hPair⟩ := hLogical
    have hInput : middle.1.1 = message := (congrArg Prod.fst hPair).symm
    apply firstLink.second_fixed_time_of_arrival middle.1 (2 * message.length + 4)
    intro result hResult
    change result ∈ (NativeBitstringRewind.component.firstArrival.procedure.execution.costed (rewindInput middle.1.1)).support at hResult
    have h := NativeBitstringRewind.firstArrival_fixed_time (rewindInput middle.1.1) result hResult
    simpa only [rewindInput, hInput] using h
  exact ⟨fixedFirst, fixedSecond⟩

theorem first_costed (message : List Bool) :
    firstLink.native.execution.costed message = PMF.pure (firstFinish message, 10 * message.length + 9) := by
  obtain ⟨fixedFirst, fixedSecond⟩ := first_stage_times message
  have h := firstLink.joint_of_fixed_time message (8 * message.length + 4) (2 * message.length + 4) fixedFirst fixedSecond
  rw [first_semantics, PMF.pure_map] at h
  simpa only [show 8 * message.length + 4 + (2 * message.length + 4) + 1 = 10 * message.length + 9 by omega] using h

theorem first_firstArrival_costed (message : List Bool) :
    firstLink.component.firstArrival.procedure.execution.costed message =
      PMF.pure (firstFinish message, 10 * message.length + 9) := by
  obtain ⟨fixedFirst, fixedSecond⟩ := first_stage_times message
  rw [firstLink.firstArrival_costed_eq_of_fixed_time message
    (8 * message.length + 4) (2 * message.length + 4)
    (by change 8 * message.length + 4 + (2 * message.length + 4) ≤ _; omega)
    fixedFirst fixedSecond, first_costed]

private theorem stage_times (message : List Bool) :
    (∀ result, result ∈ (link.first.costed message).support → result.2 = 10 * message.length + 9) ∧
    (∀ middle, middle ∈ (link.first.costed message).support →
      ∀ result, result ∈ (link.second.costed middle.1).support → result.2 = 5 * message.length + 2) := by
  constructor
  · apply link.first_fixed_time_of_arrival message (10 * message.length + 9)
    intro result hResult
    change result ∈ (firstLink.component.firstArrival.procedure.execution.costed message).support at hResult
    rw [first_firstArrival_costed, PMF.mem_support_pure_iff] at hResult
    subst result
    rfl
  · intro middle hMiddle
    have hLogical := link.first.result_support message middle hMiddle
    rw [link.first_semantics, PMF.mem_support_map_iff] at hLogical
    obtain ⟨output, _, hPair⟩ := hLogical
    have hInput : middle.1.1 = message := (congrArg Prod.fst hPair).symm
    apply link.second_fixed_time_of_arrival middle.1 (5 * message.length + 2)
    intro result hResult
    let actual := link.adapt middle.1.1 middle.1.2
    have hLogicalInput : actual.logical = samplerInput message := by
      change (firstLink.equivalentInput NativeContextualSampler.component
        (fun message _ => samplerInput message) sampler_handoff middle.1.1 middle.1.2).logical = _
      rw [firstLink.equivalentInput_logical, hInput]
    change result ∈ (NativeContextualSampler.component.equivalentEntries.firstArrival.procedure.execution.costed actual).support at hResult
    have h := NativeContextualSampler.component.equivalentEntries_firstArrival_fixed_time_of_clock
      NativeContextualSampler.exactClock actual
      (by rw [hLogicalInput]; exact NativeContextualSampler.initial_clock_valid (samplerInput message))
      (by
        rw [hLogicalInput]
        change NativeContextualSampler.exactClock.remaining (NativeContextualSampler.initial (samplerInput message)) ≤ _
        rw [NativeContextualSampler.initial_clock]
        exact Nat.le_refl _) result hResult
    rw [hLogicalInput] at h
    exact h.trans (NativeContextualSampler.initial_clock (samplerInput message))

theorem firstArrival_costed_eq (message : List Bool) :
    link.component.firstArrival.procedure.execution.costed message = link.native.execution.costed message := by
  obtain ⟨fixedFirst, fixedSecond⟩ := stage_times message
  apply link.firstArrival_costed_eq_of_fixed_time message
    (10 * message.length + 9) (5 * message.length + 2) _ fixedFirst fixedSecond
  rw [first_budget]
  exact Nat.le_refl _

theorem firstArrival_joint (message : List Bool) :
    link.component.firstArrival.procedure.execution.costed message =
      (link.native.execution.semantics message).map (fun state => (state, 15 * message.length + 12)) := by
  obtain ⟨fixedFirst, fixedSecond⟩ := stage_times message
  rw [firstArrival_costed_eq]
  have h := link.joint_of_fixed_time message
    (10 * message.length + 9) (5 * message.length + 2) fixedFirst fixedSecond
  simpa only [show 10 * message.length + 9 + (5 * message.length + 2) + 1 = 15 * message.length + 12 by omega] using h

theorem firstArrival_key_time (message : List Bool) :
    (link.component.firstArrival.procedure.execution.costed message).map
      (fun result => (readKey message result.1, result.2)) =
      (uniform (Foundation.Symmetric.Bits message.length)).map
        (fun key => (key, 15 * message.length + 12)) := by
  rw [firstArrival_joint, PMF.map_comp, ← key_distribution message, PMF.map_comp]
  rfl

end Machine.GeneratedRequest
