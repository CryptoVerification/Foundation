import Foundation.Crypto.Semantics.Machine.NativeRequestResources
import Foundation.Crypto.Semantics.Machine.NativeBackwardErasure
import Foundation.Crypto.Semantics.Machine.NativeEquivalentObservation
import Foundation.Crypto.Semantics.Machine.ConsumedInputErasure
import Foundation.Crypto.Semantics.Machine.TapeReading

/-! Continue a generated request by actually erasing its original plaintext
and rewinding the output request/key packet. The uniform key is retained in
the actual output tape. This file never installs a secret by free loading. -/
namespace Machine.GeneratedMaskPreparation
open Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

def eraseInput (message : List Bool) (middle : Configuration) : NativeBackwardErasure.Input :=
  {bits := message, other := ResponseExport.endTape
    (FlaggedBlockXor.request message ++ (GeneratedRequest.readKey message middle).toList)}

theorem erase_handoff (message : List Bool) (middle : Configuration)
    (hMiddle : middle ∈ (GeneratedRequest.link.native.execution.semantics message).support) :
    (middle.resumeAt 0).Equivalent (NativeBackwardErasure.inputComponent.procedure.execution.entry (eraseInput message middle)) := by
  have h := (GeneratedRequest.exit_equivalent message middle hMiddle).resumeAt 0
  apply h.trans
  refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
  exact ConsumedInputErasure.outer_blank message

noncomputable def erased : TypedNativeComposition.Link GeneratedRequest.link.native
    NativeBackwardErasure.inputComponent.equivalentEntries.procedure :=
  GeneratedRequest.link.appendEquivalent NativeBackwardErasure.inputComponent eraseInput erase_handoff
    (fun message => 4 * message.length + 3) (fun _ _ _ => Nat.le_refl _)

theorem erased_code_length : erased.code.length = 39 := by
  rw [erased.code_length]
  change GeneratedRequest.link.code.length + eraseOutputBlock.swapTapes.length + 3 = 39
  rw [GeneratedRequest.code_length, Program.swapTapes_length]
  rfl

theorem erased_budget (message : List Bool) : erased.native.execution.budget message = 19 * message.length + 16 := by
  rw [erased.budget, GeneratedRequest.budget]
  change 15 * message.length + 12 + (4 * message.length + 3) + 1 = _
  omega

def erasedExit (message : List Bool) (key : Bits message.length) : Configuration :=
  { pc := 38,
    inputTape := {right := List.replicate (message.length + 1) none},
    outputTape := ResponseExport.endTape (FlaggedBlockXor.request message ++ key.toList), halted := true }

theorem erased_supported_exit (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (erased.native.execution.semantics message).support) :
    ∃ key : Bits message.length, target.Equivalent (erasedExit message key) := by
  rw [erased.semantics, PMF.mem_support_bind_iff] at hTarget
  obtain ⟨middle, _, hTarget⟩ := hTarget
  rw [PMF.mem_support_map_iff] at hTarget
  obtain ⟨last, hLast, rfl⟩ := hTarget
  have hPure : NativeBackwardErasure.inputComponent.procedure.execution.semantics
      (erased.adapt message middle).logical = PMF.pure (NativeBackwardErasure.finish (eraseInput message middle)) := by
    change NativeBackwardErasure.inputComponent.procedure.execution.semantics
      (GeneratedRequest.link.equivalentInput NativeBackwardErasure.inputComponent eraseInput erase_handoff message middle).logical = _
    rw [GeneratedRequest.link.equivalentInput_logical]
    rfl
  have h := NativeBackwardErasure.inputComponent.equivalentEntries_exit _
    (NativeBackwardErasure.finish (eraseInput message middle)) hPure last hLast
  refine ⟨GeneratedRequest.readKey message middle, ?_⟩
  have hh := (h.resumeAt 38).withHalted true
  change ({last.resumeAt 38 with halted := true} : Configuration).Equivalent
    ({
      pc := 38, inputTape := {right := List.replicate (message.reverse.length + 1) none ++ []},
      outputTape := ResponseExport.endTape (FlaggedBlockXor.request message ++
        (GeneratedRequest.readKey message middle).toList), halted := true} : Configuration) at hh
  change ({last.resumeAt 38 with halted := true} : Configuration).Equivalent
    ({
      pc := 38, inputTape := {right := List.replicate (message.length + 1) none},
      outputTape := ResponseExport.endTape (FlaggedBlockXor.request message ++
        (GeneratedRequest.readKey message middle).toList), halted := true} : Configuration)
  simpa only [List.length_reverse, List.append_nil] using hh

theorem erased_key_distribution (message : List Bool) :
    (erased.native.execution.semantics message).map (GeneratedRequest.readKey message) = uniform (Bits message.length) := by
  have h := GeneratedRequest.link.appendEquivalent_observe NativeBackwardErasure.inputComponent eraseInput erase_handoff
    (fun message => 4 * message.length + 3) (fun _ _ _ => Nat.le_refl _)
    (GeneratedRequest.readKey message) (GeneratedRequest.readKey_equivalent message) message
  change (erased.native.execution.semantics message).map (GeneratedRequest.readKey message) = _ at h
  rw [h]
  change (GeneratedRequest.link.native.execution.semantics message).bind (fun middle =>
    (PMF.pure (NativeBackwardErasure.finish (eraseInput message middle))).map
      (fun result => GeneratedRequest.readKey message {result.swapTapes.resumeAt 38 with halted := true})) = _
  simp only [PMF.pure_map]
  change (GeneratedRequest.link.native.execution.semantics message).bind (fun middle =>
    PMF.pure (GeneratedRequest.readKey message (NativeContextualSampler.finish (GeneratedRequest.samplerInput message)
      (GeneratedRequest.readKey message middle)))) = _
  simp only [GeneratedRequest.readKey_finish]
  exact GeneratedRequest.key_distribution message

def rewindInput (message : List Bool) (middle : Configuration) : NativeBitstringRewind.Input :=
  {bits := FlaggedBlockXor.request message ++ (GeneratedRequest.readKey message middle).toList,
    other := {}}

theorem erased_exit_equivalent (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (erased.native.execution.semantics message).support) :
    target.Equivalent (erasedExit message (GeneratedRequest.readKey message target)) := by
  obtain ⟨key, h⟩ := erased_supported_exit message target hTarget
  have hKey := GeneratedRequest.readKey_equivalent message target (erasedExit message key) h
  change GeneratedRequest.readKey message target = GeneratedRequest.readKey message
    (NativeContextualSampler.finish (GeneratedRequest.samplerInput message) key) at hKey
  rw [GeneratedRequest.readKey_finish] at hKey
  rw [hKey]
  exact h

theorem rewind_handoff (message : List Bool) (middle : Configuration)
    (hMiddle : middle ∈ (erased.native.execution.semantics message).support) :
    (middle.resumeAt 0).Equivalent (NativeBitstringRewind.outputComponent.procedure.execution.entry (rewindInput message middle)) := by
  have h := (erased_exit_equivalent message middle hMiddle).resumeAt 0
  apply h.trans
  exact ⟨rfl, rfl, Tape.blank_padding_equivalent [] _, Tape.Equivalent.refl _⟩

theorem rewind_bounded (message : List Bool) (middle : Configuration) :
    NativeBitstringRewind.outputComponent.procedure.execution.budget (rewindInput message middle) ≤
      6 * message.length + 6 := by
  change 2 * (FlaggedBlockXor.request message ++ (GeneratedRequest.readKey message middle).toList).length + 4 ≤ _
  simp only [List.length_append, FlaggedBlockXor.request_length, Bits.length_toList]
  omega

noncomputable def link : TypedNativeComposition.Link erased.native
    NativeBitstringRewind.outputComponent.equivalentEntries.procedure :=
  erased.appendEquivalent NativeBitstringRewind.outputComponent rewindInput rewind_handoff
    (fun message => 6 * message.length + 6) (fun message middle _ => rewind_bounded message middle)

theorem code_length : link.code.length = 46 := by
  rw [link.code_length]
  change erased.code.length + rewindBitstring.swapTapes.length + 3 = 46
  rw [erased_code_length, Program.swapTapes_length]
  rfl

theorem budget (message : List Bool) : link.native.execution.budget message = 25 * message.length + 23 := by
  rw [link.budget, erased_budget]
  change 19 * message.length + 16 + (6 * message.length + 6) + 1 = _
  omega

def canonicalExit (message : List Bool) (key : Bits message.length) : Configuration :=
  {pc := 45, outputTape := (rewindBitstringFinish (FlaggedBlockXor.request message ++ key.toList) {}).inputTape,
    halted := true}

theorem readKey_canonicalExit (message : List Bool) (key : Bits message.length) :
    GeneratedRequest.readKey message (canonicalExit message key) = key := by
  have hBits := (rewindBitstringFinish_input_equivalent (FlaggedBlockXor.request message ++ key.toList) {}).bits
  have hPacket : (canonicalExit message key).outputBits = FlaggedBlockXor.request message ++ key.toList := by
    change (rewindBitstringFinish (FlaggedBlockXor.request message ++ key.toList) {}).inputTape.bits = _
    simpa only [Tape.bits_ofBits] using hBits
  funext index
  change (canonicalExit message key).outputBits[(FlaggedBlockXor.request message).length + index.val]?.getD false = key index
  rw [hPacket]
  simp [Bits.toList]

theorem supported_exit (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics message).support) :
    ∃ key : Bits message.length, target.Equivalent (canonicalExit message key) := by
  rw [link.semantics, PMF.mem_support_bind_iff] at hTarget
  obtain ⟨middle, _, hTarget⟩ := hTarget
  rw [PMF.mem_support_map_iff] at hTarget
  obtain ⟨last, hLast, rfl⟩ := hTarget
  have hPure : NativeBitstringRewind.outputComponent.procedure.execution.semantics
      (link.adapt message middle).logical = PMF.pure (NativeBitstringRewind.finish (rewindInput message middle)) := by
    change NativeBitstringRewind.outputComponent.procedure.execution.semantics
      (erased.equivalentInput NativeBitstringRewind.outputComponent rewindInput rewind_handoff message middle).logical = _
    rw [erased.equivalentInput_logical]
    rfl
  have h := NativeBitstringRewind.outputComponent.equivalentEntries_exit _
    (NativeBitstringRewind.finish (rewindInput message middle)) hPure last hLast
  exact ⟨GeneratedRequest.readKey message middle, (h.resumeAt 45).withHalted true⟩

theorem exit_equivalent (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics message).support) :
    target.Equivalent (canonicalExit message (GeneratedRequest.readKey message target)) := by
  obtain ⟨key, h⟩ := supported_exit message target hTarget
  have hKey := GeneratedRequest.readKey_equivalent message target (canonicalExit message key) h
  rw [readKey_canonicalExit] at hKey
  rw [hKey]
  exact h

theorem key_distribution (message : List Bool) :
    (link.native.execution.semantics message).map (GeneratedRequest.readKey message) = uniform (Bits message.length) := by
  have h := erased.appendEquivalent_observe NativeBitstringRewind.outputComponent rewindInput rewind_handoff
    (fun message => 6 * message.length + 6) (fun message middle _ => rewind_bounded message middle)
    (GeneratedRequest.readKey message) (GeneratedRequest.readKey_equivalent message) message
  change (link.native.execution.semantics message).map (GeneratedRequest.readKey message) = _ at h
  rw [h]
  change (erased.native.execution.semantics message).bind (fun middle =>
    (PMF.pure (NativeBitstringRewind.finish (rewindInput message middle))).map
      (fun result => GeneratedRequest.readKey message {result.swapTapes.resumeAt 45 with halted := true})) = _
  simp only [PMF.pure_map]
  change (erased.native.execution.semantics message).bind (fun middle =>
    PMF.pure (GeneratedRequest.readKey message (canonicalExit message (GeneratedRequest.readKey message middle)))) = _
  simp only [readKey_canonicalExit]
  exact erased_key_distribution message

theorem operational : TimedExecution.Procedure.Operational link.native.execution := link.operational

end Machine.GeneratedMaskPreparation
