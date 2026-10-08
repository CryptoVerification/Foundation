import Foundation.Crypto.Semantics.Machine.GeneratedMaskPreparation
import Foundation.Crypto.Semantics.Machine.FlaggedBlockXorComponent
import Foundation.Crypto.Semantics.Machine.PairPreparation

/-! Fresh-key encryption from raw plaintext, using the shared request,
sampler, erasure, rewind and masking components. Scratch cleanup is an
actual native scan. Ciphertext observations have the logical OTP law;
no claim of time-independent full encoded-state leakage is made here. -/
namespace Machine.GeneratedBlockEncryption
open Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

def maskInput (message : List Bool) (middle : Configuration) : FlaggedBlockXor.Component.Input :=
  {key := (GeneratedRequest.readKey message middle).toList, message := message,
    sameLength := Bits.length_toList _}

theorem mask_handoff (message : List Bool) (middle : Configuration)
    (hMiddle : middle ∈ (GeneratedMaskPreparation.link.native.execution.semantics message).support) :
    (middle.resumeAt 0).Equivalent (FlaggedBlockXor.Component.component.swapTapes.procedure.execution.entry (maskInput message middle)) := by
  have h := (GeneratedMaskPreparation.exit_equivalent message middle hMiddle).resumeAt 0
  apply h.trans
  refine ⟨rfl, rfl, Tape.Equivalent.refl _, ?_⟩
  exact (rewindBitstringFinish_input_equivalent
    (FlaggedBlockXor.request message ++ (GeneratedRequest.readKey message middle).toList) {}).trans
      (PairPreparation.prepared_equivalent
        (FlaggedBlockXor.request message ++ (GeneratedRequest.readKey message middle).toList)).symm

noncomputable def masked : TypedNativeComposition.Link GeneratedMaskPreparation.link.native
    FlaggedBlockXor.Component.component.swapTapes.equivalentEntries.procedure :=
  GeneratedMaskPreparation.link.appendEquivalent FlaggedBlockXor.Component.component.swapTapes maskInput mask_handoff
    (fun message => 24 * message.length + 8) (fun _ _ _ => Nat.le_refl _)

theorem masked_code_length : masked.code.length = 86 := by
  rw [masked.code_length]
  change GeneratedMaskPreparation.link.code.length + FlaggedBlockXor.code.swapTapes.length + 3 = 86
  rw [GeneratedMaskPreparation.code_length, Program.swapTapes_length]
  rfl

theorem masked_budget (message : List Bool) : masked.native.execution.budget message = 49 * message.length + 32 := by
  rw [masked.budget, GeneratedMaskPreparation.budget]
  change 25 * message.length + 23 + (24 * message.length + 8) + 1 = _
  omega

def maskedExit (message : List Bool) (key : Bits message.length) : Configuration :=
  {(FlaggedBlockXor.final key.toList message).swapTapes.resumeAt 85 with halted := true}

theorem readKey_maskedExit (message : List Bool) (key : Bits message.length) :
    GeneratedRequest.readKey message (maskedExit message key) = key := by
  have hPacket : (maskedExit message key).outputBits = FlaggedBlockXor.request message ++ key.toList := by
    change (FlaggedBlockXor.final key.toList message).inputTape.bits = _
    rw [FlaggedBlockXor.Layout.final_inputTape]
    simp [Tape.bits, List.reverse_append]
  funext index
  change (maskedExit message key).outputBits[(FlaggedBlockXor.request message).length + index.val]?.getD false = key index
  rw [hPacket]
  simp [Bits.toList]

theorem masked_supported_exit (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (masked.native.execution.semantics message).support) :
    ∃ key : Bits message.length, target.Equivalent (maskedExit message key) := by
  rw [masked.semantics, PMF.mem_support_bind_iff] at hTarget
  obtain ⟨middle, _, hTarget⟩ := hTarget
  rw [PMF.mem_support_map_iff] at hTarget
  obtain ⟨last, hLast, rfl⟩ := hTarget
  have hPure : FlaggedBlockXor.Component.component.swapTapes.procedure.execution.semantics
      (masked.adapt message middle).logical = PMF.pure
        (FlaggedBlockXor.final (GeneratedRequest.readKey message middle).toList message) := by
    change FlaggedBlockXor.Component.component.swapTapes.procedure.execution.semantics
      (GeneratedMaskPreparation.link.equivalentInput FlaggedBlockXor.Component.component.swapTapes maskInput mask_handoff message middle).logical = _
    rw [GeneratedMaskPreparation.link.equivalentInput_logical]
    rfl
  have h := FlaggedBlockXor.Component.component.swapTapes.equivalentEntries_exit _ _ hPure last hLast
  exact ⟨GeneratedRequest.readKey message middle, (h.resumeAt 85).withHalted true⟩

theorem masked_exit_equivalent (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (masked.native.execution.semantics message).support) :
    target.Equivalent (maskedExit message (GeneratedRequest.readKey message target)) := by
  obtain ⟨key, h⟩ := masked_supported_exit message target hTarget
  have hKey := GeneratedRequest.readKey_equivalent message target (maskedExit message key) h
  rw [readKey_maskedExit] at hKey
  rw [hKey]
  exact h

theorem masked_key_distribution (message : List Bool) :
    (masked.native.execution.semantics message).map (GeneratedRequest.readKey message) = uniform (Bits message.length) := by
  have h := GeneratedMaskPreparation.link.appendEquivalent_observe FlaggedBlockXor.Component.component.swapTapes
    maskInput mask_handoff (fun message => 24 * message.length + 8) (fun _ _ _ => Nat.le_refl _)
    (GeneratedRequest.readKey message) (GeneratedRequest.readKey_equivalent message) message
  change (masked.native.execution.semantics message).map (GeneratedRequest.readKey message) = _ at h
  rw [h]
  change (GeneratedMaskPreparation.link.native.execution.semantics message).bind (fun middle =>
    (PMF.pure (FlaggedBlockXor.final (GeneratedRequest.readKey message middle).toList message)).map
      (fun result => GeneratedRequest.readKey message {result.swapTapes.resumeAt 85 with halted := true})) = _
  simp only [PMF.pure_map]
  change (GeneratedMaskPreparation.link.native.execution.semantics message).bind (fun middle =>
    PMF.pure (GeneratedRequest.readKey message (maskedExit message (GeneratedRequest.readKey message middle)))) = _
  simp only [readKey_maskedExit]
  exact GeneratedMaskPreparation.key_distribution message

def eraseInput (message : List Bool) (middle : Configuration) : NativeBackwardErasure.Input :=
  {bits := FlaggedBlockXor.request message ++ (GeneratedRequest.readKey message middle).toList,
    other := (FlaggedBlockXor.final (GeneratedRequest.readKey message middle).toList message).outputTape}

theorem erase_handoff (message : List Bool) (middle : Configuration)
    (hMiddle : middle ∈ (masked.native.execution.semantics message).support) :
    (middle.resumeAt 0).Equivalent (NativeBackwardErasure.component.procedure.execution.entry (eraseInput message middle)) := by
  have h := (masked_exit_equivalent message middle hMiddle).resumeAt 0
  change (middle.resumeAt 0).Equivalent
    ({inputTape := (FlaggedBlockXor.final (GeneratedRequest.readKey message middle).toList message).outputTape,
      outputTape := (FlaggedBlockXor.final (GeneratedRequest.readKey message middle).toList message).inputTape} : Configuration) at h
  rw [FlaggedBlockXor.Layout.final_inputTape] at h
  exact h

theorem erase_bounded (message : List Bool) (middle : Configuration) :
    NativeBackwardErasure.component.procedure.execution.budget (eraseInput message middle) ≤ 12 * message.length + 7 := by
  change 4 * (FlaggedBlockXor.request message ++ (GeneratedRequest.readKey message middle).toList).length + 3 ≤ _
  simp only [List.length_append, FlaggedBlockXor.request_length, Bits.length_toList]
  omega

noncomputable def link : TypedNativeComposition.Link masked.native
    NativeBackwardErasure.component.equivalentEntries.procedure :=
  masked.appendEquivalent NativeBackwardErasure.component eraseInput erase_handoff
    (fun message => 12 * message.length + 7) (fun message middle _ => erase_bounded message middle)

theorem code_length : link.code.length = 94 := by
  rw [link.code_length]
  change masked.code.length + 5 + 3 = 94
  rw [masked_code_length]

theorem budget (message : List Bool) : link.native.execution.budget message = 61 * message.length + 40 := by
  rw [link.budget, masked_budget]
  change 49 * message.length + 32 + (12 * message.length + 7) + 1 = _
  omega

def canonicalExit (message : List Bool) (key : Bits message.length) : Configuration :=
  {pc := 93, inputTape := ResponseExport.endTape (OneTimePad.xorList key.toList message),
    outputTape := {right := List.replicate (3 * message.length + 2) none}, halted := true}

theorem supported_exit (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics message).support) :
    ∃ key : Bits message.length, target.Equivalent (canonicalExit message key) := by
  rw [link.semantics, PMF.mem_support_bind_iff] at hTarget
  obtain ⟨middle, _, hTarget⟩ := hTarget
  rw [PMF.mem_support_map_iff] at hTarget
  obtain ⟨last, hLast, rfl⟩ := hTarget
  have hPure : NativeBackwardErasure.component.procedure.execution.semantics (link.adapt message middle).logical =
      PMF.pure (NativeBackwardErasure.finish (eraseInput message middle)) := by
    change NativeBackwardErasure.component.procedure.execution.semantics
      (masked.equivalentInput NativeBackwardErasure.component eraseInput erase_handoff message middle).logical = _
    rw [masked.equivalentInput_logical]
    rfl
  have h := NativeBackwardErasure.component.equivalentEntries_exit _ _ hPure last hLast
  refine ⟨GeneratedRequest.readKey message middle, ?_⟩
  have hh := (h.resumeAt 93).withHalted true
  change ({last.resumeAt 93 with halted := true} : Configuration).Equivalent
    ({pc := 93, inputTape := (FlaggedBlockXor.final (GeneratedRequest.readKey message middle).toList message).outputTape,
      outputTape := {right := List.replicate ((FlaggedBlockXor.request message ++ (GeneratedRequest.readKey message middle).toList).reverse.length + 1) none ++ []},
      halted := true} : Configuration) at hh
  change ({last.resumeAt 93 with halted := true} : Configuration).Equivalent
    ({pc := 93, inputTape := ResponseExport.endTape (OneTimePad.xorList (GeneratedRequest.readKey message middle).toList message),
      outputTape := {right := List.replicate (3 * message.length + 2) none}, halted := true} : Configuration)
  simpa only [List.length_reverse, List.length_append, FlaggedBlockXor.request_length, Bits.length_toList,
    List.append_nil, FlaggedBlockXor.final_outputTape, ResponseExport.endTape,
    show ∀ n : Nat, 2 * n + 1 + n + 1 = 3 * n + 2 by omega] using hh

theorem scratch_blank (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics message).support) : target.outputTape.Equivalent ({} : Tape) := by
  obtain ⟨key, h⟩ := supported_exit message target hTarget
  exact h.2.2.2.trans (Tape.blank_padding_equivalent [] _)

theorem ciphertext_distribution (message : List Bool) :
    (link.native.execution.semantics message).map (fun state => state.inputTape.bits) =
      (uniform (Bits message.length)).map (fun key => OneTimePad.xorList key.toList message) := by
  have h := masked.appendEquivalent_observe NativeBackwardErasure.component eraseInput erase_handoff
    (fun message => 12 * message.length + 7) (fun message middle _ => erase_bounded message middle)
    (fun state => state.inputTape.bits) (fun _ _ h => h.2.2.1.bits) message
  change (link.native.execution.semantics message).map (fun state => state.inputTape.bits) = _ at h
  rw [h]
  change (masked.native.execution.semantics message).bind (fun middle =>
    (PMF.pure (NativeBackwardErasure.finish (eraseInput message middle))).map
      (fun result => ({result.resumeAt 93 with halted := true} : Configuration).inputTape.bits)) = _
  simp only [PMF.pure_map]
  change (masked.native.execution.semantics message).bind (fun middle =>
    PMF.pure ((FlaggedBlockXor.final (GeneratedRequest.readKey message middle).toList message).outputBits)) = _
  simp only [FlaggedBlockXor.final_output]
  have hKeys := congrArg (fun distribution => distribution.map (fun key => OneTimePad.xorList key.toList message))
    (masked_key_distribution message)
  rw [PMF.map_comp] at hKeys
  exact hKeys

theorem operational : TimedExecution.Procedure.Operational link.native.execution := link.operational

end Machine.GeneratedBlockEncryption
