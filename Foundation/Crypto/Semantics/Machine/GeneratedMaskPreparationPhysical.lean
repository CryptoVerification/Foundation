import Foundation.Crypto.Semantics.Machine.GeneratedRequestPhysical
import Foundation.Crypto.Semantics.Machine.GeneratedMaskPreparation
import Foundation.Crypto.Semantics.Machine.NativeEntryRealization
import Foundation.Crypto.Semantics.Machine.GeneratedMaskPreparationExactTime
import Foundation.Crypto.Semantics.Machine.RepresentationLayout

/-! Exact physical erasure and rewind after actual key generation.
The rewind's richer contract retains the scratch blank cells produced by
erasure. No cells are silently normalized at either handoff. -/
namespace Machine.GeneratedMaskPreparation
open Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

theorem erase_entry_exact (message : List Bool) (key : Bits message.length) :
    NativeBackwardErasure.inputComponent.procedure.execution.entry
      (eraseInput message (GeneratedRequest.physicalExit message key)) =
      (GeneratedRequest.physicalExit message key).resumeAt 0 := by
  rw [show NativeBackwardErasure.inputComponent.procedure.execution.entry _ =
    (NativeBackwardErasure.initial (eraseInput message (GeneratedRequest.physicalExit message key))).swapTapes by rfl]
  change (
    { inputTape := ResponseExport.endTape (FlaggedBlockXor.request message ++
        (GeneratedRequest.readKey message (GeneratedRequest.physicalExit message key)).toList)
      outputTape := {left := message.reverse.map some ++ [none]} } : Configuration).swapTapes = _
  rw [GeneratedRequest.readKey_physicalExit]
  simp [GeneratedRequest.physicalExit, GeneratedRequest.samplerPhysicalExit, OneTimePad.delimitedFinish,
    Configuration.frameLeft, Tape.frameLeft, Configuration.swapTapes, Configuration.resumeAt, ResponseExport.endTape]

theorem erase_physical_semantics (message : List Bool) (key : Bits message.length) :
    NativeBackwardErasure.inputComponent.equivalentEntries.procedure.execution.semantics
      (GeneratedRequest.link.equivalentInput NativeBackwardErasure.inputComponent eraseInput erase_handoff
        message (GeneratedRequest.physicalExit message key)) =
      PMF.pure ((NativeBackwardErasure.finish
        (eraseInput message (GeneratedRequest.physicalExit message key))).swapTapes) := by
  have h := NativeBackwardErasure.inputComponent.equivalentEntries_realize
    NativeBackwardErasure.inputComponent
    (GeneratedRequest.link.equivalentInput NativeBackwardErasure.inputComponent eraseInput erase_handoff
      message (GeneratedRequest.physicalExit message key))
    (eraseInput message (GeneratedRequest.physicalExit message key)) rfl
    (by rw [GeneratedRequest.link.equivalentInput_actual _ _ _ _ _
        (GeneratedRequest.physical_exit_supported message key)]; exact erase_entry_exact message key)
    (by rw [GeneratedRequest.link.equivalentInput_logical])
  change _ = (PMF.pure (NativeBackwardErasure.finish
    (eraseInput message (GeneratedRequest.physicalExit message key)))).map Configuration.swapTapes at h
  simpa only [PMF.pure_map] using h

/-- Erasure retains exactly n+1 represented scratch blanks. -/
theorem erased_physical_semantics (message : List Bool) :
    erased.native.execution.semantics message = (uniform (Bits message.length)).map (erasedExit message) := by
  rw [erased.semantics, GeneratedRequest.physical_semantics, PMF.bind_map, PMF.map]
  congr 1
  funext key
  dsimp only [Function.comp_def]
  change (NativeBackwardErasure.inputComponent.equivalentEntries.procedure.execution.semantics
    (GeneratedRequest.link.equivalentInput NativeBackwardErasure.inputComponent eraseInput erase_handoff
      message (GeneratedRequest.physicalExit message key))).map _ = _
  rw [erase_physical_semantics, PMF.pure_map]
  congr 1
  change (
    { pc := 38
      inputTape := {right := List.replicate (message.reverse.length + 1) none ++ []}
      outputTape := ResponseExport.endTape (FlaggedBlockXor.request message ++
        (GeneratedRequest.readKey message (GeneratedRequest.physicalExit message key)).toList)
      halted := true } : Configuration) = erasedExit message key
  rw [GeneratedRequest.readKey_physicalExit, List.length_reverse, List.append_nil]
  rfl

def physicalRewindInput (message : List Bool) (key : Bits message.length) : NativeBitstringRewind.Input :=
  { bits := FlaggedBlockXor.request message ++ key.toList
    other := {right := List.replicate (message.length + 1) none} }

theorem readKey_erasedExit (message : List Bool) (key : Bits message.length) :
    GeneratedRequest.readKey message (erasedExit message key) = key := by
  have hBits : (erasedExit message key).outputBits = FlaggedBlockXor.request message ++ key.toList := by
    simp [erasedExit, Configuration.outputBits, ResponseExport.endTape, Tape.bits]
  funext index
  change (erasedExit message key).outputBits[(FlaggedBlockXor.request message).length + index.val]?.getD false = key index
  rw [hBits]
  simp [Bits.toList]

theorem erased_exit_supported (message : List Bool) (key : Bits message.length) :
    erasedExit message key ∈ (erased.native.execution.semantics message).support := by
  rw [erased_physical_semantics, PMF.mem_support_map_iff]
  exact ⟨key, PMF.mem_support_uniformOfFintype key, rfl⟩

theorem rewind_entry_exact (message : List Bool) (key : Bits message.length) :
    NativeBitstringRewind.outputComponent.procedure.execution.entry (physicalRewindInput message key) =
      (erasedExit message key).resumeAt 0 := by
  change (NativeBitstringRewind.initial (physicalRewindInput message key)).swapTapes = _
  simp [NativeBitstringRewind.initial, physicalRewindInput, erasedExit, Configuration.swapTapes,
    Configuration.resumeAt, ResponseExport.endTape]

theorem rewind_physical_semantics (message : List Bool) (key : Bits message.length) :
    NativeBitstringRewind.outputComponent.equivalentEntries.procedure.execution.semantics
      (erased.equivalentInput NativeBitstringRewind.outputComponent rewindInput rewind_handoff
        message (erasedExit message key)) =
      PMF.pure (NativeBitstringRewind.finish (physicalRewindInput message key)).swapTapes := by
  have h := NativeBitstringRewind.outputComponent.equivalentEntries_realize
    NativeBitstringRewind.outputComponent
    (erased.equivalentInput NativeBitstringRewind.outputComponent rewindInput rewind_handoff
      message (erasedExit message key)) (physicalRewindInput message key) rfl
    (by rw [erased.equivalentInput_actual _ _ _ _ _ (erased_exit_supported message key)];
        exact rewind_entry_exact message key)
    (by rw [erased.equivalentInput_logical];
        change 2 * (FlaggedBlockXor.request message ++ key.toList).length + 4 ≤
          2 * (FlaggedBlockXor.request message ++ (GeneratedRequest.readKey message (erasedExit message key)).toList).length + 4
        rw [readKey_erasedExit])
  change _ = (PMF.pure (NativeBitstringRewind.finish (physicalRewindInput message key))).map Configuration.swapTapes at h
  simpa only [PMF.pure_map] using h

def physicalExit (message : List Bool) (key : Bits message.length) : Configuration :=
  {((NativeBitstringRewind.finish (physicalRewindInput message key)).swapTapes).resumeAt 45 with halted := true}

/-- Exact represented exit law of the existing 46-instruction preparation. -/
theorem physical_semantics (message : List Bool) :
    link.native.execution.semantics message = (uniform (Bits message.length)).map (physicalExit message) := by
  rw [link.semantics, erased_physical_semantics, PMF.bind_map, PMF.map]
  congr 1
  funext key
  dsimp only [Function.comp_def]
  change (NativeBitstringRewind.outputComponent.equivalentEntries.procedure.execution.semantics
    (erased.equivalentInput NativeBitstringRewind.outputComponent rewindInput rewind_handoff
      message (erasedExit message key))).map _ = _
  rw [rewind_physical_semantics, PMF.pure_map]
  rfl

theorem physical_exit_scratch (message : List Bool) (key : Bits message.length) :
    (physicalExit message key).inputTape = {right := List.replicate (message.length + 1) none} := rfl

/-- Joint distribution of complete represented state and actual first halt. -/
theorem physical_firstArrival_joint (message : List Bool) :
    link.component.firstArrival.procedure.execution.costed message =
      (uniform (Bits message.length)).map (fun key => (physicalExit message key, 25 * message.length + 23)) := by
  rw [firstArrival_joint, physical_semantics, PMF.map_comp]
  rfl

/-- The preparation layout depends only on the public plaintext length. -/
theorem physical_exit_layout (message : List Bool) (key : Bits message.length) :
    (physicalExit message key).layout = ⟨⟨0, message.length + 1⟩, ⟨1, 3 * message.length + 1⟩⟩ := by
  have hLength : (FlaggedBlockXor.request message ++ key.toList).length = 3 * message.length + 1 := by
    simp only [List.length_append, FlaggedBlockXor.request_length, Bits.length_toList]
    omega
  cases hPacket : FlaggedBlockXor.request message ++ key.toList with
  | nil => simp only [hPacket, List.length_nil] at hLength; omega
  | cons bit rest =>
      simp only [hPacket, List.length_cons] at hLength
      simp [physicalExit, physicalRewindInput, NativeBitstringRewind.finish, Configuration.layout,
        Tape.layout, Configuration.swapTapes, Configuration.resumeAt, hPacket, Tape.moveRight]
      omega

theorem supported_layout (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics message).support) :
    target.layout = ⟨⟨0, message.length + 1⟩, ⟨1, 3 * message.length + 1⟩⟩ := by
  rw [physical_semantics, PMF.mem_support_map_iff] at hTarget
  obtain ⟨key, _, rfl⟩ := hTarget
  exact physical_exit_layout message key

end Machine.GeneratedMaskPreparation
