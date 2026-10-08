import Foundation.Crypto.Semantics.Machine.DelimitedSampler
import Foundation.Crypto.Semantics.Machine.GeneratedRequest

/-! Exact represented states for the generated-request pipeline.
Unlike cell equivalence, these equalities retain the saved outer blank
introduced by the real rewind and the explicit terminal delimiter. -/
namespace Machine.GeneratedRequest
open Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

def samplerPhysicalEntry (message : List Bool) : Configuration :=
  (OneTimePad.delimitedState [] (FlaggedBlockXor.request message) message []).frameLeft [none] []

def samplerPhysicalExit (message : List Bool) (key : Bits message.length) : Configuration :=
  (OneTimePad.delimitedFinish message (FlaggedBlockXor.request message ++ key.toList) []).frameLeft [none] []

theorem sampler_entry_exact (message : List Bool) :
    (firstFinish message).resumeAt 0 = samplerPhysicalEntry message := by
  cases message <;>
    simp [firstFinish, rewindInput, NativeBitstringRewind.finish,
      samplerPhysicalEntry, OneTimePad.delimitedState, OneTimePad.delimitedTape,
      Configuration.frameLeft, Tape.frameLeft, Tape.moveRight, ResponseExport.endTape,
      Configuration.resumeAt]

theorem sampler_physical_run (message : List Bool) :
    evalConfigWithin OneTimePad.keygen ((firstFinish message).resumeAt 0) (5 * message.length + 2) =
      (uniform (Bits message.length)).map (samplerPhysicalExit message) := by
  rw [sampler_entry_exact]
  unfold samplerPhysicalEntry samplerPhysicalExit
  simpa only [List.nil_append] using
    OneTimePad.keygen_delimited_framed_run [] (FlaggedBlockXor.request message) message [] [none] []

theorem sampler_physical_semantics (message : List Bool) :
    NativeContextualSampler.component.equivalentEntries.procedure.execution.semantics
      (firstLink.equivalentInput NativeContextualSampler.component (fun message _ => samplerInput message)
        sampler_handoff message (firstFinish message)) =
      (uniform (Bits message.length)).map (samplerPhysicalExit message) := by
  change evalConfigWithin OneTimePad.keygen
    (firstLink.equivalentInput NativeContextualSampler.component (fun message _ => samplerInput message)
      sampler_handoff message (firstFinish message)).actual
    (NativeContextualSampler.component.procedure.execution.budget
      (firstLink.equivalentInput NativeContextualSampler.component (fun message _ => samplerInput message)
        sampler_handoff message (firstFinish message)).logical) = _
  rw [firstLink.equivalentInput_actual _ _ _ _ _ (by rw [first_semantics, PMF.mem_support_pure_iff]),
    firstLink.equivalentInput_logical]
  exact sampler_physical_run message

def physicalExit (message : List Bool) (key : Bits message.length) : Configuration :=
  {(samplerPhysicalExit message key).resumeAt 30 with halted := true}

/-- Exact full-state law of the existing 31-instruction pipeline. -/
theorem physical_semantics (message : List Bool) :
    link.native.execution.semantics message = (uniform (Bits message.length)).map (physicalExit message) := by
  rw [link.semantics, first_semantics, PMF.pure_bind]
  change (NativeContextualSampler.component.equivalentEntries.procedure.execution.semantics
    (firstLink.equivalentInput NativeContextualSampler.component (fun message _ => samplerInput message)
      sampler_handoff message (firstFinish message))).map _ = _
  rw [sampler_physical_semantics, PMF.map_comp]
  rfl

/-- The saved blank is now part of an equality, not an equivalence premise. -/
theorem physical_exit_input (message : List Bool) (key : Bits message.length) :
    (physicalExit message key).inputTape = {left := message.reverse.map some ++ [none]} := rfl

theorem physical_exit_output (message : List Bool) (key : Bits message.length) :
    (physicalExit message key).outputTape = ResponseExport.endTape (FlaggedBlockXor.request message ++ key.toList) := by
  simp [physicalExit, samplerPhysicalExit, OneTimePad.delimitedFinish, Configuration.resumeAt,
    Configuration.frameLeft, Tape.frameLeft, ResponseExport.endTape]

theorem readKey_physicalExit (message : List Bool) (key : Bits message.length) :
    readKey message (physicalExit message key) = key := by
  have hBits : (physicalExit message key).outputBits = FlaggedBlockXor.request message ++ key.toList := by
    simp [Configuration.outputBits, physical_exit_output, ResponseExport.endTape, Tape.bits]
  funext index
  change (physicalExit message key).outputBits[(FlaggedBlockXor.request message).length + index.val]?.getD false = key index
  rw [hBits]
  simp [Bits.toList]

theorem physical_exit_supported (message : List Bool) (key : Bits message.length) :
    physicalExit message key ∈ (link.native.execution.semantics message).support := by
  rw [physical_semantics, PMF.mem_support_map_iff]
  exact ⟨key, PMF.mem_support_uniformOfFintype key, rfl⟩

end Machine.GeneratedRequest
