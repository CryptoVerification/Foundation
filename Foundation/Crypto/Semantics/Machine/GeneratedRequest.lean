import Foundation.Crypto.Semantics.Machine.NativeRequestGeneration
import Foundation.Crypto.Semantics.Machine.NativeBitstringRewind
import Foundation.Crypto.Semantics.Machine.NativeComponentReindex
import Foundation.Crypto.Semantics.Machine.NativeEquivalentComposition
import Foundation.Crypto.Semantics.Machine.ResponseExport

/-! A raw message drives three charged native stages: write its flagged
request, rewind its preserved source, and append a uniform key using the
source cells as length markers. The code is independent of message length. -/
namespace Machine.GeneratedRequest
open Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

noncomputable def writer : NativeComponent (List Bool) Configuration :=
  NativeFlaggedRequest.component.reindex (fun message => ⟨[], [], message⟩)

def rewindInput (message : List Bool) : NativeBitstringRewind.Input :=
  {bits := message, other := ResponseExport.endTape (FlaggedBlockXor.request message)}

noncomputable def firstLink : TypedNativeComposition.Link writer.procedure NativeBitstringRewind.component.procedure :=
  writer.link NativeBitstringRewind.component
    (fun _ machine => {machine.resumeAt 14 with halted := true})
    (by
      intro message output h
      change output ∈ (PMF.pure (NativeFlaggedRequest.finish ⟨[], [], message⟩)).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl)
    (fun message _ => rewindInput message)
    (by
      intro message output h
      change output ∈ (PMF.pure (NativeFlaggedRequest.finish ⟨[], [], message⟩)).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl)
    (fun message => 2 * message.length + 4) (fun _ _ _ => Nat.le_refl _)

def firstFinish (message : List Bool) : Configuration :=
  {(NativeBitstringRewind.finish (rewindInput message)).resumeAt 21 with halted := true}

theorem first_budget (message : List Bool) : firstLink.native.execution.budget message = 10 * message.length + 9 := by
  rw [firstLink.budget]
  change 8 * message.length + 4 + (2 * message.length + 4) + 1 = _
  omega

theorem first_semantics (message : List Bool) : firstLink.native.execution.semantics message = PMF.pure (firstFinish message) := by
  rw [firstLink.semantics]
  change (PMF.pure (NativeFlaggedRequest.finish ⟨[], [], message⟩)).bind _ = _
  rw [PMF.pure_bind]
  change (PMF.pure (NativeBitstringRewind.finish (rewindInput message))).map _ = _
  rw [PMF.pure_map]
  rfl

def samplerInput (message : List Bool) : NativeBitstringContext :=
  ⟨[], FlaggedBlockXor.request message, message⟩

theorem sampler_handoff (message : List Bool) (output : Configuration)
    (hOutput : output ∈ (firstLink.native.execution.semantics message).support) :
    (output.resumeAt 0).Equivalent (NativeContextualSampler.component.procedure.execution.entry (samplerInput message)) := by
  rw [first_semantics, PMF.mem_support_pure_iff] at hOutput
  subst output
  refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
  have h := rewindBitstringFinish_input_equivalent message
    (ResponseExport.endTape (FlaggedBlockXor.request message))
  cases message <;> exact h

noncomputable def link : TypedNativeComposition.Link firstLink.native
    NativeContextualSampler.component.equivalentEntries.procedure :=
  firstLink.appendEquivalent NativeContextualSampler.component (fun message _ => samplerInput message)
    sampler_handoff (fun message => 5 * message.length + 2) (fun _ _ _ => Nat.le_refl _)

theorem code : link.code =
    (NativeFlaggedRequest.code.followedBy rewindBitstring).followedBy OneTimePad.keygen := rfl

theorem code_length : link.code.length = 31 := by
  rw [link.code_length]
  change firstLink.code.length + 6 + 3 = 31
  rw [firstLink.code_length]
  rfl

theorem budget (message : List Bool) : link.native.execution.budget message = 15 * message.length + 12 := by
  rw [link.budget, first_budget]
  change 10 * message.length + 9 + (5 * message.length + 2) + 1 = _
  omega

theorem entry (message : List Bool) : link.native.execution.entry message = Configuration.initial message := by
  rw [link.native_entry, firstLink.native_entry]
  change OneTimePad.state [] [] message = _
  exact OneTimePad.state_initial message

def readKey (message : List Bool) (machine : Configuration) : Bits message.length :=
  NativeContextualSampler.readKey (samplerInput message) machine

theorem readKey_finish (message : List Bool) (key : Bits message.length) :
    readKey message (NativeContextualSampler.finish (samplerInput message) key) = key :=
  NativeContextualSampler.readKey_finish (samplerInput message) key

theorem readKey_equivalent (message : List Bool) (first second : Configuration)
    (h : first.Equivalent second) : readKey message first = readKey message second :=
  NativeContextualSampler.readKey_equivalent (samplerInput message) first second h

theorem key_distribution (message : List Bool) :
    (link.native.execution.semantics message).map (readKey message) = uniform (Bits message.length) := by
  rw [link.semantics, first_semantics, PMF.pure_bind, PMF.map_comp]
  change (NativeContextualSampler.component.equivalentEntries.procedure.execution.semantics
    (firstLink.equivalentInput NativeContextualSampler.component (fun message _ => samplerInput message)
      sampler_handoff message (firstFinish message))).map (readKey message) = _
  rw [NativeComponent.equivalentEntries_observe _ _ (readKey message) (readKey_equivalent message)]
  rw [firstLink.equivalentInput_logical, NativeContextualSampler.semantics, PMF.map_comp]
  change (uniform (Bits message.length)).map (fun key => readKey message (NativeContextualSampler.finish (samplerInput message) key)) = _
  simp only [readKey_finish]
  exact PMF.map_id _

theorem run (message : List Bool) (horizon : Nat) (hTime : 15 * message.length + 12 ≤ horizon) :
    (evalConfigWithin link.code (Configuration.initial message) horizon).map (readKey message) = uniform (Bits message.length) := by
  have h := link.run message horizon (by change link.native.execution.budget message ≤ horizon; rw [budget]; exact hTime)
  rw [firstLink.native_entry] at h
  change evalConfigWithin link.code (OneTimePad.state [] [] message) horizon = _ at h
  rw [OneTimePad.state_initial] at h
  exact (congrArg (fun distribution => distribution.map (readKey message)) h).trans (key_distribution message)

theorem operational : TimedExecution.Procedure.Operational link.native.execution := link.operational

def canonicalExit (message : List Bool) (key : Bits message.length) : Configuration :=
  {(NativeContextualSampler.finish (samplerInput message) key).resumeAt 30 with halted := true}

theorem supported_exit (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics message).support) :
    ∃ key : Bits message.length, target.Equivalent (canonicalExit message key) := by
  rw [link.semantics, first_semantics, PMF.pure_bind, PMF.mem_support_map_iff] at hTarget
  obtain ⟨middle, hMiddle, rfl⟩ := hTarget
  obtain ⟨canonical, hCanonical, hEquivalent⟩ :=
    NativeContextualSampler.component.equivalentEntries_supported_exit _ middle hMiddle
  change canonical ∈ (NativeContextualSampler.component.procedure.execution.semantics
    (firstLink.equivalentInput NativeContextualSampler.component (fun message _ => samplerInput message)
      sampler_handoff message (firstFinish message)).logical).support at hCanonical
  rw [firstLink.equivalentInput_logical, NativeContextualSampler.semantics, PMF.mem_support_map_iff] at hCanonical
  obtain ⟨key, _, rfl⟩ := hCanonical
  exact ⟨key, (hEquivalent.resumeAt 30).withHalted true⟩

theorem exit_equivalent (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics message).support) :
    target.Equivalent (canonicalExit message (readKey message target)) := by
  obtain ⟨key, h⟩ := supported_exit message target hTarget
  have hKey := readKey_equivalent message target (canonicalExit message key) h
  change readKey message target = readKey message (NativeContextualSampler.finish (samplerInput message) key) at hKey
  rw [readKey_finish] at hKey
  rw [hKey]
  exact h

end Machine.GeneratedRequest
