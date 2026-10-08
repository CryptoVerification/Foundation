import Foundation.Crypto.Semantics.Machine.ContextualBlockXor
import Foundation.Crypto.Semantics.Machine.GeneratedMaskPreparationPhysical
import Foundation.Crypto.Semantics.Machine.GeneratedEncryptionRepresentation
import Foundation.Crypto.Semantics.Machine.BitstringXorLaws

/-! Exact represented-state law of the existing 94-instruction encryption.
Contextual masking retains the scratch delimiter. Cleanup preserves that
extra ciphertext-side blank while erasing the actual request/key packet.
All layouts below are proved for arbitrary message lengths and all keys. -/
namespace Machine.GeneratedBlockEncryption
open Foundation.Probability TimedExecution Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false

def physicalMaskInput (message : List Bool) (key : Bits message.length) : FlaggedBlockXor.Contextual.Input :=
  { key := key.toList
    message := message
    sameLength := Bits.length_toList key
    outputSuffix := [none] }

theorem readKey_preparationPhysicalExit (message : List Bool) (key : Bits message.length) :
    GeneratedRequest.readKey message (GeneratedMaskPreparation.physicalExit message key) = key := by
  have hBits : (GeneratedMaskPreparation.physicalExit message key).outputBits =
      FlaggedBlockXor.request message ++ key.toList := by
    have h := (rewindBitstringFinish_input_equivalent (FlaggedBlockXor.request message ++ key.toList) {}).bits
    change (rewindBitstringFinish (FlaggedBlockXor.request message ++ key.toList) {}).inputTape.bits = _
    simpa only [Tape.bits_ofBits] using h
  funext index
  change (GeneratedMaskPreparation.physicalExit message key).outputBits[
    (FlaggedBlockXor.request message).length + index.val]?.getD false = key index
  rw [hBits]
  simp [Bits.toList]

theorem preparation_physical_supported (message : List Bool) (key : Bits message.length) :
    GeneratedMaskPreparation.physicalExit message key ∈
      (GeneratedMaskPreparation.link.native.execution.semantics message).support := by
  rw [GeneratedMaskPreparation.physical_semantics, PMF.mem_support_map_iff]
  exact ⟨key, PMF.mem_support_uniformOfFintype key, rfl⟩

theorem mask_entry_exact (message : List Bool) (key : Bits message.length) :
    FlaggedBlockXor.Contextual.component.swapTapes.procedure.execution.entry (physicalMaskInput message key) =
      (GeneratedMaskPreparation.physicalExit message key).resumeAt 0 := by
  change (FlaggedBlockXor.Contextual.initial (physicalMaskInput message key)).swapTapes = _
  rw [FlaggedBlockXor.Contextual.initial_eq]
  cases message <;>
    simp [physicalMaskInput, GeneratedMaskPreparation.physicalExit, GeneratedMaskPreparation.physicalRewindInput,
      NativeBitstringRewind.finish, Configuration.swapTapes, Configuration.resumeAt,
      OneTimePad.delimitedTape, Tape.moveRight, FlaggedBlockXor.request, FlaggedBlockXor.messagePrefix,
      List.replicate_succ', List.append_assoc]

theorem mask_physical_semantics (message : List Bool) (key : Bits message.length) :
    FlaggedBlockXor.Component.component.swapTapes.equivalentEntries.procedure.execution.semantics
      (GeneratedMaskPreparation.link.equivalentInput FlaggedBlockXor.Component.component.swapTapes
        maskInput mask_handoff message (GeneratedMaskPreparation.physicalExit message key)) =
      PMF.pure (FlaggedBlockXor.Contextual.finish (physicalMaskInput message key)).swapTapes := by
  have h := FlaggedBlockXor.Component.component.swapTapes.equivalentEntries_realize
    FlaggedBlockXor.Contextual.component.swapTapes
    (GeneratedMaskPreparation.link.equivalentInput FlaggedBlockXor.Component.component.swapTapes
      maskInput mask_handoff message (GeneratedMaskPreparation.physicalExit message key))
    (physicalMaskInput message key) rfl
    (by rw [GeneratedMaskPreparation.link.equivalentInput_actual _ _ _ _ _ (preparation_physical_supported message key)];
        exact mask_entry_exact message key)
    (by rw [GeneratedMaskPreparation.link.equivalentInput_logical]; exact Nat.le_refl _)
  change _ = (PMF.pure (FlaggedBlockXor.Contextual.finish (physicalMaskInput message key))).map Configuration.swapTapes at h
  simpa only [PMF.pure_map] using h

def physicalMaskedExit (message : List Bool) (key : Bits message.length) : Configuration :=
  {((FlaggedBlockXor.Contextual.finish (physicalMaskInput message key)).swapTapes).resumeAt 85 with halted := true}

theorem masked_physical_semantics (message : List Bool) :
    masked.native.execution.semantics message = (uniform (Bits message.length)).map (physicalMaskedExit message) := by
  rw [masked.semantics, GeneratedMaskPreparation.physical_semantics, PMF.bind_map, PMF.map]
  congr 1
  funext key
  dsimp only [Function.comp_def]
  change (FlaggedBlockXor.Component.component.swapTapes.equivalentEntries.procedure.execution.semantics
    (GeneratedMaskPreparation.link.equivalentInput FlaggedBlockXor.Component.component.swapTapes maskInput mask_handoff
      message (GeneratedMaskPreparation.physicalExit message key))).map _ = _
  rw [mask_physical_semantics, PMF.pure_map]
  rfl

theorem readKey_physicalMaskedExit (message : List Bool) (key : Bits message.length) :
    GeneratedRequest.readKey message (physicalMaskedExit message key) = key := by
  have hBits : (physicalMaskedExit message key).outputBits = FlaggedBlockXor.request message ++ key.toList := by
    simp [physicalMaskedExit, physicalMaskInput, FlaggedBlockXor.Contextual.finish, Configuration.outputBits,
      Configuration.swapTapes, Configuration.resumeAt, Tape.bits]
  funext index
  change (physicalMaskedExit message key).outputBits[(FlaggedBlockXor.request message).length + index.val]?.getD false = key index
  rw [hBits]
  simp [Bits.toList]

theorem physical_masked_supported (message : List Bool) (key : Bits message.length) :
    physicalMaskedExit message key ∈ (masked.native.execution.semantics message).support := by
  rw [masked_physical_semantics, PMF.mem_support_map_iff]
  exact ⟨key, PMF.mem_support_uniformOfFintype key, rfl⟩

def physicalEraseInput (message : List Bool) (key : Bits message.length) : NativeBackwardErasure.Input :=
  { bits := FlaggedBlockXor.request message ++ key.toList
    other := {left := (OneTimePad.xorList key.toList message).reverse.map some, right := [none]} }

theorem erase_entry_exact (message : List Bool) (key : Bits message.length) :
    NativeBackwardErasure.component.procedure.execution.entry (physicalEraseInput message key) =
      (physicalMaskedExit message key).resumeAt 0 := by
  change (
    { inputTape := (physicalEraseInput message key).other
      outputTape := {left := (FlaggedBlockXor.request message ++ key.toList).reverse.map some ++ [none]} } : Configuration) = _
  rfl

theorem erase_physical_semantics (message : List Bool) (key : Bits message.length) :
    NativeBackwardErasure.component.equivalentEntries.procedure.execution.semantics
      (masked.equivalentInput NativeBackwardErasure.component eraseInput erase_handoff message (physicalMaskedExit message key)) =
      PMF.pure (NativeBackwardErasure.finish (physicalEraseInput message key)) := by
  have h := NativeBackwardErasure.component.equivalentEntries_realize NativeBackwardErasure.component
    (masked.equivalentInput NativeBackwardErasure.component eraseInput erase_handoff message (physicalMaskedExit message key))
    (physicalEraseInput message key) rfl
    (by rw [masked.equivalentInput_actual _ _ _ _ _ (physical_masked_supported message key)];
        exact erase_entry_exact message key)
    (by rw [masked.equivalentInput_logical];
        change 4 * (FlaggedBlockXor.request message ++ key.toList).length + 3 ≤
          4 * (FlaggedBlockXor.request message ++ (GeneratedRequest.readKey message (physicalMaskedExit message key)).toList).length + 3
        rw [readKey_physicalMaskedExit])
  change _ = (PMF.pure (NativeBackwardErasure.finish (physicalEraseInput message key))).map id at h
  simpa only [PMF.map_id] using h

/-- Every remaining represented cell is a function of ciphertext and length. -/
def physicalCipherExit (ciphertext : List Bool) : Configuration :=
  { pc := 93
    inputTape := {left := ciphertext.reverse.map some, right := [none]}
    outputTape := {right := List.replicate (3 * ciphertext.length + 2) none}
    halted := true }

theorem xorList_length (key message : List Bool) (hLength : key.length = message.length) :
    (OneTimePad.xorList key message).length = message.length := OneTimePad.xorList_length key message hLength

/-- Full represented-state law, without a layout premise. -/
theorem physical_semantics (message : List Bool) :
    link.native.execution.semantics message = (uniform (Bits message.length)).map
      (fun key => physicalCipherExit (OneTimePad.xorList key.toList message)) := by
  rw [link.semantics, masked_physical_semantics, PMF.bind_map, PMF.map]
  congr 1
  funext key
  dsimp only [Function.comp_def]
  change (NativeBackwardErasure.component.equivalentEntries.procedure.execution.semantics
    (masked.equivalentInput NativeBackwardErasure.component eraseInput erase_handoff message (physicalMaskedExit message key))).map _ = _
  rw [erase_physical_semantics, PMF.pure_map]
  congr 1
  change (
    { pc := 93
      inputTape := (physicalEraseInput message key).other
      outputTape := {right := List.replicate ((FlaggedBlockXor.request message ++ key.toList).reverse.length + 1) none ++ []}
      halted := true } : Configuration) = physicalCipherExit (OneTimePad.xorList key.toList message)
  simp [physicalEraseInput, physicalCipherExit, xorList_length _ _ (Bits.length_toList key),
    FlaggedBlockXor.request_length]
  omega

@[simp] theorem physicalCipherExit_bits (ciphertext : List Bool) :
    (physicalCipherExit ciphertext).inputTape.bits = ciphertext := by
  simp [physicalCipherExit, Tape.bits]

theorem physicalCipherExit_layout (ciphertext : List Bool) :
    (physicalCipherExit ciphertext).layout = ⟨⟨ciphertext.length, 1⟩, ⟨0, 3 * ciphertext.length + 2⟩⟩ := by
  simp [physicalCipherExit, Configuration.layout, Tape.layout]

/-- The layout premise needed by the earlier representation theorem is derived. -/
theorem physical_supported_layout (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics message).support) :
    target.layout = ⟨⟨message.length, 1⟩, ⟨0, 3 * message.length + 2⟩⟩ := by
  rw [physical_semantics, PMF.mem_support_map_iff] at hTarget
  obtain ⟨key, _, rfl⟩ := hTarget
  rw [physicalCipherExit_layout, xorList_length _ _ (Bits.length_toList key)]

/-- One common full-state distribution for every plaintext of the same length. -/
theorem physical_semantics_uniform {width : Nat} (message : Bits width) :
    link.native.execution.semantics message.toList =
      (uniform (Bits width)).map (fun ciphertext => physicalCipherExit ciphertext.toList) := by
  have hState : link.native.execution.semantics message.toList =
      ((link.native.execution.semantics message.toList).map (fun state => state.inputTape.bits)).map
        physicalCipherExit := by
    rw [physical_semantics, PMF.map_comp, PMF.map_comp]
    congr 1
    funext key
    simp only [Function.comp_def, physicalCipherExit_bits]
  rw [hState, ciphertext_uniform, PMF.map_comp]
  rfl

/-- The entire represented state and the actual first-halt time are public functions of a uniform ciphertext. -/
theorem arrival_physical_uniform {width : Nat} (message : Bits width) :
    arrival.procedure.execution.costed message.toList =
      (uniform (Bits width)).map (fun ciphertext => (physicalCipherExit ciphertext.toList, 61 * width + 40)) := by
  rw [arrival_joint, physical_semantics_uniform, Bits.length_toList, PMF.map_comp]
  rfl

/-- No cell-invariance or public-layout premise is imposed on the observer. -/
theorem arrival_representation_perfect_secrecy {width : Nat} (left right : Bits width)
    {Observed : Type u} (kernel : Configuration × Nat → PMF Observed) :
    (arrival.procedure.execution.costed left.toList).bind kernel =
      (arrival.procedure.execution.costed right.toList).bind kernel := by
  rw [arrival_physical_uniform, arrival_physical_uniform]

theorem arrival_encoded_perfect_secrecy {width : Nat} (left right : Bits width) :
    (arrival.procedure.execution.costed left.toList).map
      (fun result => (NativeEncodedResources.completeEncoding.encode (link.code, result.1), result.2)) =
    (arrival.procedure.execution.costed right.toList).map
      (fun result => (NativeEncodedResources.completeEncoding.encode (link.code, result.1), result.2)) := by
  rw [arrival_physical_uniform, arrival_physical_uniform]

/-- Subsequent code may inspect the full representation and use its own arbitrary boundary. -/
theorem arrival_representation_boundary_secrecy {width : Nat} (left right : Bits width)
    {Observed : Type u} (context : Nat → Program) (boundary : Nat → Configuration → Bool)
    (fuel : Nat → Nat) (observe : Nat → Configuration × Nat → Observed) :
    (arrival.procedure.execution.costed left.toList).bind (fun result =>
      (runToBoundary (stepPMF (context result.2)) (boundary result.2) (fuel result.2)
        (result.1.resumeAt 0)).map (observe result.2)) =
    (arrival.procedure.execution.costed right.toList).bind (fun result =>
      (runToBoundary (stepPMF (context result.2)) (boundary result.2) (fuel result.2)
        (result.1.resumeAt 0)).map (observe result.2)) := by
  exact arrival_representation_perfect_secrecy left right _

/-- Raw execution from plaintext, for any analysis fuel above the proved bound. -/
theorem run_arrival_representation_perfect_secrecy {width : Nat} (left right : Bits width)
    (horizon : Nat) (hTime : 61 * width + 40 ≤ horizon)
    {Observed : Type u} (kernel : Configuration × Nat → PMF Observed) :
    (runToBoundary (stepPMF link.code) Configuration.halted horizon (Configuration.initial left.toList)).bind kernel =
      (runToBoundary (stepPMF link.code) Configuration.halted horizon (Configuration.initial right.toList)).bind kernel := by
  rw [arrival_costed_horizon left.toList horizon (by simpa only [Bits.length_toList] using hTime),
    arrival_costed_horizon right.toList horizon (by simpa only [Bits.length_toList] using hTime)]
  exact arrival_representation_perfect_secrecy left right kernel

end Machine.GeneratedBlockEncryption
