import Foundation.Crypto.Semantics.Machine.NativeCellResponseEquivalent
import Foundation.Crypto.Semantics.Machine.GeneratedEncryptionPhysical
import Foundation.Crypto.Semantics.Machine.NativeFirstArrivalTimeTransport

/-! A concrete fresh-key masking component with physical packet delivery.
Operand relabeling puts the actual ciphertext on the export tape; it is
compilation of fixed code, not a free runtime tape exchange. Every call
samples a new key. This is not a same-key encryption security theorem. -/
namespace Machine.FreshMaskResponse
open Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

noncomputable def component := GeneratedBlockEncryption.link.component.swapTapes

@[simp] theorem output_bits (ciphertext : List Bool) :
    (GeneratedBlockEncryption.physicalCipherExit ciphertext).swapTapes.outputBits = ciphertext :=
  GeneratedBlockEncryption.physicalCipherExit_bits ciphertext

theorem supported (message : List Bool) (state : Configuration)
    (hState : state ∈ (component.procedure.execution.semantics message).support) :
    NativeCellResponse.Valid message.length (component.procedure.execution.exit message state) := by
  change state ∈ (GeneratedBlockEncryption.link.native.execution.semantics message).support at hState
  rw [GeneratedBlockEncryption.physical_semantics, PMF.mem_support_map_iff] at hState
  obtain ⟨key, _, rfl⟩ := hState
  change NativeCellResponse.Valid message.length
    (GeneratedBlockEncryption.physicalCipherExit (OneTimePad.xorList key.toList message)).swapTapes
  refine ⟨rfl, ?_, ?_⟩
  · constructor
    · rfl
    · constructor
      · intro i
        rw [output_bits]
        rfl
      · intro i
        cases i <;> simp [GeneratedBlockEncryption.physicalCipherExit, Configuration.swapTapes,
          ResponseExport.endTape]
  · rw [output_bits]
    exact (OneTimePad.xorList_length _ _ (Bits.length_toList key)).le

noncomputable def execution (message : List Bool) :=
  NativeCellResponse.whole component message message.length (supported message)

theorem budget (message : List Bool) : (execution message).budget () = 64 * message.length + 44 := by
  rw [execution, NativeCellResponse.budget]
  change GeneratedBlockEncryption.link.native.execution.budget message + (3 * message.length + 4) = _
  rw [GeneratedBlockEncryption.budget]
  omega

/-- The joint law includes fresh sampling, masking, erasure, and every
physical export movement. Only the public length determines the duration. -/
theorem costed_uniform {width : Nat} (message : Bits width) :
    ((execution message.toList).costed ()).map (fun result => (result.1.2, result.2)) =
      (uniform (Bits width)).map (fun ciphertext => (ciphertext.toList, 64 * width + 44)) := by
  rw [execution, NativeCellResponse.costed]
  rw [component, NativeComponent.swapTapes_firstArrival_costed]
  change ((GeneratedBlockEncryption.arrival.procedure.execution.costed message.toList).map _).map _ = _
  rw [GeneratedBlockEncryption.arrival_physical_uniform, PMF.map_comp, PMF.map_comp]
  congr 1
  funext ciphertext
  dsimp only [Function.comp_def]
  rw [output_bits, Bits.length_toList]
  congr 1
  omega

/-- A subsequent probabilistic observer may depend jointly on ciphertext
and the real elapsed time. Equal-width plaintexts have identical laws. -/
theorem perfect_secrecy {width : Nat} (left right : Bits width)
    {Observed : Type*} (observer : List Bool × Nat → PMF Observed) :
    (((execution left.toList).costed ()).map (fun result => (result.1.2, result.2))).bind observer =
      (((execution right.toList).costed ()).map (fun result => (result.1.2, result.2))).bind observer := by
  rw [costed_uniform, costed_uniform]

/-- Reuse the same compiled code on an inherited physical entry. The
argument carries a cell-equivalence proof, never a normalized replacement. -/
noncomputable def fromEquivalent (input : NativeComponent.EquivalentInput component) :=
  NativeCellResponse.fromEquivalent component input input.logical.length (supported input.logical)

theorem fromEquivalent_costed (input : NativeComponent.EquivalentInput component) :
    ((fromEquivalent input).costed ()).map (fun result => (result.1.2, result.2)) =
      ((execution input.logical).costed ()).map (fun result => (result.1.2, result.2)) := by
  rw [fromEquivalent, NativeCellResponse.fromEquivalent_costed, execution, NativeCellResponse.costed]

theorem fromEquivalent_uniform {width : Nat} (message : Bits width)
    (input : NativeComponent.EquivalentInput component) (hMessage : input.logical = message.toList) :
    ((fromEquivalent input).costed ()).map (fun result => (result.1.2, result.2)) =
      (uniform (Bits width)).map (fun ciphertext => (ciphertext.toList, 64 * width + 44)) := by
  rw [fromEquivalent_costed, hMessage, costed_uniform]

end Machine.FreshMaskResponse
