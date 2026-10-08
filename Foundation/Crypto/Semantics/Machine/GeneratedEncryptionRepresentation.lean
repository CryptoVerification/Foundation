import Foundation.Crypto.Semantics.Machine.GeneratedEncryptionExactTime
import Foundation.Crypto.Semantics.Machine.NativeRepresentationObservation

/-! Account explicitly for finite representation metadata at encryption exit.
The ciphertext, layout, and actual first-halt time determine the entire exit
state. Unrestricted representation secrecy requires the extra public-layout
premises below; this file does not infer them from cell equivalence. -/
namespace Machine.GeneratedBlockEncryption
open Foundation.Probability Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false

def exitCells (ciphertext : List Bool) : Configuration :=
  {pc := 93, inputTape := ResponseExport.endTape ciphertext, halted := true}

theorem arrival_equivalent_cells (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (arrival.procedure.execution.semantics message).support) :
    target.Equivalent (exitCells target.inputTape.bits) := by
  rw [arrival_semantics] at hTarget
  have hCells := continuation_entry_equivalent message target hTarget
  obtain ⟨key, hExit⟩ := supported_exit message target hTarget
  exact ⟨hExit.1, hExit.2.1, hCells.2.2.1, scratch_blank message target hTarget⟩

theorem arrival_representation_observation {Observed : Type u} (message : List Bool)
    (kernel : Configuration × Nat → PMF Observed) :
    (arrival.procedure.execution.costed message).bind kernel =
      ((arrival.procedure.execution.costed message).map
        (fun result => ((result.1.inputTape.bits, result.1.layout), result.2))).bind
        (fun result => kernel (Configuration.reconstruct result.1.2 (exitCells result.1.1), result.2)) := by
  exact arrival.representation_observation (fun _ state => state.inputTape.bits) exitCells
    arrival_equivalent_cells kernel message

theorem arrival_encoded_layout_joint (message : List Bool) :
    (arrival.procedure.execution.costed message).map
      (fun result => (NativeEncodedResources.completeEncoding.encode (link.code, result.1), result.2)) =
      ((arrival.procedure.execution.costed message).map
        (fun result => ((result.1.inputTape.bits, result.1.layout), result.2))).map
        (fun result => (NativeEncodedResources.completeEncoding.encode
          (link.code, Configuration.reconstruct result.1.2 (exitCells result.1.1)), result.2)) := by
  exact arrival.representation_encoded_joint (fun _ state => state.inputTape.bits) exitCells
    arrival_equivalent_cells message

theorem arrival_representation_secrecy_of_public_layout {width : Nat} (left right : Bits width)
    (shape : List Bool → Configuration.Layout)
    (leftLayout : ∀ result, result ∈ (arrival.procedure.execution.costed left.toList).support →
      result.1.layout = shape result.1.inputTape.bits)
    (rightLayout : ∀ result, result ∈ (arrival.procedure.execution.costed right.toList).support →
      result.1.layout = shape result.1.inputTape.bits)
    {Observed : Type u} (kernel : Configuration × Nat → PMF Observed) :
    (arrival.procedure.execution.costed left.toList).bind kernel =
      (arrival.procedure.execution.costed right.toList).bind kernel := by
  apply arrival.representation_eq_of_public_layout (fun _ state => state.inputTape.bits) exitCells
    arrival_equivalent_cells shape left.toList right.toList leftLayout rightLayout _ kernel
  rw [arrival_ciphertext_time_uniform, arrival_ciphertext_time_uniform]

theorem arrival_encoded_secrecy_of_public_layout {width : Nat} (left right : Bits width)
    (shape : List Bool → Configuration.Layout)
    (leftLayout : ∀ result, result ∈ (arrival.procedure.execution.costed left.toList).support →
      result.1.layout = shape result.1.inputTape.bits)
    (rightLayout : ∀ result, result ∈ (arrival.procedure.execution.costed right.toList).support →
      result.1.layout = shape result.1.inputTape.bits) :
    (arrival.procedure.execution.costed left.toList).map
      (fun result => (NativeEncodedResources.completeEncoding.encode (link.code, result.1), result.2)) =
    (arrival.procedure.execution.costed right.toList).map
      (fun result => (NativeEncodedResources.completeEncoding.encode (link.code, result.1), result.2)) := by
  exact arrival_representation_secrecy_of_public_layout left right shape leftLayout rightLayout
    (fun result => PMF.pure (NativeEncodedResources.completeEncoding.encode (link.code, result.1), result.2))

end Machine.GeneratedBlockEncryption
