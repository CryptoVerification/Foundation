import Foundation.Crypto.Semantics.Machine.GeneratedBlockEncryption

/-! Whole-prefix storage for plaintext cleanup and fresh-key encryption.
The initial state contains only the plaintext; request expansion, sampled
keys and every represented blank are charged in the actual compiled run. -/
namespace Machine
open Foundation.Probability TimedExecution

namespace GeneratedMaskPreparation

theorem entry (message : List Bool) : link.native.execution.entry message = Configuration.initial message := by
  rw [link.native_entry, erased.native_entry, GeneratedRequest.entry]

noncomputable def spaceProfile : Nat → Nat :=
  link.storageProfile (fun _ => 0) (fun size => size + 2)
    (fun size => 19 * size + 16) (fun size => 6 * size + 6)

theorem space_polynomial : PolynomiallyBounded spaceProfile :=
  link.storageProfile_polynomial (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))
    (((PolynomiallyBounded.const 19).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 16))
    (((PolynomiallyBounded.const 6).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 6))

theorem storage_peak (message : List Bool) (elapsed : Nat)
    (hElapsed : elapsed ≤ 25 * message.length + 23) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF link.code) elapsed (Configuration.initial message)).support) :
    (NativeEncodedResources.completeEncoding.encode (link.code, target)).length ≤ spaceProfile message.length := by
  apply link.storage_profile (fun _ => 0) (fun size => size + 2)
    (fun size => 19 * size + 16) (fun size => 6 * size + 6)
    (fun size value => value.length = size) _ _ _ _ message.length message rfl elapsed
    (by change elapsed ≤ link.native.execution.budget message; rw [budget]; exact hElapsed) target
    (by rw [erased.native_entry, GeneratedRequest.entry]; exact hTarget)
  · intro size value _
    rw [erased.native_entry, GeneratedRequest.entry]
    exact Nat.le_refl 0
  · intro size value hSize
    rw [erased.native_entry, GeneratedRequest.entry]
    change (Tape.ofBits value).cells + 1 ≤ _
    have h := Tape.cells_ofBits_le value
    omega
  · intro size value hSize
    rw [erased_budget, hSize]
  · intro size value hSize
    change 6 * value.length + 6 ≤ _
    omega

end GeneratedMaskPreparation

namespace GeneratedBlockEncryption

theorem entry (message : List Bool) : link.native.execution.entry message = Configuration.initial message := by
  rw [link.native_entry, masked.native_entry, GeneratedMaskPreparation.entry]

theorem run (message : List Bool) (horizon : Nat) (hTime : 61 * message.length + 40 ≤ horizon) :
    evalConfigWithin link.code (Configuration.initial message) horizon = link.native.execution.semantics message := by
  have h := link.run message horizon (by change link.native.execution.budget message ≤ horizon; rw [budget]; exact hTime)
  rw [← link.native_entry, entry] at h
  exact h

noncomputable def spaceProfile : Nat → Nat :=
  link.storageProfile (fun _ => 0) (fun size => size + 2)
    (fun size => 49 * size + 32) (fun size => 12 * size + 7)

theorem space_polynomial : PolynomiallyBounded spaceProfile :=
  link.storageProfile_polynomial (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))
    (((PolynomiallyBounded.const 49).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 32))
    (((PolynomiallyBounded.const 12).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 7))

theorem storage_peak (message : List Bool) (elapsed : Nat)
    (hElapsed : elapsed ≤ 61 * message.length + 40) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF link.code) elapsed (Configuration.initial message)).support) :
    (NativeEncodedResources.completeEncoding.encode (link.code, target)).length ≤ spaceProfile message.length := by
  apply link.storage_profile (fun _ => 0) (fun size => size + 2)
    (fun size => 49 * size + 32) (fun size => 12 * size + 7)
    (fun size value => value.length = size) _ _ _ _ message.length message rfl elapsed
    (by change elapsed ≤ link.native.execution.budget message; rw [budget]; exact hElapsed) target
    (by rw [masked.native_entry, GeneratedMaskPreparation.entry]; exact hTarget)
  · intro size value _
    rw [masked.native_entry, GeneratedMaskPreparation.entry]
    exact Nat.le_refl 0
  · intro size value hSize
    rw [masked.native_entry, GeneratedMaskPreparation.entry]
    change (Tape.ofBits value).cells + 1 ≤ _
    have h := Tape.cells_ofBits_le value
    omega
  · intro size value hSize
    rw [masked_budget, hSize]
  · intro size value hSize
    change 12 * value.length + 7 ≤ _
    omega

end GeneratedBlockEncryption
end Machine
