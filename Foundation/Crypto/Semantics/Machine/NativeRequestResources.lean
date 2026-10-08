import Foundation.Crypto.Semantics.Machine.GeneratedRequest

/-! Storage includes all inherited data, request expansion, appended random
bits, complete finite code and every prefix state of the generated request. -/
namespace Machine
open Foundation.Probability TimedExecution

namespace NativeBitstringContext

def size (input : NativeBitstringContext) : Nat := input.before.length + input.prefixBits.length + input.data.length

theorem initial_cells (input : NativeBitstringContext) :
    (OneTimePad.state input.before input.prefixBits input.data).tapeCells ≤ input.size + 2 := by
  have hi := Tape.cells_ofBits_le input.data
  change ({Tape.ofBits input.data with left := input.before.reverse.map some} : Tape).cells +
    ({left := input.prefixBits.reverse.map some} : Tape).cells ≤ _
  simp only [Tape.cells, List.length_map, List.length_reverse, List.length_nil]
  simp only [Tape.cells] at hi
  unfold size
  omega

end NativeBitstringContext

namespace NativeFlaggedRequest

def bitBound (size : Nat) : Nat := NativeEncodedResources.bound code 0 (size + 2) (8 * size + 4)

theorem space_polynomial : PolynomiallyBounded bitBound :=
  NativeEncodedResources.bound_polynomial _ (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))
    (((PolynomiallyBounded.const 8).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 4))

theorem storage_peak (input : NativeBitstringContext) (elapsed : Nat)
    (hElapsed : elapsed ≤ 8 * input.data.length + 4) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF code) elapsed (initial input)).support) :
    (NativeEncodedResources.completeEncoding.encode (code, target)).length ≤ bitBound input.size := by
  have h := NativeEncodedResources.peak code _ elapsed hElapsed _ target hTarget
  exact h.trans (NativeEncodedResources.bound_mono _ (Nat.le_refl 0) input.initial_cells
    (by unfold NativeBitstringContext.size; omega))

end NativeFlaggedRequest

namespace NativeContextualSampler

def bitBound (size : Nat) : Nat := NativeEncodedResources.bound OneTimePad.keygen 0 (size + 2) (5 * size + 2)

theorem space_polynomial : PolynomiallyBounded bitBound :=
  NativeEncodedResources.bound_polynomial _ (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))
    (((PolynomiallyBounded.const 5).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 2))

theorem storage_peak (input : NativeBitstringContext) (elapsed : Nat)
    (hElapsed : elapsed ≤ 5 * input.data.length + 2) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF OneTimePad.keygen) elapsed (initial input)).support) :
    (NativeEncodedResources.completeEncoding.encode (OneTimePad.keygen, target)).length ≤ bitBound input.size := by
  have h := NativeEncodedResources.peak OneTimePad.keygen _ elapsed hElapsed _ target hTarget
  exact h.trans (NativeEncodedResources.bound_mono _ (Nat.le_refl 0) input.initial_cells
    (by unfold NativeBitstringContext.size; omega))

end NativeContextualSampler

namespace GeneratedRequest

noncomputable def spaceProfile : Nat → Nat :=
  link.storageProfile (fun _ => 0) (fun size => size + 2)
    (fun size => 10 * size + 9) (fun size => 5 * size + 2)

theorem space_polynomial : PolynomiallyBounded spaceProfile :=
  link.storageProfile_polynomial (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))
    (((PolynomiallyBounded.const 10).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 9))
    (((PolynomiallyBounded.const 5).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 2))

theorem storage_peak (message : List Bool) (elapsed : Nat)
    (hElapsed : elapsed ≤ 15 * message.length + 12) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF link.code) elapsed (Configuration.initial message)).support) :
    (NativeEncodedResources.completeEncoding.encode (link.code, target)).length ≤ spaceProfile message.length := by
  apply link.storage_profile (fun _ => 0) (fun size => size + 2)
    (fun size => 10 * size + 9) (fun size => 5 * size + 2)
    (fun size value => value.length = size) _ _ _ _ message.length message rfl elapsed
    (by change elapsed ≤ link.native.execution.budget message; rw [budget]; exact hElapsed) target
    (by
      rw [firstLink.native_entry]
      change target ∈ (TimedExecution.eval (stepPMF link.code) elapsed (OneTimePad.state [] [] message)).support
      rw [OneTimePad.state_initial]
      exact hTarget)
  · intro size value _
    rw [firstLink.native_entry]
    exact Nat.le_refl 0
  · intro size value hSize
    rw [firstLink.native_entry]
    change (OneTimePad.state [] [] value).tapeCells ≤ _
    have h := NativeBitstringContext.initial_cells ⟨[], [], value⟩
    simpa only [NativeBitstringContext.size, List.length_nil, Nat.zero_add, hSize] using h
  · intro size value hSize
    rw [first_budget, hSize]
  · intro size value hSize
    change 5 * value.length + 2 ≤ _
    omega

end GeneratedRequest
end Machine
