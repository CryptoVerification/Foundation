import Foundation.Crypto.Semantics.Machine.CleanBlockMask
import Foundation.Crypto.Semantics.Machine.NativeContinuationObservation

/-! After real scratch erasure, any finite native continuation has the same
cell-invariant observations as a canonical entry containing only ciphertext.
The ciphertext head is at its end; rewinding remains a charged operation.
This is not a theorem about arbitrary inspection of the encoded zipper. -/
namespace Machine.CleanBlockMask
open Foundation.Probability
universe u

def continuationEntry (ciphertext : List Bool) : Configuration :=
  {inputTape := {left := ciphertext.reverse.map some}}

theorem continuation_entry_equivalent (input : Input) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics input).support) :
    (target.resumeAt 0).Equivalent (continuationEntry target.inputTape.bits) := by
  refine ⟨rfl, rfl, ?_, scratch_blank input target hTarget⟩
  rw [ciphertext input target hTarget]
  exact (exit_equivalent input target hTarget).2.2.1

theorem native_continuation {Observed : Type u} (context : Program) (horizon : Nat)
    (observe : Configuration → Observed)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second)
    (input : Input) :
    (link.native.execution.semantics input).bind (fun result =>
      (evalConfigWithin context (result.resumeAt 0) horizon).map observe) =
    (evalConfigWithin context (continuationEntry (OneTimePad.xorList input.key input.message)) horizon).map observe := by
  have h := link.component.continuation_observation (fun _ result => result.inputTape.bits)
    continuationEntry continuation_entry_equivalent context horizon observe invariant input
  dsimp only [TypedNativeComposition.Link.component] at h
  have hCipher : (link.native.execution.semantics input).map (fun result => result.inputTape.bits) =
      PMF.pure (OneTimePad.xorList input.key input.message) := by
    have hh := congrArg (fun distribution => distribution.map Prod.fst) (observation input)
    simpa only [PMF.map_comp, PMF.pure_map, Function.comp_def] using hh
  rw [hCipher, PMF.pure_bind] at h
  exact h

end Machine.CleanBlockMask
