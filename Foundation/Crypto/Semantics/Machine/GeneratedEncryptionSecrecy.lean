import Foundation.Crypto.Semantics.Machine.GeneratedEncryptionResources
import Foundation.Crypto.Semantics.Machine.NativeContinuationSecurity

/-! Perfect secrecy of ciphertext and cell-invariant native continuations
for the actual fixed fresh-key encryption program, at every width including
zero. This does not expose the processing-time or encoded-layout metadata. -/
namespace Machine.GeneratedBlockEncryption
open Foundation.Probability Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false

theorem ciphertext_uniform {width : Nat} (message : Bits width) :
    (link.native.execution.semantics message.toList).map (fun state => state.inputTape.bits) =
      (uniform (Bits width)).map Bits.toList := by
  have hNative := ciphertext_distribution message.toList
  rw [hNative]
  rw [Bits.length_toList message]
  have hIdeal := congrArg (fun distribution => distribution.map (Bits.toList : Bits width → List Bool))
    (Foundation.Symmetric.OneTimePad.ciphertext_uniform message)
  simpa only [Foundation.Symmetric.OneTimePad.ciphertext, Foundation.Symmetric.OneTimePad.encrypt,
    PMF.map_comp, Function.comp_def, OneTimePad.toList_xor] using hIdeal

theorem perfect_secrecy {width : Nat} (left right : Bits width) (observer : List Bool → PMF Bool) :
    ((link.native.execution.semantics left.toList).map (fun state => state.inputTape.bits)).bind observer =
      ((link.native.execution.semantics right.toList).map (fun state => state.inputTape.bits)).bind observer := by
  rw [ciphertext_uniform, ciphertext_uniform]

def continuationEntry (ciphertext : List Bool) : Configuration :=
  {inputTape := ResponseExport.endTape ciphertext}

theorem continuation_entry_equivalent (message : List Bool) (target : Configuration)
    (hTarget : target ∈ (link.native.execution.semantics message).support) :
    (target.resumeAt 0).Equivalent (continuationEntry target.inputTape.bits) := by
  obtain ⟨key, h⟩ := supported_exit message target hTarget
  refine ⟨rfl, rfl, ?_, scratch_blank message target hTarget⟩
  have hBits := h.2.2.1.bits
  have hCipher : target.inputTape.bits = OneTimePad.xorList key.toList message := by
    change target.inputTape.bits = (ResponseExport.endTape (OneTimePad.xorList key.toList message)).bits at hBits
    have hEnd : (ResponseExport.endTape (OneTimePad.xorList key.toList message)).bits =
        OneTimePad.xorList key.toList message := by
      change (OneTimePad.finish 0 [] (OneTimePad.xorList key.toList message)).outputBits = _
      exact OneTimePad.finish_output _ _ _
    exact hBits.trans hEnd
  rw [hCipher]
  exact h.2.2.1

theorem native_continuation {width : Nat} (message : Bits width) {Observed : Type u}
    (context : Program) (horizon : Nat) (observe : Configuration → Observed)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second) :
    (link.native.execution.semantics message.toList).bind (fun result =>
      (evalConfigWithin context (result.resumeAt 0) horizon).map observe) =
    ((uniform (Bits width)).map Bits.toList).bind (fun ciphertext =>
      (evalConfigWithin context (continuationEntry ciphertext) horizon).map observe) := by
  have h := link.component.continuation_observation (fun _ result => result.inputTape.bits)
    continuationEntry continuation_entry_equivalent context horizon observe invariant message.toList
  dsimp only [TypedNativeComposition.Link.component] at h
  rw [ciphertext_uniform] at h
  exact h

theorem native_perfect_secrecy {width : Nat} (left right : Bits width) {Observed : Type u}
    (context : Program) (horizon : Nat) (observe : Configuration → Observed)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second) :
    (link.native.execution.semantics left.toList).bind (fun result =>
      (evalConfigWithin context (result.resumeAt 0) horizon).map observe) =
    (link.native.execution.semantics right.toList).bind (fun result =>
      (evalConfigWithin context (result.resumeAt 0) horizon).map observe) := by
  have hView : (link.native.execution.semantics left.toList).map (fun state => state.inputTape.bits) =
      (link.native.execution.semantics right.toList).map (fun state => state.inputTape.bits) := by
    rw [ciphertext_uniform, ciphertext_uniform]
  exact link.component.continuation_eq_of_view_eq (fun _ result => result.inputTape.bits)
    continuationEntry continuation_entry_equivalent left.toList right.toList hView context horizon observe invariant

theorem run_ciphertext_uniform {width : Nat} (message : Bits width) (horizon : Nat)
    (hTime : 61 * width + 40 ≤ horizon) :
    (evalConfigWithin link.code (Configuration.initial message.toList) horizon).map
      (fun state => state.inputTape.bits) = (uniform (Bits width)).map Bits.toList := by
  rw [run message.toList horizon (by simpa only [Bits.length_toList] using hTime), ciphertext_uniform]

theorem run_native_perfect_secrecy {width : Nat} (left right : Bits width)
    (encryptionHorizon : Nat) (hTime : 61 * width + 40 ≤ encryptionHorizon)
    {Observed : Type u} (context : Program) (horizon : Nat) (observe : Configuration → Observed)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second) :
    (evalConfigWithin link.code (Configuration.initial left.toList) encryptionHorizon).bind (fun result =>
      (evalConfigWithin context (result.resumeAt 0) horizon).map observe) =
    (evalConfigWithin link.code (Configuration.initial right.toList) encryptionHorizon).bind (fun result =>
      (evalConfigWithin context (result.resumeAt 0) horizon).map observe) := by
  rw [run left.toList encryptionHorizon (by simpa only [Bits.length_toList] using hTime),
    run right.toList encryptionHorizon (by simpa only [Bits.length_toList] using hTime)]
  exact native_perfect_secrecy left right context horizon observe invariant

end Machine.GeneratedBlockEncryption
