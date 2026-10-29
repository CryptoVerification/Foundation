import Foundation.Crypto.Semantics.Machine.NativeControlledEightBitCipher
import Foundation.Crypto.Semantics.Machine.TapeEquivalence

/-! The controlled cipher's observation law from ordinary raw input.
Extra represented blank cells are related by operational tape equivalence;
no normalization or free machine step is inserted. -/
namespace Machine.NativeControlledCipherInitial
open Foundation.Probability NativeBitDecisionTree
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

private def prepend (bit : Bool) (suffix : Tape) : Tape :=
  {left := suffix.left, current := some bit, right := suffix.current :: suffix.right}

private theorem preload_cons (bit : Bool) (bits : List Bool) (suffix : Tape) :
    preload (bit :: bits) suffix = prepend bit (preload bits suffix) := by
  cases bits <;> rfl

private theorem prepend_equivalent (bit : Bool) {s t : Tape} (h : s.Equivalent t) :
    (prepend bit s).Equivalent (prepend bit t) := by
  refine ⟨rfl, h.2.1, ?_⟩
  intro i
  cases i with
  | zero => exact h.1
  | succ i => exact h.2.2 i

theorem preload_equivalent (bits : List Bool) {s t : Tape} (h : s.Equivalent t) :
    (preload bits s).Equivalent (preload bits t) := by
  induction bits with
  | nil => exact h
  | cons bit bits ih =>
    rw [preload_cons, preload_cons]
    exact prepend_equivalent bit ih

theorem preload_empty (bits : List Bool) :
    (preload bits {}).Equivalent (Tape.ofBits bits) := by
  induction bits with
  | nil => exact Tape.Equivalent.refl _
  | cons bit bits ih =>
    rw [preload_cons]
    apply (prepend_equivalent bit ih).trans
    cases bits with
    | nil =>
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro i
      cases i <;> rfl
    | cons b bs => exact Tape.Equivalent.refl _

theorem blank_workspace :
    (NativeBitGenerator.blankBlock 8 (NativePrivateBitResult.keyBuffer {})).Equivalent {} := by
  exact Tape.blank_padding_equivalent [] 11

theorem entry_equivalent (v : OrderedGridVertex 32) (message : Bool) :
    (NativeControlledEightBitCipher.entry v message {} {}).Equivalent
      (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact (preload_equivalent _ blank_workspace).trans (preload_empty _)
  · exact Tape.blank_padding_equivalent [] 1

private def readResult (input output : List (Option Bool)) : Option ((Fin 3 → Bool) × Bool) :=
  match input.getD 0 none, input.getD 1 none, input.getD 2 none, output.getD 0 none with
  | some b2, some b1, some b0, some ciphertext => some (![b0,b1,b2],ciphertext)
  | _, _, _, _ => none

private theorem observe_readResult (c : Configuration) :
    NativeRandomPrivateResult.observe c = readResult c.inputTape.left c.outputTape.left := by
  unfold NativeRandomPrivateResult.observe
  cases hi : c.inputTape.left with
  | nil => rfl
  | cons b2 xs =>
    cases hx : xs with
    | nil => cases b2 <;> rfl
    | cons b1 ys =>
      cases hy : ys with
      | nil => cases b2 <;> cases b1 <;> rfl
      | cons b0 zs =>
        cases ho : c.outputTape.left with
        | nil => cases b2 <;> cases b1 <;> cases b0 <;> rfl
        | cons ct rest => cases b2 <;> cases b1 <;> cases b0 <;> cases ct <;> rfl

theorem observe_equivalent (c d : Configuration) (h : c.Equivalent d) :
    NativeEightBitCipher.observe c = NativeEightBitCipher.observe d := by
  unfold NativeEightBitCipher.observe
  rw [observe_readResult, observe_readResult]
  unfold readResult
  rw [h.2.2.1.2.1 0, h.2.2.1.2.1 1, h.2.2.1.2.1 2, h.2.2.2.2.1 0]

theorem law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativeControlledEightBitCipher.code
      (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) 148).map
      NativeEightBitCipher.observe = (tableEightBitLaw v message).map some := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (entry_equivalent v message).symm
    148 _ observe_equivalent]
  exact NativeControlledEightBitCipher.law v message {} {}

end Machine.NativeControlledCipherInitial
