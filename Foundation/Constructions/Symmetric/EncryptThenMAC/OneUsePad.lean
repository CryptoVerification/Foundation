import Foundation.Constructions.Symmetric.EncryptThenMAC.OneUsePrivacy
import Foundation.Constructions.Symmetric.OneTimePad

/-! Arbitrary-width one-use encryption instantiates the general adaptive
privacy theorem. The width can be any function of the security parameter,
including zero; the exhaustion state prevents reuse of the same pad. -/
namespace Foundation.Symmetric.EncryptThenMAC.OneUsePad
open Foundation.Probability CryptoOracle

noncomputable def scheme (width : Nat → Nat) : Encryption where
  Key := fun n => Bits (width n)
  State := fun _ => Bool
  Message := fun n => Bits (width n)
  Ciphertext := fun n => Bits (width n)
  keygen := fun n => uniform (Bits (width n))
  initial := fun _ => false
  encrypt := fun _ key used message => (true, if used then none else some (OneTimePad.encrypt key message))
  decrypt := fun _ key ciphertext => some (OneTimePad.decrypt key ciphertext)
  correctness := by
    intro n key used message ciphertext h
    cases used
    · simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
      subst ciphertext
      exact congrArg some (OneTimePad.correctness key message)
    · simp at h

noncomputable def privacyContract (width : Nat → Nat) : OneUsePrivacy (scheme width) where
  exhausted := fun _ => true
  ciphertext := fun _ key message => OneTimePad.encrypt key message
  distribution := fun n => uniform (Bits (width n))
  first := by intros; rfl
  used := by intros; rfl
  law := fun _ message => OneTimePad.ciphertext_uniform message

theorem game_perfect (width : Nat → Nat) (n : Nat)
    (attacks : PMF (EncryptionAttack (scheme width) n)) :
    encryptionGame (scheme width) n false attacks = encryptionGame (scheme width) n true attacks :=
  (privacyContract width).game_perfect n attacks

theorem advantage_zero (width : Nat → Nat) (n : Nat)
    (attacks : PMF (EncryptionAttack (scheme width) n)) :
    (encryptionGoal (scheme width)).advantage n () attacks = 0 :=
  (privacyContract width).advantage_zero n attacks

theorem privacy_perfect (width : Nat → Nat) (M : MAC (scheme width).Ciphertext)
    (n : Nat) (attack : PrivacyAttack (scheme width) M n) :
    privacyGame (scheme width) M n false attack = privacyGame (scheme width) M n true attack :=
  (privacyContract width).privacy_perfect M n attack

end Foundation.Symmetric.EncryptThenMAC.OneUsePad
