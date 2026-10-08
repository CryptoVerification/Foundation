import Foundation.Crypto.Semantics.Machine.OneTimePad

/-! Length laws for the executable list XOR, independent of encryption,
key sampling or a particular native implementation. -/
namespace Machine.OneTimePad

theorem xorList_length (key message : List Bool) (hLength : key.length = message.length) :
    (xorList key message).length = message.length := by
  induction key generalizing message with
  | nil => have hm := List.length_eq_zero_iff.mp hLength.symm; subst message; rfl
  | cons bit rest ih =>
      cases message with
      | nil => simp at hLength
      | cons m messages => simp only [xorList, List.length_cons, ih messages (by simpa using hLength)]

end Machine.OneTimePad
