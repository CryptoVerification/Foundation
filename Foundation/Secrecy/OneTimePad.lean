import Mathlib.Data.ZMod.Basic
import Foundation.Secrecy.Basic

namespace Secrecy

open SymmetricEncryption

/-- The classical one-time pad over bitstrings of length `n`. -/
def oneTimePad (n : ℕ) :
    SymmetricEncryption (Fin n → ZMod 2) (Fin n → ZMod 2) (Fin n → ZMod 2) where
  enc k m := k + m
  dec k c := c - k
  correct k m := by
    funext i
    simp

@[simp]
lemma oneTimePad_enc (n : ℕ) (k m : Fin n → ZMod 2) :
    (oneTimePad n).enc k m = k + m :=
  rfl

@[simp]
lemma oneTimePad_dec (n : ℕ) (k c : Fin n → ZMod 2) :
    (oneTimePad n).dec k c = c - k :=
  rfl

lemma oneTimePad_ciphertextCount (n : ℕ) (m c : Fin n → ZMod 2) :
    ciphertextCount (oneTimePad n) m c = 1 := by
  classical
  have hEquiv :
      ({ k : Fin n → ZMod 2 //
          (oneTimePad n).enc k m = c } ≃ Unit) := by
    refine
      { toFun := fun _ => ()
        , invFun := fun _ => ⟨c - m, by simp [oneTimePad]⟩
        , left_inv := ?_
        , right_inv := ?_ }
    · intro k
      apply Subtype.ext
      have hk := congrArg (fun f => f - m) k.property
      simpa [oneTimePad] using hk.symm
    · intro u
      cases u
      simp
  have hCard := Fintype.card_congr hEquiv
  simpa [ciphertextCount] using hCard

lemma oneTimePad_perfectSecrecy (n : ℕ) :
    perfectSecrecy (oneTimePad n) := by
  classical
  refine (perfectSecrecy_iff_card (scheme := oneTimePad n)).2 ?_
  intro m₁ m₂ c
  simp [oneTimePad_ciphertextCount]

end Secrecy
