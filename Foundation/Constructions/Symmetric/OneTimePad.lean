import Foundation.Crypto.Semantics.Probability.Comp
import Mathlib.Data.List.OfFn

/-! Fixed-length bitstrings and exact, information-theoretic secrecy of the
one-time pad. Keys are sampled afresh and uniformly for this one encryption. -/
namespace Foundation.Symmetric

open Foundation.Probability

abbrev Bits (length : Nat) := Fin length → Bool

namespace Bits

def xor {length : Nat} (x y : Bits length) : Bits length := fun i => Bool.xor (x i) (y i)

def toList {length : Nat} (x : Bits length) : List Bool := List.ofFn x

@[simp] theorem length_toList {length : Nat} (x : Bits length) : x.toList.length = length := by
  simp [toList]

@[simp] theorem xor_self_cancel {length : Nat} (key message : Bits length) :
    xor key (xor key message) = message := by
  funext i
  simp only [xor]
  cases key i <;> cases message i <;> rfl

@[simp] theorem xor_comm {length : Nat} (x y : Bits length) : xor x y = xor y x := by
  funext i
  simp only [xor]
  cases x i <;> cases y i <;> rfl

/-- Masking by a fixed message permutes the entire key space. -/
def xorEquiv {length : Nat} (message : Bits length) : Bits length ≃ Bits length where
  toFun := xor message
  invFun := xor message
  left_inv := xor_self_cancel message
  right_inv := xor_self_cancel message

/-- Exact equality of distributions, including length zero. -/
theorem uniform_xor {length : Nat} (message : Bits length) :
    (uniform (Bits length)).map (xor message) = uniform (Bits length) := by
  classical
  ext ciphertext
  rw [PMF.map_apply]
  have unique (key : Bits length) : ciphertext = xor message key ↔ key = xor message ciphertext := by
    constructor
    · intro h
      rw [h, xor_self_cancel]
    · intro h
      rw [h, xor_self_cancel]
  simp_rw [unique]
  simp [uniform]

end Bits

namespace OneTimePad

def encrypt {length : Nat} (key message : Bits length) : Bits length := Bits.xor key message

def decrypt {length : Nat} (key ciphertext : Bits length) : Bits length := Bits.xor key ciphertext

@[simp] theorem correctness {length : Nat} (key message : Bits length) :
    decrypt key (encrypt key message) = message := Bits.xor_self_cancel key message

noncomputable def ciphertext {length : Nat} (message : Bits length) : ProbComp (Bits length) :=
  (uniform (Bits length)).map (fun key => encrypt key message)

theorem ciphertext_uniform {length : Nat} (message : Bits length) :
    ciphertext message = uniform (Bits length) := by
  simpa [ciphertext, encrypt, Bits.xor_comm] using Bits.uniform_xor message

/-- Perfect secrecy against every probabilistic observer; there is no
computational restriction or approximation in this statement. -/
theorem perfect_secrecy {length : Nat} (left right : Bits length)
    (observer : Bits length → ProbComp Bool) :
    (ciphertext left).bind observer = (ciphertext right).bind observer := by
  rw [ciphertext_uniform, ciphertext_uniform]

end OneTimePad
end Foundation.Symmetric
