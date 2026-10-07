import Foundation.Crypto.Semantics.Encoding
import Mathlib.Data.List.OfFn

/-! Faithful encodings of fixed-width vectors, over arbitrary element types.
Malformed lengths fail decoding; length zero is a valid empty vector. -/
namespace Foundation.Encoding
universe u

def vector (Value : Type u) (width : Nat) : Encoding (Fin width → Value) (List Value) where
  encode := List.ofFn
  decode := fun raw => if h : raw.length = width then
    some (fun i => raw[i.val]'(by omega)) else none
  roundtrip := by
    intro value
    simp only [List.length_ofFn, dite_true, Option.some.injEq]
    funext i
    simp

@[simp] theorem vector_encode {Value : Type u} (width : Nat) (value : Fin width → Value) :
    (vector Value width).encode value = List.ofFn value := rfl

theorem vector_decode_bad_length {Value : Type u} (width : Nat) (raw : List Value)
    (h : raw.length ≠ width) : (vector Value width).decode raw = none := by
  simp [vector, h]

end Foundation.Encoding
