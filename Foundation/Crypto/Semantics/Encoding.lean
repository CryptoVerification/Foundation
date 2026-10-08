import Mathlib.Data.Option.Basic

/-! Faithful semantic representations with explicit malformed-input failure.
Encoding and decoding are observations; execution costs require a separate
implementation certificate. -/
namespace Foundation
universe u v w x

structure Encoding (Value : Type u) (Representation : Type v) where
  encode : Value → Representation
  decode : Representation → Option Value
  roundtrip : ∀ value, decode (encode value) = some value

namespace Encoding
variable {A : Type u} {B : Type v} {C : Type w} {D : Type x}

def identity (A : Type u) : Encoding A A := ⟨id, some, fun _ => rfl⟩

def comp (first : Encoding A B) (second : Encoding B C) : Encoding A C where
  encode := second.encode ∘ first.encode
  decode := fun raw => (second.decode raw).bind first.decode
  roundtrip := by intro value; simp [first.roundtrip, second.roundtrip]

theorem encode_injective (codec : Encoding A B) : Function.Injective codec.encode := by
  intro a b h
  have hd := congrArg codec.decode h
  simpa only [codec.roundtrip, Option.some.injEq] using hd

def prod (left : Encoding A B) (right : Encoding C D) : Encoding (A × C) (B × D) where
  encode := fun value => (left.encode value.1, right.encode value.2)
  decode := fun raw => (left.decode raw.1).bind fun a => (right.decode raw.2).map fun c => (a, c)
  roundtrip := by intro value; simp [left.roundtrip, right.roundtrip]

def option (codec : Encoding A B) : Encoding (Option A) (Option B) where
  encode := Option.map codec.encode
  decode := fun raw => match raw with
    | none => some none
    | some bytes => (codec.decode bytes).map some
  roundtrip := by intro value; cases value <;> simp [codec.roundtrip]

/-- A legitimate failure response is distinct from malformed bytes. -/
@[simp] theorem option_decode_none (codec : Encoding A B) : codec.option.decode none = some none := rfl

/-- Total observations may choose a default, while the faithful partial
codec keeps invalid encodings explicit. -/
def observe (codec : Encoding A B) (default : A) (raw : B) : A := (codec.decode raw).getD default

@[simp] theorem observe_encode (codec : Encoding A B) (default value : A) :
    codec.observe default (codec.encode value) = value := by
  simp [observe, codec.roundtrip]

@[simp] theorem comp_identity (codec : Encoding A B) : codec.comp (identity B) = codec := by
  cases codec
  rfl

@[simp] theorem identity_comp (codec : Encoding A B) : (identity A).comp codec = codec := by
  cases codec
  simp [comp, identity, Function.comp_def]

theorem comp_assoc (first : Encoding A B) (second : Encoding B C) (third : Encoding C D) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  cases first; cases second; cases third
  simp [comp, Function.comp_def, Option.bind_assoc]

/-- A single tag distinguishes legitimate failure from success, including
success with an empty payload. Extra bits after a failure tag are malformed. -/
def optionBits (codec : Encoding A (List Bool)) : Encoding (Option A) (List Bool) where
  encode := fun value => match value with
    | none => [false]
    | some value => true :: codec.encode value
  decode := fun raw => match raw with
    | [false] => some none
    | true :: payload => (codec.decode payload).map some
    | _ => none
  roundtrip := by intro value; cases value <;> simp [codec.roundtrip]

@[simp] theorem optionBits_failure (codec : Encoding A (List Bool)) :
    codec.optionBits.decode [false] = some none := rfl

@[simp] theorem optionBits_empty (codec : Encoding A (List Bool)) :
    codec.optionBits.decode [] = none := rfl

@[simp] theorem optionBits_failure_junk (codec : Encoding A (List Bool))
    (bit : Bool) (rest : List Bool) :
    codec.optionBits.decode (false :: bit :: rest) = none := rfl

@[simp] theorem optionBits_success (codec : Encoding A (List Bool)) (payload : List Bool) :
    codec.optionBits.decode (true :: payload) = (codec.decode payload).map some := rfl

theorem optionBits_length (codec : Encoding A (List Bool)) (value : Option A) :
    (codec.optionBits.encode value).length = 1 + ((value.map codec.encode).getD []).length := by
  cases value <;> simp [optionBits, Nat.add_comm]

end Encoding
end Foundation
