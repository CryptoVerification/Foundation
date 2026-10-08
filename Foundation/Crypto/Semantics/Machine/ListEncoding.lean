import Foundation.Crypto.Semantics.Machine.Encoding

/-! A reusable faithful encoding of finite lists. Each element is framed;
the list terminator preserves empty elements and list boundaries. Decoder
fuel is bounded by the actual representation length, not an external proof. -/
namespace Machine.FiniteBitEncoding
universe u
variable {A : Type u}

def encodeList (E : FiniteBitEncoding A) : List A → List Bool
  | [] => [false]
  | x :: rest => true :: (delimit (E.encode x) ++ encodeList E rest)

def decodeListFuel (E : FiniteBitEncoding A) : Nat → List Bool → Option (List A)
  | 0, _ => none
  | _ + 1, [false] => some []
  | fuel + 1, true :: rest => match undelimit rest with
      | none => none
      | some (field, suffix) => (E.decode field).bind fun value =>
          (decodeListFuel E fuel suffix).map (value :: ·)
  | _ + 1, _ => none

theorem decodeListFuel_encodeList (E : FiniteBitEncoding A) (values : List A)
    (fuel : Nat) (hFuel : values.length + 1 ≤ fuel) :
    decodeListFuel E fuel (encodeList E values) = some values := by
  induction values generalizing fuel with
  | nil => cases fuel <;> simp_all [decodeListFuel, encodeList]
  | cons x rest ih =>
      cases fuel with
      | zero => simp at hFuel
      | succ fuel =>
          have ht : rest.length + 1 ≤ fuel := by simp only [List.length_cons] at hFuel; omega
          simp [encodeList, decodeListFuel, undelimit_delimit, E.decode_encode, ih fuel ht]

theorem encodeList_length (E : FiniteBitEncoding A) (values : List A) :
    (encodeList E values).length =
      2 * (values.map (fun x => (E.encode x).length)).sum + 2 * values.length + 1 := by
  induction values with
  | nil => rfl
  | cons x rest ih => simp [encodeList, ih]; omega

def list (E : FiniteBitEncoding A) : FiniteBitEncoding (List A) where
  encode := encodeList E
  decode := fun raw => decodeListFuel E raw.length raw
  decode_encode := by
    intro values
    apply decodeListFuel_encodeList
    rw [encodeList_length]
    omega

theorem list_encode_cons_length (E : FiniteBitEncoding A) (x : A) (rest : List A) :
    (E.list.encode (x :: rest)).length = 2 * (E.encode x).length + 2 + (E.list.encode rest).length := by
  simp [list, encodeList]
  omega

end Machine.FiniteBitEncoding
