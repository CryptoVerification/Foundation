import Foundation.Machine.Adversary

namespace Machine.FiniteBitEncoding

universe u v

/-- Prefix-free framing of a finite bitstring. Every data bit is preceded by
`true`, and a final `false` ends the field. This is a mathematical encoding;
the machine-step cost of producing it is not claimed here. -/
def delimit : List Bool → List Bool
  | [] => [false]
  | bit :: rest => true :: bit :: delimit rest

/-- Split one delimited field from the remaining bits. -/
def undelimit : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: bit :: rest =>
      (undelimit rest).map fun (field, tail) => (bit :: field, tail)
  | _ => none

@[simp] theorem undelimit_delimit (bits tail : List Bool) :
    undelimit (delimit bits ++ tail) = some (bits, tail) := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      simpa [delimit, undelimit] using ih

theorem undelimit_tail_length_le (bits field tail : List Bool)
    (h : undelimit bits = some (field, tail)) :
    tail.length ≤ bits.length := by
  match bits with
  | [] => simp [undelimit] at h
  | false :: rest =>
      simp [undelimit] at h
      have hlen := congrArg List.length h.2
      simp only [List.length_cons]
      omega
  | [true] => simp [undelimit] at h
  | true :: bit :: rest =>
      simp only [undelimit, Option.map_eq_some_iff] at h
      obtain ⟨pair, hPair, hValue⟩ := h
      rcases pair with ⟨inner, leftover⟩
      cases hValue
      have hle := undelimit_tail_length_le rest inner leftover hPair
      simp
      omega
termination_by bits.length

@[simp] theorem delimit_length (bits : List Bool) :
    (delimit bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      simp [delimit, ih]
      omega

/-- Product coding with a self-delimiting first component. -/
def prod {α : Type u} {β : Type v}
    (E : FiniteBitEncoding α) (D : FiniteBitEncoding β) :
    FiniteBitEncoding (α × β) where
  encode pair := delimit (E.encode pair.1) ++ D.encode pair.2
  decode bits :=
    match undelimit bits with
    | none => none
    | some (first, second) =>
        match E.decode first, D.decode second with
        | some x, some y => some (x, y)
        | _, _ => none
  decode_encode := by
    intro ⟨x, y⟩
    simp [E.decode_encode, D.decode_encode]

@[simp] theorem prod_encode_length {α : Type u} {β : Type v}
    (E : FiniteBitEncoding α) (D : FiniteBitEncoding β) (x : α) (y : β) :
    ((E.prod D).encode (x, y)).length =
      2 * (E.encode x).length + 1 + (D.encode y).length := by
  simp [prod]

/-- Decoding a product cannot make the second component larger than its
remaining bit field, provided its decoder has that size property. -/
theorem prod_decode_right_size_le {α : Type u} {β : Type v}
    (E : FiniteBitEncoding α) (D : FiniteBitEncoding β)
    (size : β → Nat)
    (hD : ∀ bits y, D.decode bits = some y → size y ≤ bits.length)
    (bits : List Bool) (x : α) (y : β)
    (h : (E.prod D).decode bits = some (x, y)) :
    size y ≤ bits.length := by
  cases hSplit : undelimit bits with
  | none => simp [prod, hSplit] at h
  | some pair =>
      rcases pair with ⟨first, second⟩
      cases hFirst : E.decode first with
      | none => simp [prod, hSplit, hFirst] at h
      | some x' =>
          cases hSecond : D.decode second with
          | none => simp [prod, hSplit, hFirst, hSecond] at h
          | some y' =>
              simp [prod, hSplit, hFirst, hSecond] at h
              cases h.1
              cases h.2
              exact (hD second y hSecond).trans
                (undelimit_tail_length_le bits first second hSplit)

/-- One prefix bit distinguishes the two alternatives. -/
def sum {α : Type u} {β : Type v}
    (E : FiniteBitEncoding α) (D : FiniteBitEncoding β) :
    FiniteBitEncoding (α ⊕ β) where
  encode
    | .inl x => false :: E.encode x
    | .inr y => true :: D.encode y
  decode
    | false :: rest => (E.decode rest).map Sum.inl
    | true :: rest => (D.decode rest).map Sum.inr
    | [] => none
  decode_encode := by
    intro value
    cases value with
    | inl x => simp [E.decode_encode]
    | inr y => simp [D.decode_encode]

@[simp] theorem sum_encode_inl_length {α : Type u} {β : Type v}
    (E : FiniteBitEncoding α) (D : FiniteBitEncoding β) (x : α) :
    ((E.sum D).encode (.inl x)).length = (E.encode x).length + 1 := by
  rfl

@[simp] theorem sum_encode_inr_length {α : Type u} {β : Type v}
    (E : FiniteBitEncoding α) (D : FiniteBitEncoding β) (y : β) :
    ((E.sum D).encode (.inr y)).length = (D.encode y).length + 1 := by
  rfl

/-- A triple of values uses the same finite element code three times. -/
def triple {α : Type u} (E : FiniteBitEncoding α) :
    FiniteBitEncoding (α × α × α) := E.prod (E.prod E)

/-- Each component code of length at most `limit` yields a triple code of
length at most `5 * limit + 2`. -/
theorem triple_encode_length_le {α : Type u}
    (E : FiniteBitEncoding α) (limit : Nat)
    (h : ∀ x : α, (E.encode x).length ≤ limit)
    (x y z : α) :
    ((E.triple).encode (x, y, z)).length ≤ 5 * limit + 2 := by
  have hx := h x
  have hy := h y
  have hz := h z
  simp only [triple, prod_encode_length]
  omega

end Machine.FiniteBitEncoding
