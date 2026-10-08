import Foundation.Crypto.Semantics.Machine.Basic

/-! Length of the contiguous bit block at a tape head. Cells beyond its
first blank and arbitrary saved cells to the left are not traversed. -/
namespace Machine.Tape

def presentPrefixLength : List (Option Bool) → Nat
  | [] => 0
  | none :: _ => 0
  | some _ :: rest => presentPrefixLength rest + 1

def bitSpan (tape : Tape) : Nat := presentPrefixLength (tape.current :: tape.right)

@[simp] theorem bitSpan_none (tape : Tape) (h : tape.current = none) : tape.bitSpan = 0 := by
  simp [bitSpan, h, presentPrefixLength]

@[simp] theorem bitSpan_some (tape : Tape) (bit : Bool) (h : tape.current = some bit) :
    tape.bitSpan = presentPrefixLength tape.right + 1 := by
  simp [bitSpan, h, presentPrefixLength]

@[simp] theorem bitSpan_moveRight (tape : Tape) : tape.moveRight.bitSpan = presentPrefixLength tape.right := by
  cases h : tape.right <;> simp [bitSpan, moveRight, h, presentPrefixLength]

@[simp] theorem presentPrefixLength_block (bits : List Bool) (after : List (Option Bool)) :
    presentPrefixLength (bits.map some ++ none :: after) = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp [presentPrefixLength, ih]

@[simp] theorem presentPrefixLength_map (bits : List Bool) :
    presentPrefixLength (bits.map some) = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp [presentPrefixLength, ih]

@[simp] theorem bitSpan_ofBits (bits : List Bool) : (ofBits bits).bitSpan = bits.length := by
  cases bits <;> simp [ofBits, bitSpan, presentPrefixLength]

@[simp] theorem bitSpan_with_left (tape : Tape) (before : List (Option Bool)) :
    ({tape with left := before} : Tape).bitSpan = tape.bitSpan := rfl

end Machine.Tape
