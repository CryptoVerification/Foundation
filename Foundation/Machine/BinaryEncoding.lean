import Foundation.Machine.Adversary
import Mathlib.Data.Nat.Size

namespace Machine.Binary

/-- Fixed-width little-endian bits. Values outside the width are truncated.
This is a mathematical codec, not a unit-cost machine instruction. -/
def encode : Nat → Nat → List Bool
  | 0, _ => []
  | width + 1, value => (value % 2 = 1) :: encode width (value / 2)

/-- Numerical value of a little-endian bitstring. -/
def value : List Bool → Nat
  | [] => 0
  | bit :: rest => bit.toNat + 2 * value rest

@[simp] theorem encode_length (width n : Nat) : (encode width n).length = width := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih => simp [encode, ih]

theorem value_lt (bits : List Bool) : value bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [value]
  | cons bit rest ih =>
      cases bit <;> simp only [value, Bool.toNat_false, Bool.toNat_true,
        List.length_cons, Nat.pow_succ] <;> omega

@[simp] theorem value_encode {width n : Nat} (h : n < 2 ^ width) :
    value (encode width n) = n := by
  induction width generalizing n with
  | zero => simp at h; subst n; rfl
  | succ width ih =>
      have hDiv : n / 2 < 2 ^ width := by
        apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
        simpa [Nat.pow_succ, Nat.mul_comm] using h
      have hMod : (decide (n % 2 = 1)).toNat = n % 2 := by
        have hm := Nat.mod_lt n (by omega : 0 < 2)
        by_cases he : n % 2 = 1
        · simp [he]
        · simp [he]
          omega
      simp only [encode, value, ih hDiv, hMod]
      exact Nat.mod_add_div n 2

theorem value_append (first second : List Bool) :
    value (first ++ second) = value first + 2 ^ first.length * value second := by
  induction first with
  | nil => simp [value]
  | cons bit rest ih =>
      simp only [List.cons_append, value, ih, List.length_cons, Nat.pow_succ]
      ring

theorem value_canonical_lower (leading : List Bool) :
    2 ^ leading.length ≤ value (leading ++ [true]) := by
  simp [value_append, value]

@[simp] theorem encode_value (bits : List Bool) : encode bits.length (value bits) = bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      have hDiv : (bit.toNat + 2 * value rest) / 2 = value rest := by
        cases bit with
        | false => simp
        | true => simp; omega
      have hMod : decide ((bit.toNat + 2 * value rest) % 2 = 1) = bit := by
        cases bit <;> simp
      simpa only [List.length_cons, encode, value, hDiv, hMod] using congrArg (List.cons bit) ih

@[simp] theorem value_nat_bits (n : Nat) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit bit n h ih =>
      rw [Nat.bits_append_bit n bit h]
      cases bit <;> simp [value, ih, Nat.bit, Nat.add_comm]

/-- Positive natural numbers have a canonical binary code ending in one. -/
theorem nat_bits_canonical (n : Nat) (hn : n ≠ 0) :
    ∃ leading : List Bool, n.bits = leading ++ [true] := by
  induction n using Nat.binaryRec' with
  | zero => exact (hn rfl).elim
  | bit bit n h ih =>
      rw [Nat.bits_append_bit n bit h]
      by_cases hZero : n = 0
      · subst n
        have hBit := h rfl
        subst bit
        exact ⟨[], by simp⟩
      · obtain ⟨leading, hLeading⟩ := ih hZero
        exact ⟨bit :: leading, by simp [hLeading]⟩

/-- Fixed-width fair-bit assignments and numbers below `2^width` are in
bijection. This is a mathematical encoding equivalence, not a machine step. -/
noncomputable def bitsEquiv (width : Nat) : (Fin width → Bool) ≃ Fin (2 ^ width) := by
  let number : (Fin width → Bool) → Fin (2 ^ width) := fun bits =>
    ⟨value (List.ofFn bits), by simpa using value_lt (List.ofFn bits)⟩
  apply Equiv.ofBijective number
  constructor
  · intro first second h
    apply List.ofFn_injective
    have hv := congrArg Fin.val h
    have hFirst : encode width (value (List.ofFn first)) = List.ofFn first := by
      simpa only [List.length_ofFn] using encode_value (List.ofFn first)
    have hSecond : encode width (value (List.ofFn second)) = List.ofFn second := by
      simpa only [List.length_ofFn] using encode_value (List.ofFn second)
    exact hFirst.symm.trans ((congrArg (encode width) hv).trans hSecond)
  · intro x
    let code := encode width x.val
    let bits : Fin width → Bool := fun i => code[i.val]'(by simp [code])
    have hBits : List.ofFn bits = code := by
      apply List.ext_getElem
      · simp [code]
      · intro i hFirst hSecond
        simp [bits]
    refine ⟨bits, Fin.ext ?_⟩
    change value (List.ofFn bits) = x.val
    rw [hBits]
    exact value_encode x.isLt

@[simp] theorem bitsEquiv_val (width : Nat) (bits : Fin width → Bool) :
    (bitsEquiv width bits).val = value (List.ofFn bits) := rfl

/-- Finite domains use the same fixed width. Invalid widths and values are
rejected by the mathematical decoder. -/
def fin (q width : Nat) (h : q ≤ 2 ^ width) : FiniteBitEncoding (Fin q) where
  encode x := encode width x.val
  decode bits :=
    if hWidth : bits.length = width then
      if hValue : value bits < q then some ⟨value bits, hValue⟩ else none
    else none
  decode_encode := by
    intro x
    simp only [encode_length, ↓reduceDIte, value_encode (x.isLt.trans_le h)]
    simp

@[simp] theorem fin_encode_length (q width : Nat) (h : q ≤ 2 ^ width) (x : Fin q) :
    ((fin q width h).encode x).length = width := encode_length _ _

end Machine.Binary
