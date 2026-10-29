import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitSampler

/-! Three ordered six-bit grid coordinates and one plaintext bit form a request. -/
namespace Machine.EightBitCipherControl
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def encodeCoordinate (value : Fin 33) : Fin 6 → Bool :=
  (bitIndexEquiv 6).symm (value.castLE (by decide : 33 ≤ 2 ^ 6))

def request (v : OrderedGridVertex 32) (message : Bool) (j : Fin 19) : Bool :=
  if h0 : j.val < 6 then encodeCoordinate (v.val 0) ⟨j.val, h0⟩ else
  if h1 : j.val < 12 then encodeCoordinate (v.val 1) ⟨j.val - 6, by omega⟩ else
  if h2 : j.val < 18 then encodeCoordinate (v.val 2) ⟨j.val - 12, by omega⟩ else message

def block (position : Fin 3) (word : Fin 19 → Bool) (i : Fin 6) : Bool :=
  word ⟨6 * position.val + i.val, by have hp := position.isLt; have hi := i.isLt; omega⟩

theorem block_request (v : OrderedGridVertex 32) (message : Bool) (position : Fin 3) :
    block position (request v message) = encodeCoordinate (v.val position) := by
  funext i
  fin_cases position <;> fin_cases i <;> rfl

def pointOfOrdered (a b c : Fin 64)
    (h : a.val ≤ b.val ∧ b.val ≤ c.val ∧ c.val ≤ 32) : OrderedGridVertex 32 :=
  ⟨![⟨a.val, by omega⟩, ⟨b.val, by omega⟩, ⟨c.val, by omega⟩], h.1, h.2.1⟩

def parseRequest (word : Fin 19 → Bool) : Option (OrderedGridVertex 32 × Bool) :=
  let a := bitIndexEquiv 6 (block 0 word)
  let b := bitIndexEquiv 6 (block 1 word)
  let c := bitIndexEquiv 6 (block 2 word)
  if h : a.val ≤ b.val ∧ b.val ≤ c.val ∧ c.val ≤ 32 then
    some (pointOfOrdered a b c h, word 18)
  else none

theorem parseRequest_request (v : OrderedGridVertex 32) (message : Bool) :
    parseRequest (request v message) = some (v, message) := by
  have hvalid : (v.val 0).val ≤ (v.val 1).val ∧ (v.val 1).val ≤ (v.val 2).val ∧
      (v.val 2).val ≤ 32 := ⟨v.property.1, v.property.2, Nat.le_of_lt_succ (v.val 2).isLt⟩
  simp only [parseRequest, block_request, encodeCoordinate, Equiv.apply_symm_apply, Fin.val_castLE]
  rw [dif_pos hvalid]
  apply congrArg some
  apply Prod.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  · rfl

end Machine.EightBitCipherControl
