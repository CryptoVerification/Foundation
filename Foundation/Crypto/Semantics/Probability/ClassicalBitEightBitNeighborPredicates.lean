import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitData

/-! Shared predicates for the kernel-checked sliced neighbor certificates. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable
open scoped BigOperators

def neighborIncrement (mask : Fin 8) (j : Fin 3) : ℕ :=
  if j.val = 0 then mask.val % 2 else if j.val = 1 then (mask.val / 2) % 2 else (mask.val / 4) % 2

def neighborCheck (a b c : ℕ) (mask : Fin 8) : Prop :=
  let aa := a+neighborIncrement mask 0
  let bb := b+neighborIncrement mask 1
  let cc := c+neighborIncrement mask 2
  aa ≤ bb → bb ≤ cc → cc ≤ 32 →
    (∑ k : Fin 5, |counts a b c k.val-counts aa bb cc k.val|) ≤ 148

def neighborRowCheck (a : ℕ) : Prop :=
  ∀ b c : Fin 33, a ≤ b.val → b.val ≤ c.val → ∀ mask : Fin 8, neighborCheck a b.val c.val mask

instance neighborCheckDecidable (a b c : ℕ) (mask : Fin 8) : Decidable (neighborCheck a b c mask) := by
  unfold neighborCheck; infer_instance
instance neighborRowCheckDecidable (a : ℕ) : Decidable (neighborRowCheck a) := by
  unfold neighborRowCheck; infer_instance

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable
