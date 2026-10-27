/- Checkpoint 2026-10-28: the full build has not completed.
The user requested a checkpoint; the exhaustive neighbor check was interrupted.
This file is a proof candidate, not a completed validation artifact. -/
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitData

/-! Binary neighboring grid vertices: a sufficient superset of actual edges.
The exhaustive integer distance certificates are checked by the Lean kernel. -/
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

local instance (a b c : ℕ) (mask : Fin 8) : Decidable (neighborCheck a b c mask) := by
  unfold neighborCheck; infer_instance
local instance (a : ℕ) : Decidable (neighborRowCheck a) := by unfold neighborRowCheck; infer_instance
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem neighborRow_0_checked : neighborRowCheck 0 := by decide +kernel

theorem neighborRow_1_checked : neighborRowCheck 1 := by decide +kernel

theorem neighborRow_2_checked : neighborRowCheck 2 := by decide +kernel

theorem neighborRow_3_checked : neighborRowCheck 3 := by decide +kernel

theorem neighborRow_4_checked : neighborRowCheck 4 := by decide +kernel

theorem neighborRow_5_checked : neighborRowCheck 5 := by decide +kernel

theorem neighborRow_6_checked : neighborRowCheck 6 := by decide +kernel

theorem neighborRow_7_checked : neighborRowCheck 7 := by decide +kernel

theorem neighborRow_8_checked : neighborRowCheck 8 := by decide +kernel

theorem neighborRow_9_checked : neighborRowCheck 9 := by decide +kernel

theorem neighborRow_10_checked : neighborRowCheck 10 := by decide +kernel

theorem neighborRow_11_checked : neighborRowCheck 11 := by decide +kernel

theorem neighborRow_12_checked : neighborRowCheck 12 := by decide +kernel

theorem neighborRow_13_checked : neighborRowCheck 13 := by decide +kernel

theorem neighborRow_14_checked : neighborRowCheck 14 := by decide +kernel

theorem neighborRow_15_checked : neighborRowCheck 15 := by decide +kernel

theorem neighborRow_16_checked : neighborRowCheck 16 := by decide +kernel

theorem neighborRow_17_checked : neighborRowCheck 17 := by decide +kernel

theorem neighborRow_18_checked : neighborRowCheck 18 := by decide +kernel

theorem neighborRow_19_checked : neighborRowCheck 19 := by decide +kernel

theorem neighborRow_20_checked : neighborRowCheck 20 := by decide +kernel

theorem neighborRow_21_checked : neighborRowCheck 21 := by decide +kernel

theorem neighborRow_22_checked : neighborRowCheck 22 := by decide +kernel

theorem neighborRow_23_checked : neighborRowCheck 23 := by decide +kernel

theorem neighborRow_24_checked : neighborRowCheck 24 := by decide +kernel

theorem neighborRow_25_checked : neighborRowCheck 25 := by decide +kernel

theorem neighborRow_26_checked : neighborRowCheck 26 := by decide +kernel

theorem neighborRow_27_checked : neighborRowCheck 27 := by decide +kernel

theorem neighborRow_28_checked : neighborRowCheck 28 := by decide +kernel

theorem neighborRow_29_checked : neighborRowCheck 29 := by decide +kernel

theorem neighborRow_30_checked : neighborRowCheck 30 := by decide +kernel

theorem neighborRow_31_checked : neighborRowCheck 31 := by decide +kernel

theorem neighborRow_32_checked : neighborRowCheck 32 := by decide +kernel

theorem neighbors_checked (a b c : Fin 33) (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val)
    (mask : Fin 8) : neighborCheck a.val b.val c.val mask := by
  fin_cases a
  · exact neighborRow_0_checked b c hab hbc mask
  · exact neighborRow_1_checked b c hab hbc mask
  · exact neighborRow_2_checked b c hab hbc mask
  · exact neighborRow_3_checked b c hab hbc mask
  · exact neighborRow_4_checked b c hab hbc mask
  · exact neighborRow_5_checked b c hab hbc mask
  · exact neighborRow_6_checked b c hab hbc mask
  · exact neighborRow_7_checked b c hab hbc mask
  · exact neighborRow_8_checked b c hab hbc mask
  · exact neighborRow_9_checked b c hab hbc mask
  · exact neighborRow_10_checked b c hab hbc mask
  · exact neighborRow_11_checked b c hab hbc mask
  · exact neighborRow_12_checked b c hab hbc mask
  · exact neighborRow_13_checked b c hab hbc mask
  · exact neighborRow_14_checked b c hab hbc mask
  · exact neighborRow_15_checked b c hab hbc mask
  · exact neighborRow_16_checked b c hab hbc mask
  · exact neighborRow_17_checked b c hab hbc mask
  · exact neighborRow_18_checked b c hab hbc mask
  · exact neighborRow_19_checked b c hab hbc mask
  · exact neighborRow_20_checked b c hab hbc mask
  · exact neighborRow_21_checked b c hab hbc mask
  · exact neighborRow_22_checked b c hab hbc mask
  · exact neighborRow_23_checked b c hab hbc mask
  · exact neighborRow_24_checked b c hab hbc mask
  · exact neighborRow_25_checked b c hab hbc mask
  · exact neighborRow_26_checked b c hab hbc mask
  · exact neighborRow_27_checked b c hab hbc mask
  · exact neighborRow_28_checked b c hab hbc mask
  · exact neighborRow_29_checked b c hab hbc mask
  · exact neighborRow_30_checked b c hab hbc mask
  · exact neighborRow_31_checked b c hab hbc mask
  · exact neighborRow_32_checked b c hab hbc mask

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable
