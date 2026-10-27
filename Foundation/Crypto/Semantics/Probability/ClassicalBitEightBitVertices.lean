import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitData

/-! Exhaustive kernel checks of all ordered triples in the N=32 vertex table.
Every row proof uses decide +kernel; no native reduction axiom is admitted. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable
local instance (a b c : ℕ) : Decidable (boundary a b c) := by unfold boundary; infer_instance
local instance (a b c : ℕ) : Decidable (vertexCheck a b c) := by unfold vertexCheck; infer_instance
local instance (a : ℕ) : Decidable (vertexRowCheck a) := by unfold vertexRowCheck; infer_instance
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem vertexRow_0_checked : vertexRowCheck 0 := by decide +kernel

theorem vertexRow_1_checked : vertexRowCheck 1 := by decide +kernel

theorem vertexRow_2_checked : vertexRowCheck 2 := by decide +kernel

theorem vertexRow_3_checked : vertexRowCheck 3 := by decide +kernel

theorem vertexRow_4_checked : vertexRowCheck 4 := by decide +kernel

theorem vertexRow_5_checked : vertexRowCheck 5 := by decide +kernel

theorem vertexRow_6_checked : vertexRowCheck 6 := by decide +kernel

theorem vertexRow_7_checked : vertexRowCheck 7 := by decide +kernel

theorem vertexRow_8_checked : vertexRowCheck 8 := by decide +kernel

theorem vertexRow_9_checked : vertexRowCheck 9 := by decide +kernel

theorem vertexRow_10_checked : vertexRowCheck 10 := by decide +kernel

theorem vertexRow_11_checked : vertexRowCheck 11 := by decide +kernel

theorem vertexRow_12_checked : vertexRowCheck 12 := by decide +kernel

theorem vertexRow_13_checked : vertexRowCheck 13 := by decide +kernel

theorem vertexRow_14_checked : vertexRowCheck 14 := by decide +kernel

theorem vertexRow_15_checked : vertexRowCheck 15 := by decide +kernel

theorem vertexRow_16_checked : vertexRowCheck 16 := by decide +kernel

theorem vertexRow_17_checked : vertexRowCheck 17 := by decide +kernel

theorem vertexRow_18_checked : vertexRowCheck 18 := by decide +kernel

theorem vertexRow_19_checked : vertexRowCheck 19 := by decide +kernel

theorem vertexRow_20_checked : vertexRowCheck 20 := by decide +kernel

theorem vertexRow_21_checked : vertexRowCheck 21 := by decide +kernel

theorem vertexRow_22_checked : vertexRowCheck 22 := by decide +kernel

theorem vertexRow_23_checked : vertexRowCheck 23 := by decide +kernel

theorem vertexRow_24_checked : vertexRowCheck 24 := by decide +kernel

theorem vertexRow_25_checked : vertexRowCheck 25 := by decide +kernel

theorem vertexRow_26_checked : vertexRowCheck 26 := by decide +kernel

theorem vertexRow_27_checked : vertexRowCheck 27 := by decide +kernel

theorem vertexRow_28_checked : vertexRowCheck 28 := by decide +kernel

theorem vertexRow_29_checked : vertexRowCheck 29 := by decide +kernel

theorem vertexRow_30_checked : vertexRowCheck 30 := by decide +kernel

theorem vertexRow_31_checked : vertexRowCheck 31 := by decide +kernel

theorem vertexRow_32_checked : vertexRowCheck 32 := by decide +kernel

theorem vertices_checked (a b c : Fin 33) (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    vertexCheck a.val b.val c.val := by
  fin_cases a
  · exact vertexRow_0_checked b c hab hbc
  · exact vertexRow_1_checked b c hab hbc
  · exact vertexRow_2_checked b c hab hbc
  · exact vertexRow_3_checked b c hab hbc
  · exact vertexRow_4_checked b c hab hbc
  · exact vertexRow_5_checked b c hab hbc
  · exact vertexRow_6_checked b c hab hbc
  · exact vertexRow_7_checked b c hab hbc
  · exact vertexRow_8_checked b c hab hbc
  · exact vertexRow_9_checked b c hab hbc
  · exact vertexRow_10_checked b c hab hbc
  · exact vertexRow_11_checked b c hab hbc
  · exact vertexRow_12_checked b c hab hbc
  · exact vertexRow_13_checked b c hab hbc
  · exact vertexRow_14_checked b c hab hbc
  · exact vertexRow_15_checked b c hab hbc
  · exact vertexRow_16_checked b c hab hbc
  · exact vertexRow_17_checked b c hab hbc
  · exact vertexRow_18_checked b c hab hbc
  · exact vertexRow_19_checked b c hab hbc
  · exact vertexRow_20_checked b c hab hbc
  · exact vertexRow_21_checked b c hab hbc
  · exact vertexRow_22_checked b c hab hbc
  · exact vertexRow_23_checked b c hab hbc
  · exact vertexRow_24_checked b c hab hbc
  · exact vertexRow_25_checked b c hab hbc
  · exact vertexRow_26_checked b c hab hbc
  · exact vertexRow_27_checked b c hab hbc
  · exact vertexRow_28_checked b c hab hbc
  · exact vertexRow_29_checked b c hab hbc
  · exact vertexRow_30_checked b c hab hbc
  · exact vertexRow_31_checked b c hab hbc
  · exact vertexRow_32_checked b c hab hbc

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable
