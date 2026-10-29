import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitNeighborRows.Row32

/-! All binary neighbor certificates; the import chain keeps row builds serial. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable

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
