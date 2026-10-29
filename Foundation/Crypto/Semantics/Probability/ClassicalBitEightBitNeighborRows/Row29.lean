import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitNeighborRows.Row28

namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

theorem neighborRow_29_checked : neighborRowCheck 29 := by
  unfold neighborRowCheck
  intro b
  fin_cases b <;> decide +kernel

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.EightBitTable
