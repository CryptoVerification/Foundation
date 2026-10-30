import Mathlib

/-! Integer certificate over all 3125 deterministic five-state decoders.
The probabilistic interpretation is proved in ClassicalBitRecoveryError. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError
open scoped BigOperators

def sourceCounts : Fin 5 → ℕ := ![43,43,42,111,17]
def targetCounts : Fin 5 → ℕ := ![45,44,39,111,17]
def assignedCounts (decoder : Fin 5 → Fin 5) (a : Fin 5) : ℕ :=
  ∑ b, if decoder b = a then targetCounts b else 0
def retainedCounts (decoder : Fin 5 → Fin 5) : ℕ :=
  ∑ a, min (sourceCounts a) (assignedCounts decoder a)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem decoder_certificate : ∀ a b c d e : Fin 5, retainedCounts ![a,b,c,d,e] ≤ 253 := by
  decide +kernel

theorem all_decoder_counts (decoder : Fin 5 → Fin 5) : retainedCounts decoder ≤ 253 := by
  have eta : ![decoder 0,decoder 1,decoder 2,decoder 3,decoder 4] = decoder := by
    funext i
    fin_cases i <;> rfl
  rw [← eta]
  exact decoder_certificate _ _ _ _ _

theorem identity_counts : retainedCounts id = 253 := by decide +kernel

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoveryError
