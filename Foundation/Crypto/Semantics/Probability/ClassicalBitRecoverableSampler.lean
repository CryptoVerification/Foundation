import Foundation.Crypto.Semantics.Probability.ClassicalBitRecoverableCoupling
import Foundation.Crypto.Semantics.Probability.ClassicalBitDyadicSampler

/-! Seven fair bits realize the repaired conditional key law exactly. Every
coin word decodes back to the original source bit; no rejection is needed. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoverableSampler
open Foundation.Probability
open scoped ENNReal

def sample (bit : Bool) (coins : Fin 7 → Bool) : Fin 5 :=
  sampleCounts (Recoverable.counts bit) (by simpa using Recoverable.counts_sum bit) (bitIndexEquiv 7 coins)

theorem sample_probability (bit : Bool) (key : Fin 5) :
    eventProb (uniform (Fin 7 → Bool)) (fun coins => sample bit coins = key) =
      (Recoverable.counts bit key : ℝ≥0∞) / 128 := by
  simpa only [sample, Nat.reducePow, Nat.cast_ofNat] using
    sampleCounts_bits_event_probability 7 (Recoverable.counts bit) (by simpa using Recoverable.counts_sum bit) key

theorem sample_law (bit : Bool) : (uniform (Fin 7 → Bool)).map (sample bit) = Recoverable.forward bit := by
  classical
  ext key
  apply (ENNReal.toReal_eq_toReal_iff' (((uniform (Fin 7 → Bool)).map (sample bit)).apply_ne_top key)
    ((Recoverable.forward bit).apply_ne_top key)).mp
  rw [← Recoverable.singleton, eventProb_map, sample_probability, Recoverable.forward_real]
  norm_num [ENNReal.toReal_div]

theorem sample_parent (bit : Bool) (coins : Fin 7 → Bool) : Recoverable.parent (sample bit coins) = bit := by
  have positive : 0 < Recoverable.counts bit (sample bit coins) := by
    change 0 < Recoverable.counts bit
      ((countSampleEquiv (Recoverable.counts bit) (by simpa using Recoverable.counts_sum bit)) (bitIndexEquiv 7 coins)).1
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (((countSampleEquiv (Recoverable.counts bit)
      (by simpa using Recoverable.counts_sum bit)) (bitIndexEquiv 7 coins)).2).isLt
  exact Recoverable.counts_compatible bit _ (Nat.ne_of_gt positive)

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.RecoverableSampler
