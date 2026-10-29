import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitCountTest

/-! The sharp edge already has its full variation in the key distribution.
A two-label predicate ignores ciphertext and attains the same gap. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open Foundation.Probability
open scoped BigOperators ENNReal

def keyPairTest (result : Fin 5 × Bool) : Bool := decide (result.1 = 0 ∨ result.1 = 2)

theorem event_real_count (v : OrderedGridVertex 32) (message : Bool) (test : (Fin 5 × Bool) → Bool) :
    (eventProb ((tableEightBitLaw v message).map test) (· = true)).toReal =
      ((∑ result, if test result = true then tableAtomCount v message result else 0 : ℕ) : ℝ) / 256 := by
  rw [eventProb_map, event_real_sum, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro result _
  rw [table_atom_real_count]
  by_cases h : test result = true <;> simp [h]

theorem keyPair_counts_first (message : Bool) :
    (∑ result, if keyPairTest result = true then tableAtomCount (sharpTableChain 0) message result else 0) = 256 := by
  cases message <;> decide +kernel

theorem keyPair_counts_second (message : Bool) :
    (∑ result, if keyPairTest result = true then tableAtomCount (sharpTableChain 2) message result else 0) = 182 := by
  cases message <;> decide +kernel

theorem keyPair_probability_first (message : Bool) :
    (eventProb ((tableEightBitLaw (sharpTableChain 0) message).map keyPairTest) (· = true)).toReal = 1 := by
  rw [event_real_count, keyPair_counts_first]
  norm_num

theorem keyPair_probability_second (message : Bool) :
    (eventProb ((tableEightBitLaw (sharpTableChain 2) message).map keyPairTest) (· = true)).toReal = 91 / 128 := by
  rw [event_real_count, keyPair_counts_second]
  norm_num

theorem keyPair_gap (message : Bool) :
    probabilityGap (eventProb ((tableEightBitLaw (sharpTableChain 0) message).map keyPairTest) (· = true))
      (eventProb ((tableEightBitLaw (sharpTableChain 2) message).map keyPairTest) (· = true)) = (37 / 128 : ℝ≥0∞) := by
  rw [probabilityGap_eq_ofReal_abs _ _
    (ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp)))
    (ne_of_lt ((eventProb_le_one _ _).trans_lt (by simp))),
    keyPair_probability_first, keyPair_probability_second]
  norm_num
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
