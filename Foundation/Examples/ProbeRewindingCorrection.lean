import Foundation.Examples.LocalRewindingCompiler

/-! Arithmetic of the one-probe correction. The unknown continuation mass is
not an input to the executable sampler: a pilot query implements its affine
acceptance probability. Operational and full-transcript proofs are separate. -/

namespace Foundation.Examples.ProbeRewindingCorrection

open Foundation.Examples.LocalRewindingCompiler
open scoped BigOperators

theorem probe_acceptance (p mass : ℚ) :
    (1 - mass) + mass * p = retryDenominator p mass := by
  unfold retryDenominator
  ring

theorem probe_probability_bounds (p mass : ℚ) (pPositive : 0 < p) (pUpper : p ≤ 1)
    (massNonnegative : 0 ≤ mass) (massUpper : mass ≤ 1) :
    0 < retryDenominator p mass ∧ retryDenominator p mass ≤ 1 := by
  have lower := denominator_lower p mass pUpper massUpper
  have product := mul_nonneg (sub_nonneg.mpr pUpper) massNonnegative
  constructor
  · linarith
  · dsimp [retryDenominator]
    linarith

theorem probe_cancels_restart (base output p mass : ℚ)
    (nonzero : retryDenominator p mass ≠ 0) :
    base * retryDenominator p mass * (output * p / retryDenominator p mass) =
      base * output * p := by
  field_simp

theorem output_after_normalization (lawA lawB p guesses mass : ℚ)
    (denominatorNonzero : retryDenominator p mass ≠ 0)
    (pNonzero : p ≠ 0) (guessesNonzero : guesses ≠ 0) :
    ((lawA / guesses) * retryDenominator p mass *
      (lawB * p / retryDenominator p mass)) / (p / guesses) = lawA * lawB := by
  rw [probe_cancels_restart _ _ _ _ denominatorNonzero]
  field_simp

theorem sum_retry_denominators {C : Type*} [Fintype C] (p : ℚ) (mass : C → ℚ)
    (normalized : ∑ c, mass c = 1) :
    (∑ c, retryDenominator p (mass c)) = (Fintype.card C : ℚ) - 1 + p := by
  simp only [retryDenominator, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [normalized]
  simp
  ring

theorem total_challenge_cost (p guesses : ℚ) (pNonzero : p ≠ 0)
    (guessesNonzero : guesses ≠ 0) :
    (2 + 1 / guesses) / (p / guesses) = (2 * guesses + 1) / p := by
  field_simp

theorem pilot_challenge_cost (p guesses : ℚ) (pNonzero : p ≠ 0)
    (guessesNonzero : guesses ≠ 0) :
    1 / (p / guesses) = guesses / p := by
  field_simp

end Foundation.Examples.ProbeRewindingCorrection
