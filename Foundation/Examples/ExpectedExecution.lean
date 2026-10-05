import Foundation.Crypto.Semantics.Machine.ExpectedExecution
import Foundation.Examples.BitMachineExecution

namespace Machine.Examples

open Foundation.Probability

/-- Tail index zero counts the halt instruction itself. -/
example (input : List Bool) : expectedSteps haltImmediately input = 1 := by
  apply le_antisymm
  · simpa using expectedSteps_le_of_haltsWithin (haltImmediately_haltsWithin input)
  · have hZero : timeoutProbability haltImmediately input 0 = 1 := by
      simp [timeoutProbability, eventProb, evalWithin, evalConfigWithin,
        Configuration.initial, PMF.pure_map]
    rw [← hZero]
    exact ENNReal.le_tsum 0

example : ExpectedPolynomialTime haltImmediately := by
  apply PolynomialTime.expectedPolynomialTime
  exact ⟨fun _ => 1, PolynomiallyBounded.const 1, haltImmediately_haltsWithin⟩

example (input : List Bool) : AlmostSureHalts haltImmediately input := by
  apply almostSureHalts_of_expectedSteps_ne_top
  exact ne_of_lt ((expectedSteps_le_of_haltsWithin
    (haltImmediately_haltsWithin input)).trans_lt (by simp))

/-- A fair output bit and a halt are two operational transitions. -/
example : expectedSteps randomOutputBit [] ≤ 2 :=
  expectedSteps_le_of_haltsWithin randomOutputBit_haltsWithin

end Machine.Examples
