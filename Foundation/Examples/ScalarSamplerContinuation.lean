import Foundation.Crypto.Semantics.Machine.ScalarSamplerContinuationDistribution

namespace Foundation.Examples.ScalarSamplerContinuation

open Machine
open scoped ENNReal

/-- A tiny modulus and a much wider public code do not cause exponential
expected work: the native sampler draws only canonical modulus bits. -/
example : expectedStepsFrom Machine.ScalarSamplerContinuation.program
    (RejectionSampling.Saved.initial (List.replicate 6 (some true)) (3 : Nat).bits) ≤ (350 : ℝ≥0∞) := by
  simpa using Machine.ScalarSamplerContinuation.expectedSteps_nat 6 3 (by decide) (by decide)

/-- The whole retained-tape code, including physical padding and its final
halt instruction, has exactly the uniform fixed-width residue law. -/
example (output : List Bool) :
    outputMassFrom Machine.ScalarSamplerContinuation.program
      (RejectionSampling.Saved.initial (List.replicate 6 (some true)) (3 : Nat).bits) output =
      ((Probability.uniform (Fin 3)).map (fun a => Binary.encode 6 a.val)) output := by
  exact Machine.ScalarSamplerContinuation.outputMass_nat 6 3 (by decide) (by decide) output

/-- Ordinary evaluation after a retry inspection and the charged padding
budget retains the same geometric upper bound on nontermination. -/
example (trials : Nat) :
    ((evalConfigWithin Machine.ScalarSamplerContinuation.program
      (RejectionSampling.Saved.initial (List.replicate 6 (some true)) [true,true])
      (114+trials*27)).map (fun c => if c.halted then some c.outputBits else none)) none ≤
        (2⁻¹ : ℝ≥0∞)^trials := by
  have bound := Machine.ScalarSamplerContinuation.timeout_after_trials_le 6 [true]
    (by decide) (by decide) trials
  have budget : RejectionSampling.preparationSteps ([true]++[true]) +
      trials*(10*([true]++[true]).length+7)+(13*6+18) = 114+trials*27 := by
    simp [RejectionSampling.preparationSteps]
    omega
  rw [budget] at bound
  simpa only [List.cons_append, List.nil_append] using bound

end Foundation.Examples.ScalarSamplerContinuation
