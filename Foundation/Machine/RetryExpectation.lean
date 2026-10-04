import Foundation.Machine.LimitExecution
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace Machine

open scoped ENNReal

/-- A geometric bound on timeout at fixed-size inspection blocks gives an
expected bound on actual transitions. Post-halt inspection stutters are not
charged, because the tail sum counts only configurations still running. -/
theorem expectedSteps_le_of_timeout_blocks {p : Program} {input : List Bool}
    (block : Nat) [NeZero block] (ratio : ℝ≥0∞)
    (h : ∀ trials : Nat,
      timeoutProbability p input (trials * block) ≤ ratio ^ trials) :
    expectedSteps p input ≤ (block : ℝ≥0∞) * (1 - ratio)⁻¹ := by
  have hEach (steps : Nat) : timeoutProbability p input steps ≤ ratio ^ (steps / block) := by
    exact (timeoutProbability_antitone p input (Nat.div_mul_le_self steps block)).trans
      (h (steps / block))
  calc
    expectedSteps p input ≤ ∑' steps : Nat, ratio ^ (steps / block) :=
      ENNReal.tsum_le_tsum hEach
    _ = ∑' pair : Nat × Fin block, ratio ^ pair.1 := by
      simpa using (Nat.divModEquiv block).tsum_eq
        (fun pair : Nat × Fin block => ratio ^ pair.1)
    _ = (block : ℝ≥0∞) * (1 - ratio)⁻¹ := by
      rw [ENNReal.tsum_prod']
      simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- Validation and physical tape preparation cost actual transitions before
the geometric retry blocks begin. -/
theorem expectedSteps_le_of_timeout_blocks_after {p : Program} {input : List Bool}
    (preparation block : Nat) [NeZero block] (ratio : ℝ≥0∞)
    (h : ∀ trials : Nat,
      timeoutProbability p input (preparation + trials * block) ≤ ratio ^ trials) :
    expectedSteps p input ≤ (preparation : ℝ≥0∞) +
      (block : ℝ≥0∞) * (1 - ratio)⁻¹ := by
  have hEach (steps : Nat) : timeoutProbability p input (steps + preparation) ≤
      ratio ^ (steps / block) := by
    exact (timeoutProbability_antitone p input (by
      have := Nat.div_mul_le_self steps block
      omega : preparation + (steps / block) * block ≤ steps + preparation)).trans
      (h (steps / block))
  have hTail : (∑' steps : Nat, timeoutProbability p input (steps + preparation)) ≤
      (block : ℝ≥0∞) * (1 - ratio)⁻¹ := by
    calc
      _ ≤ ∑' steps : Nat, ratio ^ (steps / block) := ENNReal.tsum_le_tsum hEach
      _ = ∑' pair : Nat × Fin block, ratio ^ pair.1 := by
        simpa using (Nat.divModEquiv block).tsum_eq
          (fun pair : Nat × Fin block => ratio ^ pair.1)
      _ = _ := by
        rw [ENNReal.tsum_prod']
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  unfold expectedSteps
  rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := preparation)]
  apply add_le_add _ hTail
  calc
    _ ≤ ∑ _steps ∈ Finset.range preparation, (1 : ℝ≥0∞) :=
      Finset.sum_le_sum (fun steps _ => timeoutProbability_le_one p input steps)
    _ = _ := by simp

end Machine
