import Foundation.Quantum.QKD.PairwiseSampling

/-! Exact finite checks for the pairwise sampler. These show the error bound
is derived from the real joint choices and is not an arbitrary assumed bound. -/
namespace Foundation.Quantum.QKD.PairwiseSampling
noncomputable section
open scoped ENNReal
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

theorem two_signal_max : maxBadCount 2 1 1 = 4 := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro q _
    have h : ∀ q : Pattern 2, badCount 2 1 1 q ≤ 4 := by decide
    exact h q
  · have h : badCount 2 1 1 (fun ij => ij.2) = 4 := by decide
    rw [← h]
    exact Finset.le_sup (Finset.mem_univ _)

theorem two_signal_configurations : (configurations 2 1).card = 8 := by decide

theorem two_signal_error : errorBound 2 1 1 = (1/2:ℝ≥0∞) := by
  unfold errorBound
  rw [two_signal_max, two_signal_configurations]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
  norm_num

end
end Foundation.Quantum.QKD.PairwiseSampling
