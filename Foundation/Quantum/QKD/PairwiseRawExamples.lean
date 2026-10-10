import Foundation.Quantum.QKD.PairwiseRandomizedSampling

/-! Concrete coherent copying attack in the complete independently randomized
BB84 raw experiment. This is an approximation theorem, not key secrecy. -/
namespace Foundation.Quantum.QKD.PairwiseRandomizedSampling
noncomputable section
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal

theorem one_signal_max : PairwiseSampling.maxBadCount 1 1 1 = 0 := by decide

theorem one_signal_error : PairwiseSampling.errorBound 1 1 1 = 0 := by
  unfold PairwiseSampling.errorBound
  rw [one_signal_max]
  simp

/-- Four equally likely match sets: insufficient samples contribute zero;
the single matched signal has zero integer-gap error; the full pair has 1/2. -/
theorem two_signal_total_error : error 2 1 1 = (1/4:ℝ) * Real.sqrt (1/2:ℝ) := by
  have hall : (Finset.univ : Finset (Finset (Fin 2))) = {∅,{0},{1},{0,1}} := by decide
  unfold error
  rw [hall]
  norm_num [conditionalError, BB84SiftedInput.selectedCount_eq_card,
    Foundation.Probability.uniform, PMF.uniformOfFintype_apply,
    PairwiseSampling.two_signal_error, one_signal_error]

theorem attacked_randomized :
    StateApprox
      ((discardMiddle (.register (Fintype.card (RawProtocol.Output 2))) (qubits 2) (qubits 2)).run
        (Randomized.record PairwiseAttackExamples.attack 1 1 0))
      (ideal PairwiseAttackExamples.attack 1 1 1 0) ((1/4:ℝ) * Real.sqrt (1/2:ℝ)) := by
  have h := approximation PairwiseAttackExamples.attack 1 1 1 0
  rw [two_signal_total_error] at h
  exact h

/-- Forgetting private keys preserves the same bound for the actual original
public transcript and quantum Eve, including every abort branch. -/
theorem attacked_public :
    StateApprox (Randomized.publicState PairwiseAttackExamples.attack 1 1 0)
      ((BB84DeferredRaw.publicChannel 2 (qubits 2)).run
        (ideal PairwiseAttackExamples.attack 1 1 1 0)) ((1/4:ℝ) * Real.sqrt (1/2:ℝ)) := by
  have h := public_approximation PairwiseAttackExamples.attack 1 1 1 0
  rw [two_signal_total_error] at h
  exact h

end
end Foundation.Quantum.QKD.PairwiseRandomizedSampling
