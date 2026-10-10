import Foundation.Quantum.QKD.PairwiseRecoveredFirst

/-! A concrete coherent two-signal attack after recovery and the original
BB84 first measurement, and its finite derivation interpretation. -/
namespace Foundation.Quantum.QKD.PairwiseRecovery
noncomputable section
open PairwiseRecordedSampling
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal

theorem original_interpreted {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    (QuantumSamplingLogic.model
      (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk)
      (PairwiseQuantumSampling.good k gap) (PairwiseAttackSampling.vector A M)
      (PairwiseAttackSampling.unit A M)
      (fun _ => PairwiseQuantumSampling.fallback _ (PairwiseAttackSampling.unit A M))
      (fun _ => ((measurement _ _).seq (recover A M)).seq
        (keyRotation (BB84SiftedInput.selectedCount M) (BB84SiftedInput.auxiliary M e)))).Carrier
        (.processed 0 (Real.sqrt (PairwiseSampling.errorBound
          (BB84SiftedInput.selectedCount M) k gap).toReal)) := by
  apply QuantumSamplingLogic.sound _ _ _ (PairwiseAttackSampling.unit A M) _ _
    (QuantumSamplingLogic.proof 0 (PairwiseSampling.errorBound _ k gap).toReal)
  intro _
  exact PairwiseQuantumSampling.classical k gap hk

/-- The approximation applies after physically discarding the added dilation
label and applying the actual key-side rotation of the original first stage. -/
theorem two_signal_original :
    StateApprox
      (original PairwiseAttackExamples.attack (Finset.univ : Finset (Fin 2)) 1
        (by simp [BB84SiftedInput.selectedCount]))
      (originalApproximant PairwiseAttackExamples.attack (Finset.univ : Finset (Fin 2)) 1 1
        (by simp [BB84SiftedInput.selectedCount])) (Real.sqrt (1/2:ℝ)) := by
  have h := original_approximation PairwiseAttackExamples.attack
    (Finset.univ : Finset (Fin 2)) 1 1 (by simp [BB84SiftedInput.selectedCount])
  have he : PairwiseSampling.errorBound
      (BB84SiftedInput.selectedCount (Finset.univ : Finset (Fin 2))) 1 1 = (1/2:ℝ≥0∞) := by
    have hc : BB84SiftedInput.selectedCount (Finset.univ : Finset (Fin 2)) = 2 := by
      simp [BB84SiftedInput.selectedCount]
    rw [hc]
    exact PairwiseSampling.two_signal_error
  rw [he] at h
  simpa using h

end
end Foundation.Quantum.QKD.PairwiseRecovery
