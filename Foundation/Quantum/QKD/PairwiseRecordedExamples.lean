import Foundation.Quantum.QKD.PairwiseRecordedSampling
import Foundation.Quantum.QKD.PairwiseAttackExamples

/-! Actual arbitrary block attacks and a concrete coherent two-signal attack
in the selector-controlled, fully retained measurement experiment. -/
namespace Foundation.Quantum.QKD.PairwiseRecordedSampling
noncomputable section
open PureProjection BB84DelayedMeasurements
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

/-- The real operator here is the actual purified attacked fixed-reference
state followed by the selector-controlled detailed error measurement. -/
theorem attacked_real {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    (real (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M) k hk).matrix =
      publicMixture (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk)
        (fun c => (PartitionMeasurement.instrument (errorLabel (basis c))).record.toKraus.apply
          (PairwiseAttackSampling.state A M).matrix) := by
  rw [real_eq, PairwiseAttackSampling.pure]

theorem attacked_approximation {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    StateApprox
      (real (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M) k hk)
      (ideal (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M) k gap hk)
      (Real.sqrt (PairwiseSampling.errorBound (BB84SiftedInput.selectedCount M) k gap).toReal) :=
  approximation _ _ _ _ _

theorem attacked_interpreted {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    (QuantumSamplingLogic.model
      (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk)
      (PairwiseQuantumSampling.good k gap) (PairwiseAttackSampling.vector A M)
      (PairwiseAttackSampling.unit A M)
      (fun _ => PairwiseQuantumSampling.fallback _ (PairwiseAttackSampling.unit A M))
      (fun _ => measurement _ _)).Carrier
        (.processed 0 (Real.sqrt (PairwiseSampling.errorBound
          (BB84SiftedInput.selectedCount M) k gap).toReal)) := interpreted _ _ _ _ _

/-- A genuine coherent attack; the large small-block error is retained. This
is not a claim that two signals produce a secure final key. -/
theorem two_signal_approximation :
    StateApprox
      (real (PairwiseAttackSampling.vector PairwiseAttackExamples.attack Finset.univ)
        (PairwiseAttackSampling.unit _ _) 1 (by simp [BB84SiftedInput.selectedCount]))
      (ideal (PairwiseAttackSampling.vector PairwiseAttackExamples.attack Finset.univ)
        (PairwiseAttackSampling.unit _ _) 1 1 (by simp [BB84SiftedInput.selectedCount]))
      (Real.sqrt (1/2:ℝ)) := by
  exact PairwiseAttackExamples.approximation.postprocess (measurement _ _)

end
end Foundation.Quantum.QKD.PairwiseRecordedSampling
