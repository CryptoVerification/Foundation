import Foundation.Quantum.QKD.PairwiseRecovery
import Foundation.Quantum.QKD.PairwiseRecordedExamples
import Foundation.Quantum.NestedDiscardRecord

/-! Recover the original finite-Kraus attacked measurement experiment after
tracing only the purification environment, and carry the sampling error to
that same recovered joint state. Public selector/test and error records stay. -/
namespace Foundation.Quantum.QKD.PairwiseRecovery
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference PairwiseRecordedSampling
set_option backward.isDefEq.respectTransparency false

def discardRecord {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n)) :=
  RetainedControl.channel (fun _ : Fin (count (BB84SiftedInput.selectedCount M)) => discard A M)

def recover {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n)) :=
  RetainedControl.channel
    (fun _ : Fin (Fintype.card (PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))) =>
      discardRecord A M)

theorem record {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin (BB84SiftedInput.selectedCount M) → BB84Basis)
    (ρ : Operator (jointSpace (BB84SiftedInput.selectedCount M)
      (BB84SiftedInput.auxiliary M (PairwiseAttackSampling.environment A)))) :
    (discardRecord A M).toKraus.apply
      ((PartitionMeasurement.instrument (errorLabel θ)).record.toKraus.apply ρ) =
      (PartitionMeasurement.instrument (errorLabel θ)).record.toKraus.apply ((discard A M).toKraus.apply ρ) :=
  NestedDiscard.record
    (a := BB84SiftedInput.signalSpace (BB84SiftedInput.selectedCount M))
    (b := BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M))
    (e := e) (r := krausSpace A)
    (fun p => Fintype.equivFin _ (BB84ErrorTransform.errorBits θ p)) ρ

/-- This is the original attack, with its original auxiliary system, in the
selected fixed-reference detailed-measurement experiment. -/
def actual {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    Density (output (BB84SiftedInput.selectedCount M) (BB84SiftedInput.auxiliary M e)) where
  matrix := publicMixture (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk)
    (fun c => ((PartitionMeasurement.instrument (errorLabel (basis c))).record.run
      (referenceInput (BB84SiftedInput.input A M))).matrix)
  positive := publicMixture_positive _ _ (fun _ => (Channel.run _ _).positive)
  normalized := by
    rw [publicMixture_trace]
    simp only [(Channel.run _ _).normalized, mul_one]
    norm_cast
    exact Density.probability_weights _

theorem actual_eq {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    ((recover A M).run (real (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M) k hk)).matrix =
      (actual A M k hk).matrix := by
  change (recover A M).toKraus.apply _ = _
  rw [attacked_real, recover, RetainedControl.public_apply]
  apply congrArg (publicMixture (PairwiseSampling.distribution _ k hk))
  funext c
  rw [record, reference]
  rfl

def approximant {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :=
  (recover A M).run (ideal (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M) k gap hk)

/-- A constructed normalized approximant to the original attack's measured
joint state. No recovery equation or privacy premise is assumed. -/
theorem recovered_approximation {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    StateApprox (actual A M k hk) (approximant A M k gap hk)
      (Real.sqrt (PairwiseSampling.errorBound (BB84SiftedInput.selectedCount M) k gap).toReal) := by
  have h := (attacked_approximation A M k gap hk).postprocess (recover A M)
  change OperatorApprox
    ((recover A M).run (real (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M) k hk)).matrix
    (approximant A M k gap hk).matrix _ at h
  rw [actual_eq A M k hk] at h
  exact h

end
end Foundation.Quantum.QKD.PairwiseRecovery
