import Foundation.Quantum.QKD.PairwiseRawPost

/-! Quantum sampling error for the actual prepare/attack/raw-output experiment,
with the finite pair selector and test set still public. This includes accept
and abort, original-position restoration, and the actual quantum adversary. -/
namespace Foundation.Quantum.QKD.PairwiseRawSampling
noncomputable section
open BB84DelayedMeasurements PairwiseRecordedSampling PairwiseRawPost
set_option backward.isDefEq.respectTransparency false

abbrev rawSpace (n : Nat) (e : Space) :=
  Space.tensor (.register (Fintype.card (RawProtocol.Output n))) e

def finish {n : Nat} (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) (e : Space) (minKey tolerance : Nat) :
    Channel (output (BB84SiftedInput.selectedCount M) (BB84SiftedInput.auxiliary M e))
      (Guessing.publicSpace (PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (rawSpace n e)) :=
  RetainedControl.channel (fun t =>
    let c := (Fintype.equivFin (PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))).symm t
    restore M (basis c) η e c.2 minKey tolerance)

def real {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis)
    (k minKey tolerance : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :=
  (finish M η e minKey tolerance).run (PairwiseRecovery.original A M k hk)

def ideal {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis)
    (k gap minKey tolerance : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :=
  (finish M η e minKey tolerance).run (PairwiseRecovery.originalApproximant A M k gap hk)

/-- The real side is exactly the original prepared experiment, not an
abstract protocol or a state postulated to satisfy the desired conclusion. -/
theorem real_eq {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis)
    (k minKey tolerance : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    (real A M η k minKey tolerance hk).matrix =
      publicMixture (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk)
        (fun c => (BB84MixedPreparedRaw.prepared A (BB84SiftedInput.joinBases M (basis c,η))
          (BB84SiftingRandomness.bobBases (BB84SiftedInput.joinBases M (basis c,η)) M)
          (BB84SiftedInput.liftTest M c.2) minKey tolerance).matrix) := by
  change (finish M η e minKey tolerance).toKraus.apply _ = _
  rw [PairwiseRecovery.original_eq, finish, RetainedControl.public_apply]
  apply congrArg (publicMixture (PairwiseSampling.distribution _ k hk))
  funext c
  simp only [Equiv.symm_apply_apply]
  exact restored_prepared A M (basis c) η c.2 minKey tolerance

/-- No division by acceptance: this is the entire normalized joint output,
including abort with erased keys and all public/quantum correlations. -/
theorem approximation {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis)
    (k gap minKey tolerance : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    StateApprox (real A M η k minKey tolerance hk) (ideal A M η k gap minKey tolerance hk)
      (Real.sqrt (PairwiseSampling.errorBound (BB84SiftedInput.selectedCount M) k gap).toReal) :=
  (PairwiseRecovery.original_approximation A M k gap hk).postprocess (finish M η e minKey tolerance)

/-- The same finite sampling derivation is interpreted with the actual
measurement, environment recovery, key rotation and full raw-output channel. -/
theorem interpreted {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis)
    (k gap minKey tolerance : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    (QuantumSamplingLogic.model
      (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk)
      (PairwiseQuantumSampling.good k gap) (PairwiseAttackSampling.vector A M)
      (PairwiseAttackSampling.unit A M)
      (fun _ => PairwiseQuantumSampling.fallback _ (PairwiseAttackSampling.unit A M))
      (fun _ => (((measurement _ _).seq (PairwiseRecovery.recover A M)).seq
        (PairwiseRecovery.keyRotation _ _)).seq (finish M η e minKey tolerance))).Carrier
        (.processed 0 (Real.sqrt (PairwiseSampling.errorBound
          (BB84SiftedInput.selectedCount M) k gap).toReal)) := by
  apply QuantumSamplingLogic.sound _ _ _ (PairwiseAttackSampling.unit A M) _ _
    (QuantumSamplingLogic.proof 0 (PairwiseSampling.errorBound _ k gap).toReal)
  intro _
  exact PairwiseQuantumSampling.classical k gap hk

end
end Foundation.Quantum.QKD.PairwiseRawSampling
