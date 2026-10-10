import Foundation.Quantum.QKD.PairwiseRawRecovery

/-! Restore the original attack's environment and original position labels
on the same measured phase-support certificate. The public mixture is exactly
the already constructed raw sampling approximant. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference PairwiseRecordedSampling
set_option backward.isDefEq.respectTransparency false

def rawDiscard {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n)) :=
  NestedDiscard.channel (.register (Fintype.card (RawProtocol.Output (BB84SiftedInput.selectedCount M))))
    (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e (PairwiseRecovery.krausSpace A)

def recoveredRaw {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  (rawDiscard A M).run
    (rawState (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M)
      k gap minKey tolerance c).density

theorem recoveredRaw_eq {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    (recoveredRaw A M k gap minKey tolerance c).matrix =
      (PairwiseRawPost.afterFirst (basis c) (BB84SiftedInput.auxiliary M e) c.2 minKey tolerance).toKraus.apply
        ((RetainedControl.channel (fun _ : Fin (count (BB84SiftedInput.selectedCount M)) =>
          (keyChannel (basis c)).amplify (BB84SiftedInput.auxiliary M e))).toKraus.apply
          ((first (basis c) (BB84SiftedInput.auxiliary M e)).toKraus.apply
            ((PairwiseRecovery.discard A M).toKraus.apply
              (SupportProjection.state (PairwiseQuantumSampling.good k gap c)
                (PairwiseAttackSampling.vector A M)
                (PairwiseQuantumSampling.fallback _ (PairwiseAttackSampling.unit A M))).matrix))) := by
  change (rawDiscard A M).toKraus.apply _ = _
  rw [rawState_physical]
  rw [rawDiscard, raw_record_recovery, ← record_key]
  rfl

def restoredRaw {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  (BB84SiftedInput.finish M (BB84SiftedInput.joinBases M (basis c,η)) e).run
    (recoveredRaw A M k gap minKey tolerance c)

theorem raw_ideal_eq {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis)
    (k gap minKey tolerance : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    (PairwiseRawSampling.ideal A M η k gap minKey tolerance hk).matrix =
      publicMixture (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk)
        (fun c => (restoredRaw A M η k gap minKey tolerance c).matrix) := by
  change (PairwiseRawSampling.finish M η e minKey tolerance).toKraus.apply
    ((PairwiseRecovery.keyRotation _ _).toKraus.apply
      (PairwiseRecovery.approximant A M k gap hk).matrix) = _
  rw [PairwiseRecovery.approximant_eq, PairwiseRecovery.keyRotation, RetainedControl.public_apply,
    PairwiseRawSampling.finish, RetainedControl.public_apply]
  apply congrArg (publicMixture (PairwiseSampling.distribution _ k hk))
  funext c
  simp only [Equiv.symm_apply_apply]
  change _ = (BB84SiftedInput.finish M (BB84SiftedInput.joinBases M (basis c,η)) e).toKraus.apply _
  rw [recoveredRaw_eq]
  simp only [PairwiseRawPost.restore, Channel.seq, Kraus.seq_apply, first]

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
