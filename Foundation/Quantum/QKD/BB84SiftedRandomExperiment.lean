import Foundation.Quantum.QKD.BB84SiftedFullRecord

/-! The error-first selected experiment is the actual entire randomized BB84
raw experiment, with the unmatched signals and Bob's final signal discarded.
Eve, public records, abort flags and both private raw keys are retained. -/
namespace Foundation.Quantum.QKD.BB84SiftedInput
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : Nonempty BB84Basis := ⟨.Z⟩

def delayedRecord {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Density (BB84MixedPreparedRaw.recordSpace n e) :=
  Density.mixture (Foundation.Probability.uniform (Finset (Fin n))) (fun M =>
    Density.mixture (Foundation.Probability.uniform (Fin (selectedCount M) → BB84Basis)) (fun θ =>
      Density.mixture (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis)) (fun η =>
        Density.mixture
          (BB84SiftingRandomness.testDistribution (Finset.univ : Finset (Fin (selectedCount M))) k)
          (fun S => (delayedOutput M (joinBases M (θ,η)) e S
            (BB84SiftingRandomness.requiredLength M k minKey) tolerance).run (input A M)))))

/-- All distribution branches, including insufficient samples, are preserved. -/
theorem delayed_reindexed {n : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :
    (delayedRecord A k minKey tolerance).matrix =
      ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
        (reindexedRecord A k minKey tolerance)).matrix := by
  unfold delayedRecord reindexedRecord
  rw [Density.mixture_channel]
  apply Density.mixture_congr_matrix
  intro M
  rw [Density.mixture_channel]
  apply Density.mixture_congr_matrix
  intro θ
  rw [Density.mixture_channel]
  apply Density.mixture_congr_matrix
  intro η
  rw [Density.mixture_channel]
  apply Density.mixture_congr_matrix
  intro S
  exact delayed_source A M (joinBases M (θ,η)) S
    (BB84SiftingRandomness.requiredLength M k minKey) tolerance

/-- The interpreted selected derivation agrees with the full original
randomized preparation experiment, after physically discarding Bob. -/
theorem delayed_record_eq {n : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :
    (delayedRecord A k minKey tolerance).matrix =
      ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
        (Randomized.record A k minKey tolerance)).matrix := by
  rw [delayed_reindexed]
  change (discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).toKraus.apply _ = _
  rw [reindexed_record_eq]
  rfl

/-- The public state includes quantum correlations with the original Eve,
without exposing the unmatched signals as extra adversarial output. -/
theorem delayed_public_eq {n : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :
    ((BB84DeferredRaw.publicChannel n e).run (delayedRecord A k minKey tolerance)).matrix =
      (Randomized.publicState A k minKey tolerance).matrix := by
  change (BB84DeferredRaw.publicChannel n e).toKraus.apply _ = _
  rw [delayed_record_eq]
  change (BB84DeferredRaw.publicChannel n e).toKraus.apply
    ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).toKraus.apply
      (Randomized.record A k minKey tolerance).matrix) = _
  rw [show (Randomized.publicState A k minKey tolerance).matrix =
    (RawProtocol.publicChannel n e).toKraus.apply (Randomized.record A k minKey tolerance).matrix from rfl,
    RawProtocol.publicChannel, Channel.seq, Kraus.seq_apply]
  exact (classicalMap_discardMiddle (qubits n) e _ _).symm

end
end Foundation.Quantum.QKD.BB84SiftedInput
