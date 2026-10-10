import Foundation.Quantum.QKD.BB84SiftedOutput

/-! Exact test reindexing in the actual randomized quantum record and a
physical classical restoration applied to the interpreted selected experiment.
Their final composition through unmatched measurement and discard is proved
in BB84SiftedFullRecord and BB84SiftedRandomExperiment. -/
namespace Foundation.Quantum.QKD.BB84SiftedInput
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : Nonempty BB84Basis := ⟨.Z⟩

def reindexedRecord {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Density (BB84RawSource.outputSpace n e) :=
  Density.mixture (Foundation.Probability.uniform (Finset (Fin n))) (fun M =>
    Density.mixture (Foundation.Probability.uniform (Fin (selectedCount M) → BB84Basis)) (fun θ =>
      Density.mixture (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis)) (fun η =>
        Density.mixture
          (BB84SiftingRandomness.testDistribution (Finset.univ : Finset (Fin (selectedCount M))) k)
          (fun S => BB84RawSource.state A (joinBases M (θ,η))
            (BB84SiftingRandomness.bobBases (joinBases M (θ,η)) M) (liftTest M S)
            (BB84SiftingRandomness.requiredLength M k minKey) tolerance))))

/-- Includes all basis/test choices, actual attack, transcript and quantum
systems. The impossible-sample branch is preserved as well. -/
theorem reindexed_record_eq {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    (reindexedRecord A k minKey tolerance).matrix = (Randomized.record A k minKey tolerance).matrix := by
  rw [record_split_eq]
  apply Density.mixture_congr_matrix
  intro M
  apply Density.mixture_congr_matrix
  intro θ
  apply Density.mixture_congr_matrix
  intro η
  rw [← testDistribution_lift M k, Density.mixture_map]

theorem reindexed_public_eq {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    ((RawProtocol.publicChannel n e).run (reindexedRecord A k minKey tolerance)).matrix =
      (Randomized.publicState A k minKey tolerance).matrix :=
  congrArg (RawProtocol.publicChannel n e).toKraus.apply (reindexed_record_eq A k minKey tolerance)

def restoreChannel {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis) (e : Space) :=
  classicalMap e (fun r : Fin (Fintype.card (RawProtocol.Output (selectedCount M))) =>
    Fintype.equivFin (RawProtocol.Output n)
      (restoreOutput M θ ((Fintype.equivFin (RawProtocol.Output (selectedCount M))).symm r)))

/-- The existing finite closed derivation is interpreted on the actual
selected attacked source, then physically restored to original-position labels. -/
theorem restored_interpreted {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) :
    (restoreChannel M θ (auxiliary M e)).toKraus.apply
      ((BB84DecisionRaw.decided (bases M θ) (auxiliary M e) S minKey tolerance).toKraus.apply
        (input A M).matrix) =
    (restoreChannel M θ (auxiliary M e)).toKraus.apply
      ((BB84DeferredRaw.reference (bases M θ) (auxiliary M e) S minKey tolerance).toKraus.apply
        (input A M).matrix) := by
  have h := interpreted A M θ S minKey tolerance
  change (BB84DecisionRaw.decided (bases M θ) (auxiliary M e) S minKey tolerance).toKraus.apply
      (input A M).matrix =
    (BB84DeferredRaw.reference (bases M θ) (auxiliary M e) S minKey tolerance).toKraus.apply
      (input A M).matrix at h
  exact congrArg (restoreChannel M θ (auxiliary M e)).toKraus.apply h

end
end Foundation.Quantum.QKD.BB84SiftedInput
