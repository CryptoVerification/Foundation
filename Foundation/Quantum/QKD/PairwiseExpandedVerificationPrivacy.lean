import Foundation.Quantum.QKD.PairwiseExpandedVerification
import Foundation.Quantum.PublicMixtureObservation

/-! Supported BB84 verification and PA with both full-position seed families.
The existing Presentation/Model PA derivation discharges the bound; there is
no extra entropy assumption and the public seed cardinalities are not charged. -/
namespace Foundation.Quantum.QKD.PairwiseExpandedVerification
noncomputable section
open Subnormalized PureProjection PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def verifiedSource {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :=
  relabel (verifiedAlice M v hv k gap minKey tolerance c s) (testEquiv c.2)

theorem verified_test_dominated {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :
    Dominated (withPublic (verifiedSource M v hv k gap minKey tolerance c s))
      (leakedReference (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis)
        (reference v hv k gap c)) ((2:ℝ)^c.2.card * bound k gap minKey tolerance c) := by
  have h := split_dominated (verifiedAlice M v hv k gap minKey tolerance c s)
    (testEquiv c.2) (reference v hv k gap c) (bound k gap minKey tolerance c)
    (verifiedAlice_dominated M v hv k gap minKey tolerance c s)
  simpa only [tested_alphabet, Nat.cast_pow, Nat.cast_ofNat, verifiedSource] using h

def verifiedTagKey {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :=
  withPublic (withPublic (disclose (verifiedSource M v hv k gap minKey tolerance c s)
    (fun x _ => expandedHash M c.2 s x)))

theorem verified_tag_dominated {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :
    Dominated (verifiedTagKey M v hv k gap minKey tolerance c s)
      (leakedReference (C := IdealKey.Key tag)
        (leakedReference (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis)
          (reference v hv k gap c)))
      (Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c)) :=
  disclose_dominated _ _ _ _ (verified_test_dominated M v hv k gap minKey tolerance c s)

theorem verified_hash_privacy {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun r => Collision.hashed (verifiedTagKey M v hv k gap minKey tolerance c s).block
          (expandedHash M c.2 r)))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun _ => Collision.uniformComparator (Y := IdealKey.Key length)
          (verifiedTagKey M v hv k gap minKey tolerance c s).block))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))) := by
  apply PrivacyAmplificationLogic.sound _ (expandedHash M c.2)
    (fun _ => verifiedTagKey M v hv k gap minKey tolerance c s)
    (fun _ => leakedReference (C := IdealKey.Key tag)
      (leakedReference (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis)
        (reference v hv k gap c))) (expanded_collision M c.2)
    (PrivacyAmplificationLogic.proof (Fintype.card (IdealKey.Key length)) 0 0
      (Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c)) 1 _
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) (bound_nonneg _ _ _ _ _))) le_rfl)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact verified_tag_dominated M v hv k gap minKey tolerance c s
  · have hi1 : i = 1 := by omega
    subst i
    exact (verifiedTagKey M v hv k gap minKey tolerance c s).bounded

/-- Both independent hash seeds are public. Only test values and the
verification tag occur in the entropy coefficient, not seed cardinalities. -/
theorem verified_hash_average {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n tag)) (fun s =>
        publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
          (fun r => Collision.hashed (verifiedTagKey M v hv k gap minKey tolerance c s).block
            (expandedHash M c.2 r))))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n tag)) (fun s =>
        publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
          (fun _ => Collision.uniformComparator (Y := IdealKey.Key length)
            (verifiedTagKey M v hv k gap minKey tolerance c s).block)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))) := by
  have h := publicMixture_approx (Foundation.Probability.uniform (Hashing.RawSeed n tag)) _ _
    (fun _ => (1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
      ((1-1/Fintype.card (IdealKey.Key length))*
        ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1))))
    (fun s => verified_hash_privacy M v hv k gap minKey tolerance c s)
  simpa only [← Finset.sum_mul, Density.probability_weights, one_mul] using h


end
end Foundation.Quantum.QKD.PairwiseExpandedVerification
