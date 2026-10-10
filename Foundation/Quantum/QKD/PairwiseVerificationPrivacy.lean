import Foundation.Quantum.QKD.PairwiseVerificationCoordinates
import Foundation.Quantum.PublicMixtureObservation

/-! Proved BB84 support domination after the actual two-key check, public
test-bit removal and tag disclosure. No new entropy/secrecy premise is used.
The real-to-support sampling error and full-output restoration are separate. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized PureProjection
set_option backward.isDefEq.respectTransparency false

def verifiedSource {n tag : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n)
    (s : Hashing.RawSeed n tag) :=
  relabel (verifiedAlice v hv k gap minKey tolerance c s) (testEquiv c.2)

theorem verified_test_dominated {n tag : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n)
    (s : Hashing.RawSeed n tag) :
    Dominated (withPublic (verifiedSource v hv k gap minKey tolerance c s))
      (leakedReference (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis)
        (reference v hv k gap c)) ((2:ℝ)^c.2.card * bound k gap minKey tolerance c) := by
  have h := split_dominated (verifiedAlice v hv k gap minKey tolerance c s)
    (testEquiv c.2) (reference v hv k gap c) (bound k gap minKey tolerance c)
    (verifiedAlice_dominated v hv k gap minKey tolerance c s)
  simpa only [tested_alphabet, Nat.cast_pow, Nat.cast_ofNat, verifiedSource] using h

def verifiedTagKey {n tag : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n)
    (s : Hashing.RawSeed n tag) :=
  withPublic (withPublic (disclose (verifiedSource v hv k gap minKey tolerance c s)
    (fun x _ => remainingHash c.2 s x)))

theorem verified_tag_dominated {n tag : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n)
    (s : Hashing.RawSeed n tag) :
    Dominated (verifiedTagKey v hv k gap minKey tolerance c s)
      (leakedReference (C := IdealKey.Key tag)
        (leakedReference (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis)
          (reference v hv k gap c)))
      (Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c)) :=
  disclose_dominated _ _ _ _ (verified_test_dominated v hv k gap minKey tolerance c s)

theorem verified_hash_privacy {n tag length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n)
    (s : Hashing.RawSeed n tag) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun r => Collision.hashed (verifiedTagKey v hv k gap minKey tolerance c s).block
          (remainingHash c.2 r)))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun _ => Collision.uniformComparator (Y := IdealKey.Key length)
          (verifiedTagKey v hv k gap minKey tolerance c s).block))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))) := by
  apply PrivacyAmplificationLogic.sound _ (remainingHash c.2)
    (fun _ => verifiedTagKey v hv k gap minKey tolerance c s)
    (fun _ => leakedReference (C := IdealKey.Key tag)
      (leakedReference (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis)
        (reference v hv k gap c))) (remaining_collision c.2)
    (PrivacyAmplificationLogic.proof (Fintype.card (IdealKey.Key length)) 0 0
      (Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c)) 1 _
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) (bound_nonneg _ _ _ _ _))) le_rfl)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact verified_tag_dominated v hv k gap minKey tolerance c s
  · have hi1 : i = 1 := by omega
    subst i
    exact (verifiedTagKey v hv k gap minKey tolerance c s).bounded

/-- Both independent hash seeds are public. Only test values and the
verification tag occur in the entropy coefficient, not seed cardinalities. -/
theorem verified_hash_average {n tag length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n tag)) (fun s =>
        publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
          (fun r => Collision.hashed (verifiedTagKey v hv k gap minKey tolerance c s).block
            (remainingHash c.2 r))))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n tag)) (fun s =>
        publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
          (fun _ => Collision.uniformComparator (Y := IdealKey.Key length)
            (verifiedTagKey v hv k gap minKey tolerance c s).block)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))) := by
  have h := publicMixture_approx (Foundation.Probability.uniform (Hashing.RawSeed n tag)) _ _
    (fun _ => (1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
      ((1-1/Fintype.card (IdealKey.Key length))*
        ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1))))
    (fun s => verified_hash_privacy v hv k gap minKey tolerance c s)
  simpa only [← Finset.sum_mul, Density.probability_weights, one_mul] using h

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
