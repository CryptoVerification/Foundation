import Foundation.Quantum.QKD.PairwiseVerificationPublicRaw
import Foundation.Quantum.QKD.PairwiseExpandedVerificationPublic
import Foundation.Quantum.QKD.SubnormalizedIntersection
import Foundation.Quantum.QKD.PublicKeyProcess
import Foundation.Quantum.QKD.CommonKeyMixture

/-! The explicit public labels reconstruct the original raw transcript and
retain both public seeds and Alice's tag. Exact equality with directly hashing
the same checked raw state keeps the full quantum auxiliary system. -/
namespace Foundation.Quantum.QKD.PairwiseExpandedVerification
noncomputable section
open Subnormalized PureProjection PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def verifiedPublicRawHash {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  CommonKey.publicProcess (verifiedPublished (length := length) M v hv k gap minKey tolerance c s)
    (fun p => (((testTranscript c p.1.2 p.2,s),p.1.1.1),p.1.1.2))

def verifiedRawHash {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (checkedRaw M v hv k gap minKey tolerance c s))
    (fun ro => (Hashing.rawHash ro.1 (BB84SiftedInput.expand M ro.2.aliceKey),
      (((ro.2.transcript,s),Hashing.rawHash s (BB84SiftedInput.expand M ro.2.aliceKey)),ro.1)))

/-- Same checked keys, actual original transcript, both public seeds and tag. -/
theorem verifiedRawHash_eq {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    verifiedRawHash (length := length) M v hv k gap minKey tolerance c s =
      verifiedPublicRawHash (length := length) M v hv k gap minKey tolerance c s := by
  unfold verifiedRawHash verifiedPublicRawHash CommonKey.publicProcess
  rw [checkedRaw_coordinates, verifiedPublished_eq, seed_relabel, relabel_comp, relabel_comp]
  unfold checkedCoordinates
  rw [restrict_intersection, seed_restrict]
  apply relabel_restrict_congr
  intro rx hx
  rcases rx with ⟨rPA,x,r⟩
  have hr := hx.1
  simp only [Function.comp_def]
  rw [coordinate_alice_key c minKey tolerance x r hr, coordinate_public_record c minKey tolerance x r hr]
  rfl

theorem verified_raw_secrecy {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    OperatorApprox (joint (verifiedRawHash (length := length) M v hv k gap minKey tolerance c s))
      (joint (CommonKey.uniformize (verifiedRawHash (length := length) M v hv k gap minKey tolerance c s)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))) := by
  rw [verifiedRawHash_eq]
  exact CommonKey.publicProcess_secrecy _ _ _ (verified_published_secrecy M v hv k gap minKey tolerance c s)

def verifiedRawAverage {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  mixture (Foundation.Probability.uniform (Hashing.RawSeed n tag))
    (fun s => verifiedRawHash (length := length) M v hv k gap minKey tolerance c s)

/-- The verification seed stays in the actual public transcript while its
independent distribution is averaged. The ideal uses the same averaged marginal. -/
theorem verified_raw_average_secrecy {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (verifiedRawAverage (tag := tag) (length := length) M v hv k gap minKey tolerance c))
      (joint (CommonKey.uniformize (verifiedRawAverage (tag := tag) (length := length) M v hv k gap minKey tolerance c)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))) := by
  have h := CommonKey.mixture_secrecy (Foundation.Probability.uniform (Hashing.RawSeed n tag))
    (fun s => verifiedRawHash (length := length) M v hv k gap minKey tolerance c s)
    (fun _ => (1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
      ((1-1/Fintype.card (IdealKey.Key length))*
        ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1))))
    (fun s => verified_raw_secrecy M v hv k gap minKey tolerance c s)
  simpa only [verifiedRawAverage, ← Finset.sum_mul, Density.probability_weights, one_mul] using h

end
end Foundation.Quantum.QKD.PairwiseExpandedVerification
