import Foundation.Quantum.QKD.PairwiseReconciledRaw
import Foundation.Quantum.QKD.PairwiseReconciledPublished
import Foundation.Quantum.QKD.PairwiseVerificationPublicRaw

/-! Identify the proved privacy output with directly decoding, checking,
and hashing the original raw CQ state. Same public messages and both full
position seeds, same quantum entries; no outcome-only identification. -/
namespace Foundation.Quantum.QKD.PairwiseReconciledVerification
noncomputable section
open Subnormalized PureProjection PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

theorem published_coordinates {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    published (length := length) M v hv k gap minKey tolerance c s =
      relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (checkedCoordinates M v hv k gap minKey tolerance c s))
        (fun rx => (expandedHash M c.2 rx.1 (testEquiv c.2 rx.2.1).1,
          ((((ArbitraryReconciliation.quantumMessage (testEquiv c.2 rx.2.1).1,
            expandedHash M c.2 s (testEquiv c.2 rx.2.1).1),rx.1),(testEquiv c.2 rx.2.1).2),rx.2.2))) := by
  unfold published
  rw [show PublicRegisterExpose.expose (HashLayout.output
      (withPublic (verifiedDisclosure M v hv k gap minKey tolerance c s))
      (Foundation.Probability.uniform (Hashing.RawSeed n length)) (expandedHash M c.2)) =
    relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
      (verifiedDisclosure M v hv k gap minKey tolerance c s))
      (fun rx => (expandedHash M c.2 rx.1 rx.2.1.1,((rx.2.1.2,rx.1),rx.2.2))) from
    PublicRegisterExpose.expose_seed_relabel _ _ _]
  unfold verifiedDisclosure disclose verifiedSource
  rw [verifiedAlice_coordinates, seed_relabel, seed_relabel, relabel_comp, relabel_comp]
  exact PublicRegisterExpose.expose_seed_relabel _ _ _

def publicRawHash {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  CommonKey.publicProcess (published (length := length) M v hv k gap minKey tolerance c s)
    (fun p => ((((testTranscript c p.1.2 p.2,ArbitraryReconciliation.messageRecord (RawReconciliation.public_fits M c.2) p.1.1.1.1),s),p.1.1.1.2),p.1.1.2))

def rawHash {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (checkedRaw M v hv k gap minKey tolerance c s))
    (fun ro => (Hashing.rawHash ro.1 (BB84SiftedInput.expand M ro.2.aliceKey),
      ((((ro.2.transcript,RawReconciliation.publicMessage M c.2 ro.2),s),
        Hashing.rawHash s (BB84SiftedInput.expand M ro.2.aliceKey)),ro.1)))

theorem rawHash_eq {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    rawHash (length := length) M v hv k gap minKey tolerance c s =
      publicRawHash (length := length) M v hv k gap minKey tolerance c s := by
  unfold rawHash publicRawHash CommonKey.publicProcess
  rw [checkedRaw_coordinates, published_coordinates, seed_relabel, relabel_comp, relabel_comp]
  unfold checkedCoordinates
  rw [restrict_intersection, seed_restrict]
  apply relabel_restrict_congr
  intro rx hx
  rcases rx with ⟨rPA,x,r⟩
  have hr := hx.1
  simp only [Function.comp_def, RawReconciliation.output, RawReconciliation.publicMessage, RawReconciliation.message]
  rw [coordinate_alice_key c minKey tolerance x r hr, RawReconciliation.remaining_optional,
    coordinate_public_record c minKey tolerance x r hr]
  rfl

theorem raw_secrecy {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    OperatorApprox (joint (rawHash (length := length) M v hv k gap minKey tolerance c s))
      (joint (CommonKey.uniformize (rawHash (length := length) M v hv k gap minKey tolerance c s)))
      (privacyError tag length k gap minKey tolerance c) := by
  rw [rawHash_eq]
  exact CommonKey.publicProcess_secrecy _ _ _ (published_secrecy M v hv k gap minKey tolerance c s)

def rawAverage {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  mixture (Foundation.Probability.uniform (Hashing.RawSeed n tag))
    (fun s => rawHash (length := length) M v hv k gap minKey tolerance c s)

theorem raw_average_secrecy {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (rawAverage (tag := tag) (length := length) M v hv k gap minKey tolerance c))
      (joint (CommonKey.uniformize (rawAverage (tag := tag) (length := length) M v hv k gap minKey tolerance c)))
      (privacyError tag length k gap minKey tolerance c) := by
  have h := CommonKey.mixture_secrecy (Foundation.Probability.uniform (Hashing.RawSeed n tag))
    (fun s => rawHash (length := length) M v hv k gap minKey tolerance c s)
    (fun _ => privacyError tag length k gap minKey tolerance c)
    (fun s => raw_secrecy M v hv k gap minKey tolerance c s)
  simpa only [rawAverage, ← Finset.sum_mul, Density.probability_weights, one_mul] using h

end
end Foundation.Quantum.QKD.PairwiseReconciledVerification
