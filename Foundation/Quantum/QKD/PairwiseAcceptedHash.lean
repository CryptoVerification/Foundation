import Foundation.Quantum.QKD.PairwisePublicSecrecy
import Foundation.Quantum.QKD.PublicRegisterHash
import Foundation.Quantum.QKD.RelabelRestricted

/-! Identify the privacy-certified published state with the accepted hash of
the same original raw-record reconstruction, not just an isomorphic key type. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized PairwiseRecordedSampling
set_option backward.isDefEq.respectTransparency false

theorem published_source {n length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) :
    publishedRawHash (length := length) v hv k gap minKey tolerance c =
      relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (restrict (aliceState v hv k gap c)
          (fun p => BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode p.2))))
        (fun sx => (Hashing.rawHash sx.1 (optionalKey c.2 (testEquiv c.2 sx.2.1).1),
          (testTranscript c (testEquiv c.2 sx.2.1).2 sx.2.2,sx.1))) := by
  unfold publishedRawHash publishedHash testedSource acceptedAlice
  rw [PublicRegisterExpose.split_hash_expose, CommonKey.publicProcess, relabel_comp]
  rfl

def acceptedRawHash {n length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (restrict (ofCQ (rawState v hv k gap minKey tolerance c))
      (fun o => o.transcript.accepted = true)))
    (fun so => (Hashing.rawHash so.1 so.2.aliceKey,(so.2.transcript,so.1)))

theorem acceptedRawHash_eq {n length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) :
    acceptedRawHash (length := length) v hv k gap minKey tolerance c =
      publishedRawHash (length := length) v hv k gap minKey tolerance c := by
  unfold acceptedRawHash
  rw [rawState, ofCQ_relabel, ofCQ_relabel, relabel_comp, restrict_relabel, seed_relabel, relabel_comp]
  have hp : (fun x : (qubits n).Basis × (qubits n).Basis =>
      (decodeRawLabel (basis c) c.2 minKey tolerance (labelEquiv n x)).transcript.accepted = true) =
      (fun x => BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode x.2)) := by
    funext x
    apply propext
    simp only [labelEquiv, Equiv.coe_fn_mk, decoded_acceptance, decide_eq_true_eq]
  simp only [Function.comp_apply]
  simp only [hp]
  rw [published_source]
  unfold aliceState
  rw [restrict_relabel, seed_relabel, relabel_comp]
  change relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (restrict (ofCQ (jointState v hv k gap c))
      (fun x => BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode x.2)))) _ =
    relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
      (restrict (ofCQ (jointState v hv k gap c))
        (fun x => BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode x.2)))) _
  rw [seed_restrict]
  apply relabel_restrict_congr
  intro ⟨s,⟨z,r⟩⟩ hr
  simp only [Function.comp_apply, labelEquiv, alicePairEquiv, Equiv.coe_fn_mk]
  rw [decoded_alice_key (basis c) c.2 minKey tolerance r z hr,
    decoded_transcript c minKey tolerance r z hr]

theorem accepted_raw_secrecy {n length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) :
    OperatorApprox (joint (acceptedRawHash (length := length) v hv k gap minKey tolerance c))
      (joint (CommonKey.uniformize (acceptedRawHash (length := length) v hv k gap minKey tolerance c)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) * ((1-1/Fintype.card (IdealKey.Key length))*
        (((2:ℝ)^c.2.card * bound k gap minKey tolerance c)*1)))) := by
  rw [acceptedRawHash_eq]
  exact public_raw_secrecy v hv k gap minKey tolerance c

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
