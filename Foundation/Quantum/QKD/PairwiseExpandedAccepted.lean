import Foundation.Quantum.QKD.PairwiseExpandedPublished
import Foundation.Quantum.QKD.PublicRegisterHash
import Foundation.Quantum.QKD.RelabelRestricted

/-! Identify full-position hashing and restored public records with the
actual selected raw record, using the original full-position seed distribution. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized PairwiseRecordedSampling
set_option backward.isDefEq.respectTransparency false

theorem expanded_published_source {n length : Nat} {e : Space} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    expandedPublishedRawHash (length := length) M θ v hv k gap minKey tolerance c =
      relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (restrict (aliceState v hv k gap c)
          (fun p => BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode p.2))))
        (fun sx => (Hashing.rawHash sx.1 (BB84SiftedInput.expand M (optionalKey c.2 (testEquiv c.2 sx.2.1).1)),
          (restoreTranscript M θ (testTranscript c (testEquiv c.2 sx.2.1).2 sx.2.2),sx.1))) := by
  unfold expandedPublishedRawHash expandedPublishedHash testedSource acceptedAlice
  rw [PublicRegisterExpose.split_hash_expose, CommonKey.publicProcess, relabel_comp]
  rfl

def expandedAcceptedHash {n length : Nat} {e : Space} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (restrict (ofCQ (rawState v hv k gap minKey tolerance c))
      (fun o => o.transcript.accepted = true)))
    (fun so => (Hashing.rawHash so.1 (BB84SiftedInput.expand M so.2.aliceKey),(restoreTranscript M θ so.2.transcript,so.1)))

theorem expandedAcceptedHash_eq {n length : Nat} {e : Space} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    expandedAcceptedHash (length := length) M θ v hv k gap minKey tolerance c =
      expandedPublishedRawHash (length := length) M θ v hv k gap minKey tolerance c := by
  unfold expandedAcceptedHash
  rw [rawState, ofCQ_relabel, ofCQ_relabel, relabel_comp, restrict_relabel, seed_relabel, relabel_comp]
  have hp : (fun x : (qubits (BB84SiftedInput.selectedCount M)).Basis × (qubits (BB84SiftedInput.selectedCount M)).Basis =>
      (decodeRawLabel (basis c) c.2 minKey tolerance (labelEquiv (BB84SiftedInput.selectedCount M) x)).transcript.accepted = true) =
      (fun x => BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode x.2)) := by
    funext x
    apply propext
    simp only [labelEquiv, Equiv.coe_fn_mk, decoded_acceptance, decide_eq_true_eq]
  simp only [Function.comp_apply]
  simp only [hp]
  rw [expanded_published_source]
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

theorem expanded_accepted_raw_secrecy {n length : Nat} {e : Space} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (expandedAcceptedHash (length := length) M θ v hv k gap minKey tolerance c))
      (joint (CommonKey.uniformize (expandedAcceptedHash (length := length) M θ v hv k gap minKey tolerance c)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) * ((1-1/Fintype.card (IdealKey.Key length))*
        (((2:ℝ)^c.2.card * bound k gap minKey tolerance c)*1)))) := by
  rw [expandedAcceptedHash_eq]
  exact expanded_public_raw_secrecy M θ v hv k gap minKey tolerance c

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
