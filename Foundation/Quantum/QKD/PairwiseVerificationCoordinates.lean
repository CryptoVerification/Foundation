import Foundation.Quantum.QKD.KeyVerificationPrivacy
import Foundation.Quantum.QKD.PairwisePublicTranscript
import Foundation.Quantum.QKD.RelabelRestricted

/-! The verification input is constructed from the same supported BB84
measurement state. Alice and Bob are actual decoded measurement outcomes,
not independent keys or a newly assumed entropy certificate. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized PureProjection
set_option backward.isDefEq.respectTransparency false

def coordinateRaw {n : Nat} (c : PairwiseSampling.Configuration n) (minKey tolerance : Nat)
    (p : (qubits n).Basis × (qubits n).Basis) : RawProtocol.Output n :=
  decodeRawLabel (PairwiseRecordedSampling.basis c) c.2 minKey tolerance
    (errorCode p.2,errorCode (alice n (PairwiseRecordedSampling.basis c) p.2 p.1))

def bobCoordinate {n : Nat} (c : PairwiseSampling.Configuration n)
    (x r : (qubits n).Basis) : (qubits n).Basis :=
  (BB84OutcomeCoordinates.originalOutcomes (PairwiseRecordedSampling.basis c)
    (errorCode r,errorCode (alice n (PairwiseRecordedSampling.basis c) r x))).1

/-- The old raw measurement state equals the same Alice/error coordinates
processed by the original raw decoder. Full quantum blocks are preserved. -/
theorem rawState_coordinates {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :
    ofCQ (rawState v hv k gap minKey tolerance c) =
      relabel (aliceState v hv k gap c) (coordinateRaw c minKey tolerance) := by
  simp only [rawState, ofCQ_relabel, aliceState, relabel_comp]
  congr 1
  funext p
  simp only [Function.comp_def, coordinateRaw, alicePairEquiv, Equiv.coe_fn_mk, alice_involution, labelEquiv]

theorem coordinate_alice_key {n : Nat} (c : PairwiseSampling.Configuration n)
    (minKey tolerance : Nat) (x r : (qubits n).Basis)
    (hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)) :
    (coordinateRaw c minKey tolerance (x,r)).aliceKey = optionalKey c.2 (testEquiv c.2 x).1 := by
  simpa only [coordinateRaw, alice_involution] using
    decoded_alice_key (PairwiseRecordedSampling.basis c) c.2 minKey tolerance r
      (alice n (PairwiseRecordedSampling.basis c) r x) hr

theorem coordinate_bob_key {n : Nat} (c : PairwiseSampling.Configuration n)
    (minKey tolerance : Nat) (x r : (qubits n).Basis)
    (hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)) :
    (coordinateRaw c minKey tolerance (x,r)).bobKey =
      optionalKey c.2 (testEquiv c.2 (bobCoordinate c x r)).1 := by
  have ha := decoded_acceptance (PairwiseRecordedSampling.basis c) c.2 minKey tolerance
    (errorCode r) (errorCode (alice n (PairwiseRecordedSampling.basis c) r x))
  have hac : RawProtocol.accepts (PairwiseRecordedSampling.basis c) (PairwiseRecordedSampling.basis c)
      (readBits (BB84OutcomeCoordinates.originalOutcomes (PairwiseRecordedSampling.basis c)
        (errorCode r,errorCode (alice n (PairwiseRecordedSampling.basis c) r x))).2)
      (readBits (BB84OutcomeCoordinates.originalOutcomes (PairwiseRecordedSampling.basis c)
        (errorCode r,errorCode (alice n (PairwiseRecordedSampling.basis c) r x))).1)
      c.2 minKey tolerance = true := by
    simpa only [decodeRawLabel, BB84DeferredRaw.recoverLabel, BB84DeferredRaw.rawLabel,
      Equiv.symm_apply_apply, RawProtocol.output, hr, decide_true] using ha
  rw [optionalKey_split]
  funext i
  simp only [coordinateRaw, decodeRawLabel, BB84DeferredRaw.recoverLabel,
    BB84DeferredRaw.rawLabel, Equiv.symm_apply_apply, RawProtocol.output, hac]
  simp [RawProtocol.keyPositions, RawProtocol.matched, bobCoordinate]

def verificationInput {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :=
  relabel (restrict (aliceState v hv k gap c)
    (fun p => BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode p.2)))
    (fun p => ((p.1,bobCoordinate c p.1 p.2),p.2))

theorem verificationInput_alice {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :
    withPublic (CommonKey.aliceView (verificationInput v hv k gap minKey tolerance c)) =
      acceptedAlice v hv k gap minKey tolerance c := by
  unfold CommonKey.aliceView verificationInput
  rw [relabel_comp]
  simp only [Function.comp_def, Prod.mk.eta]
  change withPublic (relabel _ id) = _
  rw [relabel_id]
  rfl

def verificationHash {n tag : Nat} (c : PairwiseSampling.Configuration n)
    (s : Hashing.RawSeed n tag) (x : (qubits n).Basis) : IdealKey.Key tag :=
  remainingHash c.2 s (testEquiv c.2 x).1


/-- Both local tags use exactly the original decoded optional-position keys. -/
theorem coordinate_verification {n tag : Nat} (c : PairwiseSampling.Configuration n)
    (minKey tolerance : Nat) (x r : (qubits n).Basis) (s : Hashing.RawSeed n tag)
    (hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)) :
    (verificationHash c s x = verificationHash c s (bobCoordinate c x r)) ↔
      Hashing.rawHash s (coordinateRaw c minKey tolerance (x,r)).aliceKey =
        Hashing.rawHash s (coordinateRaw c minKey tolerance (x,r)).bobKey := by
  rw [coordinate_alice_key c minKey tolerance x r hr, coordinate_bob_key c minKey tolerance x r hr]
  rfl

/-- The original acceptance and the new real two-key check, before test
values and the new tag are exposed. -/
def verifiedAlice {n tag : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n)
    (s : Hashing.RawSeed n tag) :=
  withPublic (CommonKey.aliceView (KeyVerification.selected
    (verificationInput v hv k gap minKey tolerance c) (verificationHash c) s))

theorem verifiedAlice_dominated {n tag : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n)
    (s : Hashing.RawSeed n tag) :
    Dominated (verifiedAlice v hv k gap minKey tolerance c s)
      (reference v hv k gap c) (bound k gap minKey tolerance c) := by
  apply KeyVerification.selected_alice_dominated
  rw [verificationInput_alice]
  exact acceptedAlice_dominated v hv k gap minKey tolerance c

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
