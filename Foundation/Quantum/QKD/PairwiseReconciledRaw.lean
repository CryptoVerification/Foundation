import Foundation.Quantum.QKD.RawReconciliation
import Foundation.Quantum.QKD.PairwiseReconciledPrivacy

/-! Exact equality of the real raw-key decoder/check and the same supported
BB84 coordinates. Equality keeps every conditional quantum entry. -/
namespace Foundation.Quantum.QKD.PairwiseReconciledVerification
noncomputable section
open Subnormalized PureProjection PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def checkedCoordinates {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  restrict (restrict (aliceState v hv k gap c)
    (fun p => BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode p.2)))
    (fun p => PairwiseExpandedVerification.verificationHash M c s p.1 =
      PairwiseExpandedVerification.verificationHash M c s (correctedBob c p.1 (bobCoordinate c p.1 p.2)))

theorem verifiedAlice_coordinates {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    verifiedAlice M v hv k gap minKey tolerance c s =
      withPublic (checkedCoordinates M v hv k gap minKey tolerance c s) := by
  unfold verifiedAlice CommonKey.aliceView KeyVerification.selected reconciledInput PairwisePhaseCoordinates.verificationInput
  rw [restrict_relabel, restrict_relabel, relabel_comp, relabel_comp]
  simp only [Function.comp_def, Prod.mk.eta]
  change withPublic (relabel _ id) = _
  rw [relabel_id]
  rfl

def selectedRaw {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  restrict (restrict (ofCQ (rawState v hv k gap minKey tolerance c))
    (fun o => o.transcript.accepted = true))
    (fun o => Hashing.rawHash s (BB84SiftedInput.expand M o.aliceKey) =
      Hashing.rawHash s (BB84SiftedInput.expand M (RawReconciliation.bobKey c.2 o)))

theorem selectedRaw_coordinates {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    selectedRaw M v hv k gap minKey tolerance c s =
      relabel (checkedCoordinates M v hv k gap minKey tolerance c s) (coordinateRaw c minKey tolerance) := by
  unfold selectedRaw
  rw [rawState_coordinates, restrict_relabel, restrict_relabel]
  congr 1
  apply State.ext
  funext ⟨x,r⟩
  by_cases hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)
  · have ha : (coordinateRaw c minKey tolerance (x,r)).transcript.accepted = true := by
      simp only [coordinateRaw, decoded_acceptance, hr, decide_true]
    simp only [checkedCoordinates, restrict, ha, hr, ite_true]
    have hh : (PairwiseExpandedVerification.verificationHash M c s x =
        PairwiseExpandedVerification.verificationHash M c s (correctedBob c x (bobCoordinate c x r))) ↔
        Hashing.rawHash s (BB84SiftedInput.expand M (coordinateRaw c minKey tolerance (x,r)).aliceKey) =
          Hashing.rawHash s (BB84SiftedInput.expand M (RawReconciliation.bobKey c.2 (coordinateRaw c minKey tolerance (x,r)))) := by
      simpa only [RawReconciliation.output] using RawReconciliation.coordinate_verification M c minKey tolerance x r s hr
    simp only [← hh]
  · have ha : (coordinateRaw c minKey tolerance (x,r)).transcript.accepted ≠ true := by
      simpa only [coordinateRaw, decoded_acceptance, hr, decide_false] using (show false ≠ true by decide)
    simp [checkedCoordinates, restrict, ha, hr]

def checkedRaw {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  relabel (selectedRaw M v hv k gap minKey tolerance c s) (RawReconciliation.output c.2)

theorem checkedRaw_coordinates {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    checkedRaw M v hv k gap minKey tolerance c s =
      relabel (checkedCoordinates M v hv k gap minKey tolerance c s)
        (fun p => RawReconciliation.output c.2 (coordinateRaw c minKey tolerance p)) := by
  unfold checkedRaw
  rw [selectedRaw_coordinates, relabel_comp]
  rfl

end
end Foundation.Quantum.QKD.PairwiseReconciledVerification
