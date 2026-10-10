import Foundation.Quantum.QKD.PairwiseExpandedVerificationPrivacy

/-! Equality with the actual raw-output check on the same approximant, not
merely equality of outcome probabilities. The auxiliary matrices remain whole. -/
namespace Foundation.Quantum.QKD.PairwiseExpandedVerification
noncomputable section
open Subnormalized PureProjection PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false

def checkedCoordinates {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :=
  restrict (restrict (aliceState v hv k gap c)
    (fun p => BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode p.2)))
    (fun p => verificationHash M c s p.1 = verificationHash M c s (bobCoordinate c p.1 p.2))

theorem verifiedAlice_coordinates {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :
    verifiedAlice M v hv k gap minKey tolerance c s =
      withPublic (checkedCoordinates M v hv k gap minKey tolerance c s) := by
  unfold verifiedAlice CommonKey.aliceView KeyVerification.selected verificationInput
  rw [restrict_relabel, relabel_comp]
  simp only [Function.comp_def, Prod.mk.eta]
  change withPublic (relabel _ id) = _
  rw [relabel_id]
  rfl

def checkedRaw {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :=
  restrict (restrict (ofCQ (rawState v hv k gap minKey tolerance c))
    (fun o => o.transcript.accepted = true))
    (fun o => Hashing.rawHash s (BB84SiftedInput.expand M o.aliceKey) = Hashing.rawHash s (BB84SiftedInput.expand M o.bobKey))

/-- The actual decoder, the original acceptance test and the new public
verification select exactly the state used by the derived support bound. -/
theorem checkedRaw_coordinates {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :
    checkedRaw M v hv k gap minKey tolerance c s =
      relabel (checkedCoordinates M v hv k gap minKey tolerance c s)
        (coordinateRaw c minKey tolerance) := by
  unfold checkedRaw
  rw [rawState_coordinates, restrict_relabel, restrict_relabel]
  congr 1
  apply State.ext
  funext ⟨x,r⟩
  by_cases hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)
  · have ha : (coordinateRaw c minKey tolerance (x,r)).transcript.accepted = true := by
      simp only [coordinateRaw, decoded_acceptance, hr, decide_true]
    simp only [checkedCoordinates, restrict, ha, hr, ite_true]
    simp only [← coordinate_verification M c minKey tolerance x r s hr]
  · have ha : (coordinateRaw c minKey tolerance (x,r)).transcript.accepted ≠ true := by
      simpa only [coordinateRaw, decoded_acceptance, hr, decide_false] using
        (show false ≠ true by decide)
    simp [checkedCoordinates, restrict, ha, hr]

end
end Foundation.Quantum.QKD.PairwiseExpandedVerification
