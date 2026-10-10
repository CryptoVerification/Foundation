import Foundation.Quantum.QKD.PairwiseVerificationPrivacy
import Foundation.Quantum.QKD.PairwiseExpandedHash

/-! Both verifier and PA seeds are drawn on the original, unsifted positions.
Selection uses the two actual restored keys; no equality between the full
and reduced seed distributions is assumed. -/
namespace Foundation.Quantum.QKD.PairwiseExpandedVerification
noncomputable section
open Subnormalized PureProjection PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def verificationHash {n tag : Nat} (M : Finset (Fin n))
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) (x : (qubits (BB84SiftedInput.selectedCount M)).Basis) : IdealKey.Key tag :=
  expandedHash M c.2 s (testEquiv c.2 x).1

/-- The verifier evaluates exactly the expanded Alice and Bob keys. -/
theorem coordinate_verification {n tag : Nat} (M : Finset (Fin n))
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (minKey tolerance : Nat) (x r : (qubits (BB84SiftedInput.selectedCount M)).Basis)
    (s : Hashing.RawSeed n tag)
    (hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)) :
    (verificationHash M c s x = verificationHash M c s (bobCoordinate c x r)) ↔
      Hashing.rawHash s (BB84SiftedInput.expand M (coordinateRaw c minKey tolerance (x,r)).aliceKey) =
        Hashing.rawHash s (BB84SiftedInput.expand M (coordinateRaw c minKey tolerance (x,r)).bobKey) := by
  rw [coordinate_alice_key c minKey tolerance x r hr, coordinate_bob_key c minKey tolerance x r hr]
  rfl

def verifiedAlice {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :=
  withPublic (CommonKey.aliceView (KeyVerification.selected
    (verificationInput v hv k gap minKey tolerance c) (verificationHash M c) s))

theorem verifiedAlice_dominated {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M))
    (s : Hashing.RawSeed n tag) :
    Dominated (verifiedAlice M v hv k gap minKey tolerance c s)
      (reference v hv k gap c) (bound k gap minKey tolerance c) := by
  apply KeyVerification.selected_alice_dominated
  rw [verificationInput_alice]
  exact acceptedAlice_dominated v hv k gap minKey tolerance c


end
end Foundation.Quantum.QKD.PairwiseExpandedVerification
