import Foundation.Quantum.QKD.ArbitraryReconciliationCQ
import Foundation.Quantum.QKD.PairwiseExpandedVerificationPrivacy

/-! Apply the actual arbitrary-length decoder to the same BB84 remaining
measurement outcomes before verification. Bob gets Alice's parity/suffix
message, not Alice's private word. The message is charged in the next module. -/
namespace Foundation.Quantum.QKD.PairwiseReconciledVerification
noncomputable section
open Subnormalized PureProjection PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def correctedBob {m : Nat} (c : PairwiseSampling.Configuration m)
    (alice bob : (qubits m).Basis) : (qubits m).Basis :=
  (testEquiv c.2).symm (ArbitraryReconciliation.quantumDecode (testEquiv c.2 bob).1
    (ArbitraryReconciliation.quantumMessage (testEquiv c.2 alice).1), (testEquiv c.2 bob).2)

theorem correctedBob_remaining {m : Nat} (c : PairwiseSampling.Configuration m)
    (alice bob : (qubits m).Basis) :
    (testEquiv c.2 (correctedBob c alice bob)).1 =
      ArbitraryReconciliation.quantumDecode (testEquiv c.2 bob).1
        (ArbitraryReconciliation.quantumMessage (testEquiv c.2 alice).1) := by
  simp only [correctedBob, Equiv.apply_symm_apply]

theorem correctedBob_correct {m : Nat} (c : PairwiseSampling.Configuration m)
    (alice bob : (qubits m).Basis)
    (h : ∀ j, RepetitionReconciliation.errors
      (ArbitraryReconciliation.block (readBits (testEquiv c.2 alice).1) j)
      (ArbitraryReconciliation.block (readBits (testEquiv c.2 bob).1) j) ≤ 1) :
    (testEquiv c.2 (correctedBob c alice bob)).1 = (testEquiv c.2 alice).1 := by
  rw [correctedBob_remaining]
  exact ArbitraryReconciliation.quantum_correct _ _ h

def reconciledInput {m : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace m e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration m) :=
  relabel (PairwisePhaseCoordinates.verificationInput v hv k gap minKey tolerance c)
    (fun p => ((p.1.1,correctedBob c p.1.1 p.1.2),p.2))

/-- Exact equality on every quantum block, including correlations with the
actual Bob outcome and the public error register. -/
theorem reconciledInput_alice {m : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace m e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration m) :
    withPublic (CommonKey.aliceView (reconciledInput v hv k gap minKey tolerance c)) =
      acceptedAlice v hv k gap minKey tolerance c := by
  unfold reconciledInput CommonKey.aliceView
  rw [relabel_comp]
  exact verificationInput_alice v hv k gap minKey tolerance c

def verifiedAlice {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  withPublic (CommonKey.aliceView (KeyVerification.selected
    (reconciledInput v hv k gap minKey tolerance c) (PairwiseExpandedVerification.verificationHash M c) s))

theorem verifiedAlice_dominated {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    Dominated (verifiedAlice M v hv k gap minKey tolerance c s)
      (reference v hv k gap c) (bound k gap minKey tolerance c) := by
  apply KeyVerification.selected_alice_dominated
  rw [reconciledInput_alice]
  exact acceptedAlice_dominated v hv k gap minKey tolerance c

def verifiedSource {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :=
  relabel (verifiedAlice M v hv k gap minKey tolerance c s) (testEquiv c.2)

theorem verified_test_dominated {n tag : Nat} {e : Space} (M : Finset (Fin n))
    (v : (BB84DelayedMeasurements.jointSpace (BB84SiftedInput.selectedCount M) e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) (s : Hashing.RawSeed n tag) :
    Dominated (withPublic (verifiedSource M v hv k gap minKey tolerance c s))
      (leakedReference (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis) (reference v hv k gap c))
      ((2:ℝ)^c.2.card * bound k gap minKey tolerance c) := by
  have h := split_dominated (verifiedAlice M v hv k gap minKey tolerance c s)
    (testEquiv c.2) (reference v hv k gap c) (bound k gap minKey tolerance c)
    (verifiedAlice_dominated M v hv k gap minKey tolerance c s)
  simpa only [tested_alphabet, Nat.cast_pow, Nat.cast_ofNat, verifiedSource] using h

end
end Foundation.Quantum.QKD.PairwiseReconciledVerification
