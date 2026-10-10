import Foundation.Quantum.QKD.PairwisePublishedHash

/-! Reconstruct only the actual public raw transcript from public test values
and detailed errors. The function does not inspect the remaining private key. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84DelayedMeasurements BB84ErrorTransform PairwiseRecordedSampling
set_option backward.isDefEq.respectTransparency false

theorem original_signal {n : Nat} (θ : Fin n → BB84Basis) (r z : (qubits n).Basis) :
    BB84OutcomeCoordinates.originalOutcomes θ (errorCode r,errorCode z) = relabel n θ (split n θ (r,z)) := by
  rw [BB84OutcomeCoordinates.originalOutcomes, ← encode_split, BB84OutcomeCoordinates.decode_encode]

theorem original_error {n : Nat} (θ : Fin n → BB84Basis) (r z : (qubits n).Basis) (i : Fin n) :
    bitXor (readBits (BB84OutcomeCoordinates.originalOutcomes θ (errorCode r,errorCode z)).1 i)
      (readBits (BB84OutcomeCoordinates.originalOutcomes θ (errorCode r,errorCode z)).2 i) = readBits r i := by
  rw [original_signal]
  have he := errorBits_relabel n θ (relabel n θ (split n θ (r,z))).1 (relabel n θ (split n θ (r,z))).2
  rw [Prod.mk.eta, relabel_involution] at he
  have hb := (bits n θ (split n θ (r,z))).1
  rw [split_involution] at hb
  exact (congrFun he i).symm.trans (congrFun hb.symm i)

theorem original_bob {n : Nat} (θ : Fin n → BB84Basis) (r z : (qubits n).Basis) (i : Fin n) :
    readBits (BB84OutcomeCoordinates.originalOutcomes θ (errorCode r,errorCode z)).1 i =
      bitXor (readBits (alice n θ r z) i) (readBits r i) := by
  rw [← original_alice, ← original_error θ r z i]
  rw [bitXor_comm (readBits (BB84OutcomeCoordinates.originalOutcomes θ (errorCode r,errorCode z)).2 i),
    bitXor_cancel]

def testTranscript {n : Nat} (c : PairwiseSampling.Configuration n)
    (t : (qubits (BB84SiftedInput.selectedCount c.2)).Basis) (r : (qubits n).Basis) : RawProtocol.PublicRecord n where
  aliceBases := basis c
  bobBases := basis c
  tested := c.2
  aliceTest := fun i => if h : i ∈ c.2 then
    some (readBits t ((BB84SiftedInput.selectedIndex c.2).symm ⟨i,h⟩)) else none
  bobTest := fun i => if h : i ∈ c.2 then
    some (bitXor (readBits t ((BB84SiftedInput.selectedIndex c.2).symm ⟨i,h⟩)) (readBits r i)) else none
  accepted := true

theorem decoded_transcript {n : Nat} (c : PairwiseSampling.Configuration n)
    (minKey tolerance : Nat) (r z : (qubits n).Basis)
    (hr : BB84DelayedDecision.accepts c.2 minKey tolerance (errorCode r)) :
    (decodeRawLabel (basis c) c.2 minKey tolerance (errorCode r,errorCode z)).transcript =
      testTranscript c (testEquiv c.2 (alice n (basis c) r z)).2 r := by
  have ha := decoded_acceptance (basis c) c.2 minKey tolerance (errorCode r) (errorCode z)
  simp only [decodeRawLabel, BB84DeferredRaw.recoverLabel, BB84DeferredRaw.rawLabel,
    Equiv.symm_apply_apply, RawProtocol.output, hr, decide_true] at ha
  simp only [decodeRawLabel, BB84DeferredRaw.recoverLabel, BB84DeferredRaw.rawLabel,
    Equiv.symm_apply_apply, RawProtocol.output, testTranscript]
  congr 1
  · funext i
    by_cases hi : i ∈ c.2 <;> simp only [hi, ite_true, ite_false, dite_true, dite_false]
    rw [original_alice, test_bits]
    simp only [Equiv.apply_symm_apply]
  · funext i
    by_cases hi : i ∈ c.2 <;> simp only [hi, ite_true, ite_false, dite_true, dite_false]
    rw [original_bob, test_bits]
    simp only [Equiv.apply_symm_apply]

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
