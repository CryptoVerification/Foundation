import Foundation.Quantum.QKD.PairwisePhaseLabels

/-! Reconstruct the original raw record from exactly the measured state used
by the phase certificate. The operator equals the implemented error-first,
key-later, signal-discarding raw experiment on this same approximant. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference PairwiseRecordedSampling PureProjection
set_option backward.isDefEq.respectTransparency false

def decodeRawLabel {n : Nat} (θ : Fin n → BB84Basis) (T : Finset (Fin n))
    (minKey tolerance : Nat) (p : Fin (count n) × Fin (count n)) : RawProtocol.Output n :=
  (Fintype.equivFin (RawProtocol.Output n)).symm
    (BB84DeferredRaw.recoverLabel θ T minKey tolerance (Fintype.equivFin _ p))

def rawState {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :=
  Guessing.relabel (Guessing.relabel (jointState v hv k gap c) (labelEquiv n))
    (decodeRawLabel (basis c) c.2 minKey tolerance)

theorem decoded_acceptance {n : Nat} (θ : Fin n → BB84Basis) (T : Finset (Fin n))
    (minKey tolerance : Nat) (r s : Fin (count n)) :
    (decodeRawLabel θ T minKey tolerance (r,s)).transcript.accepted =
      decide (BB84DelayedDecision.accepts T minKey tolerance r) :=
  BB84DecisionRaw.recovered_acceptance θ T minKey tolerance r s

theorem rawState_physical {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :
    (rawState v hv k gap minKey tolerance c).density.matrix =
      (PairwiseRawPost.afterFirst (basis c) e c.2 minKey tolerance).toKraus.apply
        ((first (basis c) e).toKraus.apply
          (((keyChannel (basis c)).amplify e).toKraus.apply
            (SupportProjection.state (PairwiseQuantumSampling.good k gap c) v
              (PairwiseQuantumSampling.fallback v hv)).matrix)) := by
  rw [rawState, Guessing.relabel_physical]
  change (classicalMap e (fun t => Fintype.equivFin (RawProtocol.Output n)
    (decodeRawLabel (basis c) c.2 minKey tolerance ((Fintype.equivFin _).symm t)))).toKraus.apply
      (Guessing.relabel (jointState v hv k gap c) (labelEquiv n)).density.matrix = _
  simp only [decodeRawLabel, Equiv.apply_symm_apply]
  rw [labelled_joint]
  have hs := PartitionMeasurement.sequential_discard_eq
    (fun p => (BB84OutcomeCoordinates.encode (basis c) p).1)
    (fun p => (BB84OutcomeCoordinates.encode (basis c) p).2)
    (((keyChannel (basis c)).amplify e).toKraus.apply
      (SupportProjection.state (PairwiseQuantumSampling.good k gap c) v
        (PairwiseQuantumSampling.fallback v hv)).matrix)
  simp only [PartitionMeasurement.sequentialDiscard, PartitionMeasurement.sequential,
    Channel.seq, Kraus.seq_apply] at hs
  simp only [PairwiseRawPost.afterFirst, first, BB84DecisionRaw.finish, Channel.seq, Kraus.seq_apply]
  dsimp only [BB84DeferredRaw.signalLabel, PartitionMeasurement.together, BB84OutcomeCoordinates.encode,
    errorLabel, keyLabel] at hs ⊢
  exact congrArg (fun ρ => (classicalMap e
    (BB84DeferredRaw.recoverLabel (basis c) c.2 minKey tolerance)).toKraus.apply ρ) hs.symm

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
