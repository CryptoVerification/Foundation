import Foundation.Quantum.QKD.PairwiseRecordOrder
import Foundation.Quantum.NestedDiscardClassical

/-! Complete raw-record recovery commutes with tracing only the additional
purification environment. All original quantum auxiliary systems stay. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false

theorem after_first_record {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (T : Finset (Fin n)) (minKey tolerance : Nat) (ρ : Operator (jointSpace n e)) :
    (PairwiseRawPost.afterFirst θ e T minKey tolerance).toKraus.apply ((first θ e).toKraus.apply ρ) =
      (classicalMap e (BB84DeferredRaw.recoverLabel θ T minKey tolerance)).toKraus.apply
        ((PartitionMeasurement.discardSignal (BB84DeferredRaw.signalLabel θ) e).toKraus.apply ρ) := by
  have hs := PartitionMeasurement.sequential_discard_eq
    (fun p => (BB84OutcomeCoordinates.encode θ p).1)
    (fun p => (BB84OutcomeCoordinates.encode θ p).2) ρ
  simp only [PartitionMeasurement.sequentialDiscard, PartitionMeasurement.sequential,
    Channel.seq, Kraus.seq_apply] at hs
  simp only [PairwiseRawPost.afterFirst, first, BB84DecisionRaw.finish, Channel.seq, Kraus.seq_apply]
  dsimp only [BB84DeferredRaw.signalLabel, PartitionMeasurement.together,
    BB84OutcomeCoordinates.encode, errorLabel, keyLabel] at hs ⊢
  exact congrArg (fun σ => (classicalMap e
    (BB84DeferredRaw.recoverLabel θ T minKey tolerance)).toKraus.apply σ) hs

theorem raw_record_recovery {n : Nat} (θ : Fin n → BB84Basis) (b e r : Space)
    (T : Finset (Fin n)) (minKey tolerance : Nat)
    (ρ : Operator (jointSpace n (.tensor b (.tensor e r)))) :
    (NestedDiscard.channel (.register (Fintype.card (RawProtocol.Output n))) b e r).toKraus.apply
      ((PairwiseRawPost.afterFirst θ (.tensor b (.tensor e r)) T minKey tolerance).toKraus.apply
        ((first θ (.tensor b (.tensor e r))).toKraus.apply
          (((keyChannel θ).amplify (.tensor b (.tensor e r))).toKraus.apply ρ))) =
      (PairwiseRawPost.afterFirst θ (.tensor b e) T minKey tolerance).toKraus.apply
        ((first θ (.tensor b e)).toKraus.apply
          (((keyChannel θ).amplify (.tensor b e)).toKraus.apply
            ((NestedDiscard.channel (signal n) b e r).toKraus.apply ρ))) := by
  rw [after_first_record, after_first_record, NestedDiscard.classical_map,
    NestedDiscard.discard_signal, NestedDiscard.local_operations]

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
