import Foundation.Quantum.QKD.PairwisePhaseMeasured
import Foundation.Quantum.QKD.CQRelabel

/-! Exact error/key record encoding used by the original delayed-measurement
implementation. The key/error CQ state and the physical discarded-signal
record agree as operators, including all auxiliary coherences. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference PairwiseRecordedSampling PureProjection
set_option backward.isDefEq.respectTransparency false

def labelEquiv (n : Nat) : ((qubits n).Basis × (qubits n).Basis) ≃ (Fin (count n) × Fin (count n)) where
  toFun p := (errorCode p.2,errorCode p.1)
  invFun p := (writeBits n ((Fintype.equivFin (Fin n → Fin 2)).symm p.2),
    writeBits n ((Fintype.equivFin (Fin n → Fin 2)).symm p.1))
  left_inv p := by simp only [errorCode, Equiv.symm_apply_apply, write_read]
  right_inv p := by simp only [errorCode, read_write, Equiv.apply_symm_apply]

theorem signal_label_fiber {n : Nat} (θ : Fin n → BB84Basis)
    (s : (signal n).Basis) (p : (qubits n).Basis × (qubits n).Basis) :
    BB84DeferredRaw.signalLabel θ s = Fintype.equivFin (Fin (count n) × Fin (count n)) (labelEquiv n p) ↔
      s = split n θ (p.2,p.1) := by
  change Fintype.equivFin _ (BB84OutcomeCoordinates.encode θ s) =
    Fintype.equivFin _ (errorCode p.2,errorCode p.1) ↔ _
  rw [Equiv.apply_eq_iff_eq, ← encode_split]
  exact (BB84OutcomeCoordinates.equivalence θ).injective.eq_iff

theorem labelled_joint {n : Nat} {e : Space} (v : (jointSpace n e).Basis → ℂ)
    (hv : bracket v v = 1) (k gap : Nat) (c : PairwiseSampling.Configuration n) :
    (Guessing.relabel (jointState v hv k gap c) (labelEquiv n)).density.matrix =
      (PartitionMeasurement.discardSignal (BB84DeferredRaw.signalLabel (basis c)) e).toKraus.apply
        (((keyChannel (basis c)).amplify e).toKraus.apply
          (SupportProjection.state (PairwiseQuantumSampling.good k gap c) v
            (PairwiseQuantumSampling.fallback v hv)).matrix) := by
  ext ⟨i,u⟩ ⟨j,w⟩
  obtain ⟨p,rfl⟩ := ((labelEquiv n).trans (Fintype.equivFin _)).surjective i
  obtain ⟨q,rfl⟩ := ((labelEquiv n).trans (Fintype.equivFin _)).surjective j
  simp only [Equiv.trans_apply]
  rw [Guessing.CQ.density_block, PartitionMeasurement.discard_entry]
  simp only [Equiv.apply_eq_iff_eq, (labelEquiv n).injective.eq_iff]
  by_cases hp : p = q
  · subst q
    simp only [ite_true, signal_label_fiber]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    have hb : (Guessing.relabel (jointState v hv k gap c) (labelEquiv n)).block (labelEquiv n p) =
        (jointState v hv k gap c).block p := by
      simp only [Guessing.relabel, (labelEquiv n).injective.eq_iff]
      simp
    rw [hb]
    exact key_diagonal v hv k gap c p.2 p.1 u w
  · simp only [hp, ite_false]

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
