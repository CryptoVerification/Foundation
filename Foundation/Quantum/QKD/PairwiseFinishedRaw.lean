import Foundation.Quantum.QKD.PairwiseExpandedRecovered
import Foundation.Quantum.QKD.SubnormalizedDiscard

/-! The same phase-support certificate after the actual full-position raw
restoration and unmatched-signal discard, with conditional Eve blocks explicit. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false

def finishedRawCQ {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  Guessing.post (Guessing.relabel (recoveredRawCQ A M k gap minKey tolerance c)
    (BB84SiftedInput.restoreOutput M θ))
    (discardFirst (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e)

theorem finishedRawCQ_physical {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    (finishedRawCQ A M (BB84SiftedInput.joinBases M (PairwiseRecordedSampling.basis c,η))
      k gap minKey tolerance c).density.matrix =
      (restoredRaw A M η k gap minKey tolerance c).matrix := by
  rw [← joint_ofCQ]
  unfold finishedRawCQ
  rw [← post_ofCQ, post_physical, joint_ofCQ, discardFirst_retained,
    Guessing.relabel_physical]
  simp only [Channel.run]
  rw [recoveredRawCQ_physical]
  simp only [restoredRaw, BB84SiftedInput.finish, BB84SiftedInput.restoreChannel,
    Channel.run, Channel.seq, Kraus.seq_apply]

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
