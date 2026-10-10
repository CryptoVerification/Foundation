import Foundation.Quantum.QKD.FullReconciledRestoration
import Foundation.Quantum.QKD.PairwiseFinishedRaw

/-! The public-record-driven full algorithm on the actual restored physical
certificate. It retains the original adversary and the entire public message.
The secrecy estimate is derived from the existing support/PA proof. -/
namespace Foundation.Quantum.QKD.PairwiseReconciledVerification
noncomputable section
open Subnormalized PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

theorem full_recovered_average {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (M : Finset (Fin n)) (θ : Fin n → BB84Basis) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    FullReconciledHash.average (tag := tag) (length := length)
      (relabel (ofCQ (recoveredRawCQ A M k gap minKey tolerance c)) (BB84SiftedInput.restoreOutput M θ)) =
      restorePublic M θ (recoveredAverage (tag := tag) (length := length) A M k gap minKey tolerance c) := by
  unfold recoveredRawCQ
  rw [← post_ofCQ, ← post_relabel, ← FullReconciledHash.post_average, full_raw_average]
  rw [recoveredAverage_eq]
  unfold restorePublic CommonKey.publicProcess
  simp only [post_relabel]

theorem full_physical {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (M : Finset (Fin n)) (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis)
    (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    FullReconciledHash.fromDensity (tag := tag) (length := length)
      (restoredRaw A M η k gap minKey tolerance c) =
      finishedHash (tag := tag) (length := length) A M
        (BB84SiftedInput.joinBases M (PairwiseRecordedSampling.basis c,η)) k gap minKey tolerance c := by
  unfold FullReconciledHash.fromDensity
  rw [readDensity_congr _ (finishedRawCQ A M
      (BB84SiftedInput.joinBases M (PairwiseRecordedSampling.basis c,η)) k gap minKey tolerance c).density
      (finishedRawCQ_physical A M η k gap minKey tolerance c).symm, readDensity_CQ]
  unfold finishedRawCQ
  rw [← post_ofCQ, ofCQ_relabel, ← FullReconciledHash.post_average, full_recovered_average]
  rfl

theorem full_physical_secrecy {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (M : Finset (Fin n)) (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis)
    (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (FullReconciledHash.fromDensity (tag := tag) (length := length)
        (restoredRaw A M η k gap minKey tolerance c)))
      (joint (CommonKey.uniformize (FullReconciledHash.fromDensity (tag := tag) (length := length)
        (restoredRaw A M η k gap minKey tolerance c))))
      (privacyError tag length k gap minKey tolerance c) := by
  rw [full_physical]
  exact finished_secrecy A M _ k gap minKey tolerance c

end
end Foundation.Quantum.QKD.PairwiseReconciledVerification
