import Foundation.Quantum.QKD.AcceptedHashProcess
import Foundation.Quantum.QKD.PairwiseConditionalSecrecy
import Foundation.Quantum.QKD.PairwiseRandomizedCertificate

/-! Identify the averaged secrecy-certified accepted hash with the same
operation on the already constructed conditional raw sampling certificate. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false

theorem finished_hash_process {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    AcceptedHash.fromDensity (restoredRaw A M η k gap minKey tolerance c)
      (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash =
    finishedAcceptedHash (length := length) A M
      (BB84SiftedInput.joinBases M (PairwiseRecordedSampling.basis c,η)) k gap minKey tolerance c := by
  rw [← AcceptedHash.fromDensity_congr _ _ (finishedRawCQ_physical A M η k gap minKey tolerance c),
    AcceptedHash.fromDensity_CQ]
  rfl

theorem conditional_hash_process {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat)
    (hk : k ≤ BB84SiftedInput.selectedCount M) :
    AcceptedHash.fromDensity (conditionalCertificate A M η k gap minKey tolerance)
      (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash =
    conditionalAcceptedHash (length := length) A M η k gap minKey tolerance hk := by
  unfold conditionalCertificate
  rw [dif_pos hk, AcceptedHash.fromDensity_mixture]
  unfold conditionalAcceptedHash
  congr 1
  funext c
  exact finished_hash_process A M η k gap _ tolerance c

theorem conditional_certificate_secrecy {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat)
    (hk : k ≤ BB84SiftedInput.selectedCount M) :
    OperatorApprox
      (joint (AcceptedHash.fromDensity (conditionalCertificate A M η k gap minKey tolerance)
        (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash))
      (joint (CommonKey.uniformize (AcceptedHash.fromDensity (conditionalCertificate A M η k gap minKey tolerance)
        (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash)))
      (conditionalPrivacyError (length := length) M k gap minKey tolerance hk) := by
  rw [conditional_hash_process A M η k gap minKey tolerance hk]
  exact conditional_accepted_secrecy A M η k gap minKey tolerance hk

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
