import Foundation.Quantum.QKD.PairwiseFinishedSecrecy
import Foundation.Quantum.QKD.CommonKeyMixture

/-! Actual basis/test randomness averaged on a fixed selected-position set.
The accepted output is subnormalized throughout, including zero-mass branches. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false

def conditionalAcceptedHash {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat)
    (hk : k ≤ BB84SiftedInput.selectedCount M) :=
  mixture (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk) (fun c =>
    finishedAcceptedHash (length := length) A M
      (BB84SiftedInput.joinBases M (PairwiseRecordedSampling.basis c,η))
      k gap (BB84SiftingRandomness.requiredLength M k minKey) tolerance c)

def conditionalPrivacyError {n length : Nat} (M : Finset (Fin n)) (k gap minKey tolerance : Nat)
    (hk : k ≤ BB84SiftedInput.selectedCount M) : ℝ :=
  ∑ c, (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk c).toReal *
    ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) * ((1-1/Fintype.card (IdealKey.Key length))*
      (((2:ℝ)^c.2.card * bound k gap (BB84SiftingRandomness.requiredLength M k minKey) tolerance c)*1))))

theorem conditional_accepted_secrecy {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat)
    (hk : k ≤ BB84SiftedInput.selectedCount M) :
    OperatorApprox (joint (conditionalAcceptedHash (length := length) A M η k gap minKey tolerance hk))
      (joint (CommonKey.uniformize (conditionalAcceptedHash (length := length) A M η k gap minKey tolerance hk)))
      (conditionalPrivacyError (length := length) M k gap minKey tolerance hk) :=
  CommonKey.mixture_secrecy _ _ _ (fun c => finished_accepted_secrecy A M
    (BB84SiftedInput.joinBases M (PairwiseRecordedSampling.basis c,η)) k gap
    (BB84SiftingRandomness.requiredLength M k minKey) tolerance c)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
