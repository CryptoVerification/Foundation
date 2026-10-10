import Foundation.Quantum.QKD.UniformKeyDistance
import Foundation.Quantum.QKD.PairwiseVerifiedGlobalSecrecy

/-! Transfer the proved support-state bound to the actual whole randomized
BB84 experiment, with arbitrary finite Kraus block attacks. The same public
check, tag and both public seeds are used in real and certificate states. -/
namespace Foundation.Quantum.QKD.PairwiseExpandedVerification
noncomputable section
open Subnormalized PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def realVerifiedHash {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :=
  VerifiedHash.fromDensity (tag := tag) (length := length) (Randomized.keyState A k minKey tolerance)

theorem real_verified_certificate {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    OperatorApprox (joint (realVerifiedHash (tag := tag) (length := length) A k minKey tolerance))
      (joint (globalVerifiedHash (tag := tag) (length := length) A k gap minKey tolerance))
      (PairwiseRandomizedSampling.error n k gap) :=
  VerifiedHash.fromDensity_approx _ _ _ (certificate_approximation A k gap minKey tolerance)

/-- Unconditioned accepted Alice secrecy for the actual randomized experiment.
No division by the probability of either acceptance test is performed. -/
theorem real_verified_secrecy {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    OperatorApprox (joint (realVerifiedHash (tag := tag) (length := length) A k minKey tolerance))
      (joint (CommonKey.uniformize (realVerifiedHash (tag := tag) (length := length) A k minKey tolerance)))
      (2*PairwiseRandomizedSampling.error n k gap + globalPrivacyError n tag length k gap minKey tolerance) :=
  CommonKey.secrecy_transfer _ _ _ _ (real_verified_certificate A k gap minKey tolerance)
    (global_verified_secrecy A k gap minKey tolerance)

end
end Foundation.Quantum.QKD.PairwiseExpandedVerification
