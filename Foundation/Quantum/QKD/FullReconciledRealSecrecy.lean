import Foundation.Quantum.QKD.UniformKeyDistance
import Foundation.Quantum.QKD.FullReconciledGlobalSecrecy

/-! Transfer the proved support-state bound to the actual whole randomized
BB84 experiment, with arbitrary finite Kraus block attacks. The same public
check, tag and both public seeds are used in real and certificate states. -/
namespace Foundation.Quantum.QKD.FullReconciledSecurity
noncomputable section
open Subnormalized PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def realHash {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :=
  FullReconciledHash.fromDensity (tag := tag) (length := length) (Randomized.keyState A k minKey tolerance)

theorem real_verified_certificate {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    OperatorApprox (joint (realHash (tag := tag) (length := length) A k minKey tolerance))
      (joint (globalHash (tag := tag) (length := length) A k gap minKey tolerance))
      (PairwiseRandomizedSampling.error n k gap) :=
  FullReconciledHash.fromDensity_approx _ _ _ (certificate_approximation A k gap minKey tolerance)

/-- Unconditioned accepted Alice secrecy for the actual randomized experiment.
No division by the probability of either acceptance test is performed. -/
theorem real_verified_secrecy {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    OperatorApprox (joint (realHash (tag := tag) (length := length) A k minKey tolerance))
      (joint (CommonKey.uniformize (realHash (tag := tag) (length := length) A k minKey tolerance)))
      (2*PairwiseRandomizedSampling.error n k gap + globalPrivacyError n tag length k gap minKey tolerance) :=
  CommonKey.secrecy_transfer _ _ _ _ (real_verified_certificate A k gap minKey tolerance)
    (global_verified_secrecy A k gap minKey tolerance)

end
end Foundation.Quantum.QKD.FullReconciledSecurity
