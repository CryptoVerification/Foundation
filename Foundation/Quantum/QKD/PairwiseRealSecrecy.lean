import Foundation.Quantum.QKD.PairwiseGlobalSecrecy
import Foundation.Quantum.QKD.AcceptedHashDistance

/-! Accepted Alice-key secrecy for the actual whole randomized BB84 raw
experiment under arbitrary finite Kraus block attacks. Phase-support privacy
and the proved sampling approximation are composed, not assumed as bounds. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false

def realAcceptedHash {n length : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :=
  AcceptedHash.fromDensity (Randomized.keyState A k minKey tolerance)
    (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash

theorem real_hash_certificate {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    OperatorApprox (joint (realAcceptedHash (length := length) A k minKey tolerance))
      (joint (globalAcceptedHash (length := length) A k gap minKey tolerance))
      (PairwiseRandomizedSampling.error n k gap) :=
  AcceptedHash.fromDensity_approx _ _ _ _ _ (certificate_approximation A k gap minKey tolerance)

theorem real_accepted_secrecy {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    OperatorApprox (joint (realAcceptedHash (length := length) A k minKey tolerance))
      (joint (CommonKey.uniformize (realAcceptedHash (length := length) A k minKey tolerance)))
      (2*PairwiseRandomizedSampling.error n k gap + privacyError n length k gap minKey tolerance) :=
  CommonKey.secrecy_transfer _ _ _ _ (real_hash_certificate A k gap minKey tolerance)
    (global_accepted_secrecy A k gap minKey tolerance)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
