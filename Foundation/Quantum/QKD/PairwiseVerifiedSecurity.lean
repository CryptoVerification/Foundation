import Foundation.Quantum.QKD.PairwiseVerifiedRealSecrecy
import Foundation.Quantum.QKD.VerifiedHashFullOutput

/-! Full normalized actual randomized BB84 with the specified check and PA,
under arbitrary finite Kraus block attacks. Public communication is assumed
authentic by this model; useful parameter bounds and error correction remain. -/
namespace Foundation.Quantum.QKD.PairwiseExpandedVerification
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def realVerifiedState {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :=
  VerifiedHash.fullState (tag := tag) (length := length)
    (readDensity (Randomized.keyState A k minKey tolerance)) (mass_ofCQ _)

/-- Actual two-key output, aborts, public records, both public seeds and Eve
are all included. The error is a proved expression, not a useful-key claim. -/
theorem real_verified_secure {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    IdealKey.Secure (realVerifiedState (tag := tag) (length := length) A k minKey tolerance)
      (1 / Fintype.card (IdealKey.Key tag) +
        (2*PairwiseRandomizedSampling.error n k gap + globalPrivacyError n tag length k gap minKey tolerance)) := by
  apply VerifiedHash.full_secure
  exact real_verified_secrecy A k gap minKey tolerance

end
end Foundation.Quantum.QKD.PairwiseExpandedVerification
