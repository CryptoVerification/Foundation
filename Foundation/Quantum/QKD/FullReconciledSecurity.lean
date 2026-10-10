import Foundation.Quantum.QKD.FullReconciledRealSecrecy
import Foundation.Quantum.QKD.FullReconciledFullOutput

/-! Full normalized actual randomized BB84 with the specified check and PA,
under arbitrary finite Kraus block attacks. Public communication is assumed
authentic by this model; useful parameter bounds and authentication remain. -/
namespace Foundation.Quantum.QKD.FullReconciledSecurity
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def realState {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :=
  FullReconciledHash.fullState (tag := tag) (length := length)
    (readDensity (Randomized.keyState A k minKey tolerance)) (mass_ofCQ _)

/-- Actual two-key output, aborts, public records, both public seeds and Eve
are all included. The error is a proved expression, not a useful-key claim. -/
theorem real_verified_secure {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    IdealKey.Secure (realState (tag := tag) (length := length) A k minKey tolerance)
      (1 / Fintype.card (IdealKey.Key tag) +
        (2*PairwiseRandomizedSampling.error n k gap + globalPrivacyError n tag length k gap minKey tolerance)) := by
  apply FullReconciledHash.full_secure
  exact real_verified_secrecy A k gap minKey tolerance

/-- The same security comparison can retain the actual decoder-failure mass. -/
theorem real_verified_secure_weighted {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    IdealKey.Secure (realState (tag := tag) (length := length) A k minKey tolerance)
      ((1 / Fintype.card (IdealKey.Key tag)) * CommonKey.correctnessError
        (FullReconciledHash.checkedInput (readDensity (Randomized.keyState A k minKey tolerance))) +
        (2*PairwiseRandomizedSampling.error n k gap + globalPrivacyError n tag length k gap minKey tolerance)) := by
  apply FullReconciledHash.full_secure_weighted
  exact real_verified_secrecy A k gap minKey tolerance

end
end Foundation.Quantum.QKD.FullReconciledSecurity
