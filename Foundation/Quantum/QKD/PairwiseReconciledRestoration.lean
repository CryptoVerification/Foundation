import Foundation.Quantum.QKD.PairwiseReconciledRecovery
import Foundation.Quantum.QKD.PairwiseVerifiedRestoration
import Foundation.Quantum.QKD.SubnormalizedDiscard

/-! Restore the original public record of the same corrected raw-key
experiment, retain the exact fixed-type message and both seeds, then discard
unmatched signals. The output type is independent of the selected/test sets. -/
namespace Foundation.Quantum.QKD.PairwiseReconciledVerification
noncomputable section
open Subnormalized PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def restorePublic {n tag length : Nat} {e : Space} (M : Finset (Fin n))
    (θ : Fin n → BB84Basis)
    (ρ : State (IdealKey.Key length × ((((RawProtocol.PublicRecord (BB84SiftedInput.selectedCount M) ×
      ArbitraryReconciliation.Word n) × Hashing.RawSeed n tag) × IdealKey.Key tag) × Hashing.RawSeed n length)) e) :=
  CommonKey.publicProcess ρ (fun p =>
    ((((PairwiseExpandedVerification.restoreRecord M θ p.1.1.1.1,p.1.1.1.2),p.1.1.2),p.1.2),p.2))

def finishedHash {n tag length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  post (restorePublic M θ (recoveredAverage (tag := tag) (length := length) A M k gap minKey tolerance c))
    (discardFirst (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e)

/-- Direct processing of the recovered physical raw density, followed by
exact public restoration and unmatched-system removal. -/
theorem finished_hash_physical {n tag length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    finishedHash (tag := tag) (length := length) A M θ k gap minKey tolerance c =
      post (restorePublic M θ (ReconciledHash.fromDensity (tag := tag) (length := length) M c.2
        (recoveredRaw A M k gap minKey tolerance c)))
        (discardFirst (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e) := by
  rw [recovered_physical]
  rfl

theorem finished_secrecy {n tag length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (finishedHash (tag := tag) (length := length) A M θ k gap minKey tolerance c))
      (joint (CommonKey.uniformize (finishedHash (tag := tag) (length := length) A M θ k gap minKey tolerance c)))
      (privacyError tag length k gap minKey tolerance c) := by
  apply CommonKey.quantumProcess_secrecy
  apply CommonKey.publicProcess_secrecy
  exact recovered_average_secrecy A M k gap minKey tolerance c

end
end Foundation.Quantum.QKD.PairwiseReconciledVerification
