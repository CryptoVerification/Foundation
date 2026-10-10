import Foundation.Quantum.QKD.FullReconciledPhysical
import Foundation.Quantum.QKD.FullReconciledAbort

/-! Average the same checked-and-hashed physical certificate over the actual
basis, test and selected-set distributions, including insufficient-test aborts.
Both full-position public seeds and the original Eve system are retained. -/
namespace Foundation.Quantum.QKD.FullReconciledSecurity
noncomputable section
open Subnormalized BB84SiftedInput PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
local instance : Nonempty BB84Basis := ⟨.Z⟩

def conditionalPrivacyError {n : Nat} (tag length : Nat) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (hk : k ≤ selectedCount M) : ℝ :=
  ∑ c, (PairwiseSampling.distribution (selectedCount M) k hk c).toReal *
    PairwiseReconciledVerification.privacyError tag length k gap (BB84SiftingRandomness.requiredLength M k minKey) tolerance c

theorem conditional_certificate_secrecy {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (η : Fin (remainderCount M) → BB84Basis)
    (k gap minKey tolerance : Nat) (hk : k ≤ selectedCount M) :
    OperatorApprox
      (joint (FullReconciledHash.fromDensity (tag := tag) (length := length) (conditionalCertificate A M η k gap minKey tolerance)))
      (joint (CommonKey.uniformize (FullReconciledHash.fromDensity (tag := tag) (length := length)
        (conditionalCertificate A M η k gap minKey tolerance))))
      (conditionalPrivacyError tag length M k gap minKey tolerance hk) := by
  unfold conditionalCertificate
  rw [dif_pos hk, FullReconciledHash.fromDensity_mixture]
  exact CommonKey.mixture_secrecy _ _ _ (fun c => PairwiseReconciledVerification.full_physical_secrecy A M η k gap
    (BB84SiftingRandomness.requiredLength M k minKey) tolerance c)

def conditionalSecrecyError {n : Nat} (tag length : Nat) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) : ℝ :=
  if hk : k ≤ selectedCount M then conditionalPrivacyError tag length M k gap minKey tolerance hk else 0

theorem conditional_all_secrecy {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (η : Fin (remainderCount M) → BB84Basis)
    (k gap minKey tolerance : Nat) :
    OperatorApprox
      (joint (FullReconciledHash.fromDensity (tag := tag) (length := length) (conditionalCertificate A M η k gap minKey tolerance)))
      (joint (CommonKey.uniformize (FullReconciledHash.fromDensity (tag := tag) (length := length)
        (conditionalCertificate A M η k gap minKey tolerance))))
      (conditionalSecrecyError tag length M k gap minKey tolerance) := by
  unfold conditionalSecrecyError
  split_ifs with hk
  · exact conditional_certificate_secrecy A M η k gap minKey tolerance hk
  · rw [conditional_insufficient_zero A M η k gap minKey tolerance hk]
    exact CommonKey.zero_secrecy

def globalHash {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :=
  FullReconciledHash.fromDensity (tag := tag) (length := length) (certificate A k gap minKey tolerance)

def globalPrivacyError (n tag length k gap minKey tolerance : Nat) : ℝ :=
  ∑ M : Finset (Fin n), (Foundation.Probability.uniform (Finset (Fin n)) M).toReal *
    conditionalSecrecyError tag length M k gap minKey tolerance

theorem global_verified_secrecy {n tag length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    OperatorApprox (joint (globalHash (tag := tag) (length := length) A k gap minKey tolerance))
      (joint (CommonKey.uniformize (globalHash (tag := tag) (length := length) A k gap minKey tolerance)))
      (globalPrivacyError n tag length k gap minKey tolerance) := by
  unfold globalHash certificate
  rw [FullReconciledHash.fromDensity_mixture]
  simp_rw [FullReconciledHash.fromDensity_mixture]
  apply CommonKey.mixture_secrecy
  intro M
  have hh := CommonKey.mixture_secrecy
    (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis)) _
    (fun _ => conditionalSecrecyError tag length M k gap minKey tolerance)
    (fun η => conditional_all_secrecy A M η k gap minKey tolerance)
  simpa only [← Finset.sum_mul, Density.probability_weights, one_mul] using hh

end
end Foundation.Quantum.QKD.FullReconciledSecurity
