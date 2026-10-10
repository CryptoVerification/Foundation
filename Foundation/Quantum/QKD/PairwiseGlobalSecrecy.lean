import Foundation.Quantum.QKD.PairwiseInsufficientSecrecy

/-! Accepted Alice-key secrecy of the whole raw sampling certificate.
All selected sets and unmatched bases use their actual distributions;
insufficient-test branches are retained and contribute zero accepted mass. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized BB84SiftedInput
set_option backward.isDefEq.respectTransparency false
local instance : Nonempty BB84Basis := ⟨.Z⟩

def conditionalSecrecyError {n length : Nat} (M : Finset (Fin n)) (k gap minKey tolerance : Nat) : ℝ :=
  if hk : k ≤ selectedCount M then conditionalPrivacyError (length := length) M k gap minKey tolerance hk else 0

theorem conditional_all_secrecy {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat) :
    OperatorApprox
      (joint (AcceptedHash.fromDensity (conditionalCertificate A M η k gap minKey tolerance)
        (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash))
      (joint (CommonKey.uniformize (AcceptedHash.fromDensity (conditionalCertificate A M η k gap minKey tolerance)
        (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash)))
      (conditionalSecrecyError (length := length) M k gap minKey tolerance) := by
  unfold conditionalSecrecyError
  split_ifs with hk
  · exact conditional_certificate_secrecy A M η k gap minKey tolerance hk
  · rw [conditional_insufficient_zero A M η k gap minKey tolerance hk]
    exact CommonKey.zero_secrecy

def globalAcceptedHash {n length : Nat} {e : Space} (A : BlockAttack n e) (k gap minKey tolerance : Nat) :=
  AcceptedHash.fromDensity (certificate A k gap minKey tolerance)
    (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash

def privacyError (n length k gap minKey tolerance : Nat) : ℝ :=
  ∑ M : Finset (Fin n), (Foundation.Probability.uniform (Finset (Fin n)) M).toReal *
    conditionalSecrecyError (length := length) M k gap minKey tolerance

theorem global_accepted_secrecy {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    OperatorApprox (joint (globalAcceptedHash (length := length) A k gap minKey tolerance))
      (joint (CommonKey.uniformize (globalAcceptedHash (length := length) A k gap minKey tolerance)))
      (privacyError n length k gap minKey tolerance) := by
  unfold globalAcceptedHash certificate
  rw [AcceptedHash.fromDensity_mixture]
  simp_rw [AcceptedHash.fromDensity_mixture]
  apply CommonKey.mixture_secrecy
  intro M
  have hh := CommonKey.mixture_secrecy
    (Foundation.Probability.uniform (Fin (remainderCount M) → BB84Basis)) _
    (fun _ => conditionalSecrecyError (length := length) M k gap minKey tolerance)
    (fun η => conditional_all_secrecy A M η k gap minKey tolerance)
  simpa only [← Finset.sum_mul, Density.probability_weights, one_mul] using hh

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
