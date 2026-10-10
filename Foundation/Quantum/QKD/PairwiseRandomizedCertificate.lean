import Foundation.Quantum.QKD.PairwiseRawRestoration

/-! The measured support-certificate states, after actual environment recovery
and original-position restoration, reconstruct the whole randomized raw
sampling approximant. Insufficient-test abort branches remain unchanged. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : Nonempty BB84Basis := ⟨.Z⟩

def conditionalCertificate {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat) :=
  if hk : k ≤ BB84SiftedInput.selectedCount M then
    Density.mixture (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk)
      (fun c => restoredRaw A M η k gap (BB84SiftingRandomness.requiredLength M k minKey) tolerance c)
  else PairwiseRandomizedSampling.conditionalReal A M η k minKey tolerance

theorem conditionalCertificate_eq {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (BB84SiftedInput.remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat) :
    (conditionalCertificate A M η k gap minKey tolerance).matrix =
      (PairwiseRandomizedSampling.conditionalIdeal A M η k gap minKey tolerance).matrix := by
  unfold conditionalCertificate PairwiseRandomizedSampling.conditionalIdeal
  split_ifs with hk
  · change _ = (PairwiseRawSampling.forget n e (BB84SiftedInput.selectedCount M)).toKraus.apply _
    rw [raw_ideal_eq, PairwiseRawSampling.forget, publicMixture_forget]
    rfl
  · rfl

def certificate {n : Nat} {e : Space} (A : BlockAttack n e) (k gap minKey tolerance : Nat) :=
  Density.mixture (Foundation.Probability.uniform (Finset (Fin n))) (fun M =>
    Density.mixture (Foundation.Probability.uniform (Fin (BB84SiftedInput.remainderCount M) → BB84Basis))
      (fun η => conditionalCertificate A M η k gap minKey tolerance))

theorem certificate_eq {n : Nat} {e : Space} (A : BlockAttack n e) (k gap minKey tolerance : Nat) :
    (certificate A k gap minKey tolerance).matrix =
      (PairwiseRandomizedSampling.ideal A k gap minKey tolerance).matrix := by
  apply Density.mixture_congr_matrix
  intro M
  apply Density.mixture_congr_matrix
  intro η
  exact conditionalCertificate_eq _ _ _ _ _ _ _

theorem certificate_approximation {n : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    StateApprox (Randomized.keyState A k minKey tolerance)
      (certificate A k gap minKey tolerance) (PairwiseRandomizedSampling.error n k gap) := by
  have h := PairwiseRandomizedSampling.approximation A k gap minKey tolerance
  change OperatorApprox _ _ _ at h ⊢
  rw [certificate_eq]
  exact h

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
