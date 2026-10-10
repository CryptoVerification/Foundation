import Foundation.Quantum.QKD.BB84AbortBranches
import Foundation.Quantum.QKD.ZeroSecrecy

/-! The actual insufficient-test branch has no accepted output. The whole
conditional abort experiment is unchanged in the sampling certificate. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized BB84SiftedInput
set_option backward.isDefEq.respectTransparency false

theorem delayed_abort {n length : Nat} {e : Space} {S : Type} [Fintype S] [DecidableEq S]
    (A : BlockAttack n e) (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (T : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) (h : selectedCount M < minKey)
    (p : PMF S) (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    AcceptedHash.fromDensity ((delayedOutput M θ e T minKey tolerance).run (input A M)) p hash = zero := by
  rw [AcceptedHash.fromDensity_congr _ ((referenceOutput M θ e T minKey tolerance).run (input A M))
    (finished_interpreted A M θ T minKey tolerance)]
  exact reference_abort M θ T minKey tolerance h (input A M) p hash

theorem conditional_insufficient_zero {n length : Nat} {e : Space} {S : Type} [Fintype S] [DecidableEq S]
    (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat)
    (hk : ¬ k ≤ selectedCount M) (p : PMF S)
    (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    AcceptedHash.fromDensity (conditionalCertificate A M η k gap minKey tolerance) p hash = zero := by
  have hc : selectedCount M = M.card := Fintype.card_coe M
  have hlen : selectedCount M < BB84SiftingRandomness.requiredLength M k minKey := by
    have hkm : ¬ k ≤ M.card := by simpa only [hc] using hk
    simp only [BB84SiftingRandomness.requiredLength, hkm, ite_false, hc]
    omega
  unfold conditionalCertificate
  rw [dif_neg hk]
  unfold PairwiseRandomizedSampling.conditionalReal
  rw [AcceptedHash.fromDensity_mixture]
  have hz (θ : Fin (selectedCount M) → BB84Basis) :
      AcceptedHash.fromDensity (Density.mixture
        (BB84SiftingRandomness.testDistribution (Finset.univ : Finset (Fin (selectedCount M))) k)
        (fun T => (delayedOutput M (joinBases M (θ,η)) e T
          (BB84SiftingRandomness.requiredLength M k minKey) tolerance).run (input A M))) p hash = zero := by
    rw [AcceptedHash.fromDensity_mixture]
    have hT (T : Finset (Fin (selectedCount M))) := delayed_abort A M (joinBases M (θ,η)) T
      (BB84SiftingRandomness.requiredLength M k minKey) tolerance hlen p hash
    simp_rw [hT]
    exact mixture_zero _
  simp_rw [hz]
  exact mixture_zero _

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
