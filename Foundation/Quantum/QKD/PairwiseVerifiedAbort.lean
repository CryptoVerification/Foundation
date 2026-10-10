import Foundation.Quantum.QKD.VerifiedHashLaws
import Foundation.Quantum.QKD.PairwiseInsufficientSecrecy

/-! The original insufficient-test branch is retained as an abort. Its
accepted checked-and-hashed output is zero at original branch weight. -/
namespace Foundation.Quantum.QKD.PairwiseExpandedVerification
noncomputable section
open Subnormalized BB84SiftedInput PairwisePhaseCoordinates
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

theorem reference_abort {n tag length : Nat} {e : Space}
    (M : Finset (Fin n)) (θ : Fin n → BB84Basis) (T : Finset (Fin (selectedCount M)))
    (minKey tolerance : Nat) (h : selectedCount M < minKey)
    (ρ : Density (.tensor (signalSpace (selectedCount M)) (auxiliary M e))) :
    VerifiedHash.fromDensity (tag := tag) (length := length) ((referenceOutput M θ e T minKey tolerance).run ρ) = zero := by
  let f : Fin (Fintype.card (signalSpace (selectedCount M)).Basis) → Fin (Fintype.card (RawProtocol.Output (selectedCount M))) :=
    fun r => BB84DeferredRaw.rawLabel (bases M θ) T minKey tolerance
      ((Fintype.equivFin (signalSpace (selectedCount M)).Basis).symm r)
  let g : Fin (Fintype.card (RawProtocol.Output (selectedCount M))) → Fin (Fintype.card (RawProtocol.Output n)) :=
    fun r => Fintype.equivFin _ (restoreOutput M θ ((Fintype.equivFin _).symm r))
  let C := (((BB84ErrorTransform.basisChannel (selectedCount M) (bases M θ)).amplify (auxiliary M e)).seq
    (FirstRegister.channel (signalSpace (selectedCount M)) (auxiliary M e))).seq
      (discardMiddle (.register (Fintype.card (signalSpace (selectedCount M)).Basis))
        (signalSpace (remainderCount M)) e)
  let out : Fin (Fintype.card (signalSpace (selectedCount M)).Basis) → RawProtocol.Output n :=
    fun r => restoreOutput M θ ((Fintype.equivFin _).symm (f r))
  have he : ((referenceOutput M θ e T minKey tolerance).run ρ).matrix =
      ((classicalMap e (fun r => Fintype.equivFin _ (out r))).run (C.run ρ)).matrix := by
    simp only [referenceOutput, finish, BB84DeferredRaw.reference, restoreChannel,
      Channel.run, Channel.seq, Kraus.seq_apply]
    change (discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (signalSpace (remainderCount M)) e).toKraus.apply
      ((classicalMap (auxiliary M e) g).toKraus.apply ((classicalMap (auxiliary M e) f).toKraus.apply _)) = _
    rw [classicalMap_discardMiddle, classicalMap_discardMiddle, classicalMap_compose]
    have hgf : g ∘ f = (fun r => Fintype.equivFin _ (out r)) := rfl
    rw [hgf]
    congr 1
    simp only [C, Channel.seq, Kraus.seq_apply]
  rw [VerifiedHash.fromDensity_congr (tag := tag) (length := length) _ _ he]
  apply VerifiedHash.fromDensity_abort_map (tag := tag) (length := length)
  intro r
  simp only [out, f, BB84DeferredRaw.rawLabel, Equiv.symm_apply_apply, restoreOutput, RawProtocol.output]
  exact RawProtocol.too_short _ _ _ _ _ _ _ h


theorem delayed_abort {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (T : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) (h : selectedCount M < minKey) :
    VerifiedHash.fromDensity (tag := tag) (length := length) ((delayedOutput M θ e T minKey tolerance).run (input A M)) = zero := by
  rw [VerifiedHash.fromDensity_congr (tag := tag) (length := length) _ ((referenceOutput M θ e T minKey tolerance).run (input A M))
    (finished_interpreted A M θ T minKey tolerance)]
  exact reference_abort M θ T minKey tolerance h (input A M)

theorem conditional_insufficient_zero {n tag length : Nat} {e : Space}
    (A : BlockAttack n e) (M : Finset (Fin n))
    (η : Fin (remainderCount M) → BB84Basis) (k gap minKey tolerance : Nat)
    (hk : ¬ k ≤ selectedCount M) :
    VerifiedHash.fromDensity (tag := tag) (length := length) (conditionalCertificate A M η k gap minKey tolerance) = zero := by
  have hc : selectedCount M = M.card := Fintype.card_coe M
  have hlen : selectedCount M < BB84SiftingRandomness.requiredLength M k minKey := by
    have hkm : ¬ k ≤ M.card := by simpa only [hc] using hk
    simp only [BB84SiftingRandomness.requiredLength, hkm, ite_false, hc]
    omega
  unfold conditionalCertificate
  rw [dif_neg hk]
  unfold PairwiseRandomizedSampling.conditionalReal
  rw [VerifiedHash.fromDensity_mixture (tag := tag) (length := length)]
  have hz (θ : Fin (selectedCount M) → BB84Basis) :
      VerifiedHash.fromDensity (tag := tag) (length := length) (Density.mixture
        (BB84SiftingRandomness.testDistribution (Finset.univ : Finset (Fin (selectedCount M))) k)
        (fun T => (delayedOutput M (joinBases M (θ,η)) e T
          (BB84SiftingRandomness.requiredLength M k minKey) tolerance).run (input A M))) = zero := by
    rw [VerifiedHash.fromDensity_mixture (tag := tag) (length := length)]
    have hT (T : Finset (Fin (selectedCount M))) := delayed_abort (tag := tag) (length := length) A M (joinBases M (θ,η)) T
      (BB84SiftingRandomness.requiredLength M k minKey) tolerance hlen
    simp_rw [hT]
    exact mixture_zero _
  simp_rw [hz]
  exact mixture_zero _


end
end Foundation.Quantum.QKD.PairwiseExpandedVerification
