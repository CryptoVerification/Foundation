import Foundation.Quantum.QKD.PairwiseAuxiliaryRecovery
import Foundation.Quantum.QKD.PairwiseExpandedAccepted

/-! Full-position raw-key hashing and restored public records after recovering
the original attack environment. The original full-position seed is public. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false

def recoveredExpandedHash {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (restrict (ofCQ (recoveredRawCQ A M k gap minKey tolerance c))
      (fun o => o.transcript.accepted = true)))
    (fun so => (Hashing.rawHash so.1 (BB84SiftedInput.expand M so.2.aliceKey),(restoreTranscript M θ so.2.transcript,so.1)))

theorem recoveredExpandedHash_eq {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    recoveredExpandedHash (length := length) A M θ k gap minKey tolerance c =
      post (expandedAcceptedHash (length := length) M θ (PairwiseAttackSampling.vector A M)
        (PairwiseAttackSampling.unit A M) k gap minKey tolerance c)
        (auxiliaryDiscard (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e
          (PairwiseRecovery.krausSpace A)) := by
  unfold recoveredExpandedHash expandedAcceptedHash recoveredRawCQ
  rw [post_relabel, post_seed, post_restrict, post_ofCQ]

theorem recovered_expanded_secrecy {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (recoveredExpandedHash (length := length) A M θ k gap minKey tolerance c))
      (joint (CommonKey.uniformize (recoveredExpandedHash (length := length) A M θ k gap minKey tolerance c)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) * ((1-1/Fintype.card (IdealKey.Key length))*
        (((2:ℝ)^c.2.card * bound k gap minKey tolerance c)*1)))) := by
  rw [recoveredExpandedHash_eq]
  exact CommonKey.quantumProcess_secrecy _ _ _
    (expanded_accepted_raw_secrecy M θ (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M)
      k gap minKey tolerance c)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
