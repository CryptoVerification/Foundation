import Foundation.Quantum.QKD.PairwiseAuxiliaryRecovery
import Foundation.Quantum.QKD.PairwiseAcceptedHash

/-! Accepted raw-key secrecy after recovering the original attack environment.
Both the actual output and its own uniform-key comparator undergo the same
physical partial trace; unmatched signals are still retained. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false

def recoveredAcceptedHash {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed (BB84SiftedInput.selectedCount M) length))
    (restrict (ofCQ (recoveredRawCQ A M k gap minKey tolerance c))
      (fun o => o.transcript.accepted = true)))
    (fun so => (Hashing.rawHash so.1 so.2.aliceKey,(so.2.transcript,so.1)))

theorem recoveredAcceptedHash_eq {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    recoveredAcceptedHash (length := length) A M k gap minKey tolerance c =
      post (acceptedRawHash (length := length) (PairwiseAttackSampling.vector A M)
        (PairwiseAttackSampling.unit A M) k gap minKey tolerance c)
        (auxiliaryDiscard (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e
          (PairwiseRecovery.krausSpace A)) := by
  unfold recoveredAcceptedHash acceptedRawHash recoveredRawCQ
  rw [post_relabel, post_seed, post_restrict, post_ofCQ]

theorem recovered_accepted_secrecy {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (recoveredAcceptedHash (length := length) A M k gap minKey tolerance c))
      (joint (CommonKey.uniformize (recoveredAcceptedHash (length := length) A M k gap minKey tolerance c)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) * ((1-1/Fintype.card (IdealKey.Key length))*
        (((2:ℝ)^c.2.card * bound k gap minKey tolerance c)*1)))) := by
  rw [recoveredAcceptedHash_eq]
  exact CommonKey.quantumProcess_secrecy _ _ _
    (accepted_raw_secrecy (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M)
      k gap minKey tolerance c)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
