import Foundation.Quantum.QKD.PairwiseFinishedRaw

/-! Accepted Alice-key secrecy for the actual restored raw-state certificate,
with only the original adversary system retained. Public raw transcript and
the original full-position fresh hash seed remain explicit. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false

def finishedAcceptedHash {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
    (restrict (ofCQ (finishedRawCQ A M θ k gap minKey tolerance c))
      (fun o => o.transcript.accepted = true)))
    (fun so => (Hashing.rawHash so.1 so.2.aliceKey,(so.2.transcript,so.1)))

theorem finishedAcceptedHash_eq {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    finishedAcceptedHash (length := length) A M θ k gap minKey tolerance c =
      post (recoveredExpandedHash (length := length) A M θ k gap minKey tolerance c)
        (discardFirst (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e) := by
  unfold finishedAcceptedHash finishedRawCQ
  rw [← post_ofCQ, ← post_restrict, ← post_seed, ← post_relabel]
  congr 1
  rw [ofCQ_relabel, restrict_relabel, seed_relabel, relabel_comp]
  rfl

theorem finished_accepted_secrecy {n length : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    OperatorApprox (joint (finishedAcceptedHash (length := length) A M θ k gap minKey tolerance c))
      (joint (CommonKey.uniformize (finishedAcceptedHash (length := length) A M θ k gap minKey tolerance c)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) * ((1-1/Fintype.card (IdealKey.Key length))*
        (((2:ℝ)^c.2.card * bound k gap minKey tolerance c)*1)))) := by
  rw [finishedAcceptedHash_eq]
  exact CommonKey.quantumProcess_secrecy _ _ _ (recovered_expanded_secrecy A M θ k gap minKey tolerance c)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
