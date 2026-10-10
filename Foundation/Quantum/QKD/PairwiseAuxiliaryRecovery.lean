import Foundation.Quantum.QKD.PairwiseRawRestoration
import Foundation.Quantum.QKD.CommonKeyProcessing

/-! Remove only the purification's Kraus label in the conditional quantum
blocks, retaining unmatched signals and the original adversary's system. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false

def auxiliaryDiscard (b e r : Space) : Channel (.tensor b (.tensor e r)) (.tensor b e) :=
  (BasisChannel.channel (Equiv.prodAssoc b.Basis e.Basis r.Basis).symm).seq
    (discardRight (.tensor b e) r)

theorem auxiliaryDiscard_entry (b e r : Space) (A : Operator (.tensor b (.tensor e r)))
    (u v : b.Basis) (x y : e.Basis) :
    (auxiliaryDiscard b e r).toKraus.apply A (u,x) (v,y) =
      ∑ t : r.Basis, A (u,(x,t)) (v,(y,t)) := by
  unfold auxiliaryDiscard
  rw [Channel.seq, Kraus.seq_apply, discardRight_apply, BasisChannel.apply]
  rfl

theorem auxiliaryDiscard_retained (a b e r : Space) (A : Operator (.tensor a (.tensor b (.tensor e r)))) :
    (Subnormalized.rightChannel a (auxiliaryDiscard b e r)).toKraus.apply A =
      (NestedDiscard.channel a b e r).toKraus.apply A := by
  ext ⟨i,u,x⟩ ⟨j,v,y⟩
  rw [Subnormalized.rightChannel_entry, auxiliaryDiscard_entry, NestedDiscard.apply_entry]
  rfl

def recoveredRawCQ {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :=
  Guessing.post (rawState (PairwiseAttackSampling.vector A M) (PairwiseAttackSampling.unit A M)
    k gap minKey tolerance c)
    (auxiliaryDiscard (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e
      (PairwiseRecovery.krausSpace A))

theorem recoveredRawCQ_physical {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration (BB84SiftedInput.selectedCount M)) :
    (recoveredRawCQ A M k gap minKey tolerance c).density.matrix =
      (recoveredRaw A M k gap minKey tolerance c).matrix := by
  rw [← Subnormalized.joint_ofCQ]
  unfold recoveredRawCQ
  rw [← Subnormalized.post_ofCQ, Subnormalized.post_physical, Subnormalized.joint_ofCQ,
    auxiliaryDiscard_retained]
  rfl

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
