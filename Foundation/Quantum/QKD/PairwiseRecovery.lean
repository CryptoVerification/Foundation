import Foundation.Quantum.QKD.PairwiseRecordedSampling
import Foundation.Quantum.NestedDiscard

/-! Recovery of the actual attacked source after purification, selection,
fixed-reference gates, and detailed error measurement. Only the newly added
Kraus environment is discarded. The original Eve and unmatched signals remain. -/
namespace Foundation.Quantum.QKD.PairwiseRecovery
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false

abbrev krausSpace {n : Nat} {e : Space} (A : BlockAttack n e) :=
  Space.register (Fintype.card A.index)

def discard {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n)) :=
  NestedDiscard.channel (BB84SiftedInput.signalSpace (BB84SiftedInput.selectedCount M))
    (BB84SiftedInput.signalSpace (BB84SiftedInput.remainderCount M)) e (krausSpace A)

theorem selected_entry {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (p q : (jointSpace (BB84SiftedInput.selectedCount M)
      (BB84SiftedInput.auxiliary M (PairwiseAttackSampling.environment A))).Basis) :
    (PairwiseAttackSampling.selected A M).matrix p q =
      (BB84PurifiedSource.state A).matrix
        ((PairwiseAttackSampling.transport A).symm
          ((BB84SiftedInput.jointEquiv M (PairwiseAttackSampling.environment A)).symm p))
        ((PairwiseAttackSampling.transport A).symm
          ((BB84SiftedInput.jointEquiv M (PairwiseAttackSampling.environment A)).symm q)) := by
  change (BasisChannel.channel _).toKraus.apply (PairwiseAttackSampling.transported A).matrix p q = _
  rw [BasisChannel.apply]
  change (BasisChannel.channel _).toKraus.apply (BB84PurifiedSource.state A).matrix _ _ = _
  rw [BasisChannel.apply]
  rfl

/-- Exact recovery after reversible matched-position selection, preserving
all coherences of the unmatched systems and the original attack output. -/
theorem selected {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n)) :
    (discard A M).toKraus.apply (PairwiseAttackSampling.selected A M).matrix =
      (BB84SiftedInput.input A M).matrix := by
  ext ⟨i,u,x⟩ ⟨j,v,y⟩
  rw [discard, NestedDiscard.apply_entry]
  simp_rw [selected_entry A M]
  rw [BB84SiftedInput.input_entry]
  change _ = (BasisChannel.channel _).toKraus.apply (BB84PreparedInput.unrotated A).matrix _ _
  rw [BasisChannel.apply]
  have h := BB84PurifiedSource.recover A
  change ((discardRight (.tensor (qubits n) e) (krausSpace A)).amplify (qubits n)).toKraus.apply
    (BB84PurifiedSource.state A).matrix = (BB84PreparedInput.unrotated A).matrix at h
  have he := congrArg (fun τ => τ
      (((BB84SiftedInput.splitEquiv M).symm (i.1,u.1),x),
        (BB84SiftedInput.splitEquiv M).symm (i.2,u.2))
      (((BB84SiftedInput.splitEquiv M).symm (j.1,v.1),y),
        (BB84SiftedInput.splitEquiv M).symm (j.2,v.2))) h
  rw [discardRight_amplify_apply] at he
  exact he

/-- The same equality after CNOT and the fixed Bob-Z/Alice-X reference gate. -/
theorem reference {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n)) :
    (discard A M).toKraus.apply (PairwiseAttackSampling.state A M).matrix =
      (referenceInput (BB84SiftedInput.input A M)).matrix := by
  unfold PairwiseAttackSampling.state referenceInput
  change (discard A M).toKraus.apply
    (((referenceChannel _).amplify _).toKraus.apply
      (((BB84ErrorTransform.cnotChannel _).amplify _).toKraus.apply
        (PairwiseAttackSampling.selected A M).matrix)) = _
  rw [discard, NestedDiscard.local_operations, NestedDiscard.local_operations]
  rw [← discard, selected]
  rfl

end
end Foundation.Quantum.QKD.PairwiseRecovery
