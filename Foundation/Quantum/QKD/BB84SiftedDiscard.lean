import Foundation.Quantum.QKD.BB84SiftedRecord
import Foundation.Quantum.FirstRegisterSplit
import Foundation.Quantum.ClassicalDiscard
import Foundation.Quantum.LocalOperations

/-! Finish the interpreted selected experiment by restoring original raw
labels and physically discarding the unmatched signals. Eve remains quantum.
Local unmatched basis operations cannot affect this retained output. -/
namespace Foundation.Quantum.QKD.BB84SiftedInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

def finish {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis) (e : Space) :=
  (restoreChannel M θ (auxiliary M e)).seq
    (discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (signalSpace (remainderCount M)) e)

def delayedOutput {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis) (e : Space)
    (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) :=
  (BB84DecisionRaw.decided (bases M θ) (auxiliary M e) S minKey tolerance).seq (finish M θ e)

def referenceOutput {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis) (e : Space)
    (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) :=
  (BB84DeferredRaw.reference (bases M θ) (auxiliary M e) S minKey tolerance).seq (finish M θ e)

/-- Apply physical discard to the equality obtained by evaluating the finite
closed derivation on the actual attacked, selected entangled source. -/
theorem finished_interpreted {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) :
    (delayedOutput M θ e S minKey tolerance).toKraus.apply (input A M).matrix =
      (referenceOutput M θ e S minKey tolerance).toKraus.apply (input A M).matrix := by
  simp only [delayedOutput, referenceOutput, finish, Channel.seq, Kraus.seq_apply]
  exact congrArg (discardMiddle (.register (Fintype.card (RawProtocol.Output n)))
    (signalSpace (remainderCount M)) e).toKraus.apply
      (restored_interpreted A M θ S minKey tolerance)

/-- A local unmatched isometry before the ordinary selected measurement
does not change the eventual raw output after unmatched signal discard. -/
theorem unmatched_irrelevant {n : Nat} {e : Space} (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat)
    (U : Operator (signalSpace (remainderCount M))) (hU : U.conjTranspose * U = 1)
    (ρ : Operator (.tensor (signalSpace (selectedCount M)) (auxiliary M e))) :
    (referenceOutput M θ e S minKey tolerance).toKraus.apply
      ((Kraus.single (Op.tensor (Op.ident (signalSpace (selectedCount M))) (Op.tensor U (Op.ident e)))).apply ρ) =
    (referenceOutput M θ e S minKey tolerance).toKraus.apply ρ := by
  let f : Fin (Fintype.card (signalSpace (selectedCount M)).Basis) → Fin (Fintype.card (RawProtocol.Output (selectedCount M))) := fun r => BB84DeferredRaw.rawLabel (bases M θ) S minKey tolerance
    ((Fintype.equivFin (signalSpace (selectedCount M)).Basis).symm r)
  let g := fun r : Fin (Fintype.card (RawProtocol.Output (selectedCount M))) =>
    Fintype.equivFin (RawProtocol.Output n)
      (restoreOutput M θ ((Fintype.equivFin (RawProtocol.Output (selectedCount M))).symm r))
  simp only [referenceOutput, finish, BB84DeferredRaw.reference, Channel.seq, Kraus.seq_apply]
  change (discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (signalSpace (remainderCount M)) e).toKraus.apply
      ((classicalMap (.tensor (signalSpace (remainderCount M)) e) g).toKraus.apply
        ((classicalMap (.tensor (signalSpace (remainderCount M)) e) f).toKraus.apply
          ((FirstRegister.channel (signalSpace (selectedCount M)) (.tensor (signalSpace (remainderCount M)) e)).toKraus.apply
            (((BB84ErrorTransform.basisChannel (selectedCount M) (bases M θ)).amplify (.tensor (signalSpace (remainderCount M)) e)).toKraus.apply
              ((Kraus.single (Op.tensor (Op.ident (signalSpace (selectedCount M))) (Op.tensor U (Op.ident e)))).apply ρ))))) =
    (discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (signalSpace (remainderCount M)) e).toKraus.apply
      ((classicalMap (.tensor (signalSpace (remainderCount M)) e) g).toKraus.apply
        ((classicalMap (.tensor (signalSpace (remainderCount M)) e) f).toKraus.apply
          ((FirstRegister.channel (signalSpace (selectedCount M)) (.tensor (signalSpace (remainderCount M)) e)).toKraus.apply
            (((BB84ErrorTransform.basisChannel (selectedCount M) (bases M θ)).amplify (.tensor (signalSpace (remainderCount M)) e)).toKraus.apply ρ))))
  rw [classicalMap_discardMiddle, classicalMap_discardMiddle,
    classicalMap_discardMiddle, classicalMap_discardMiddle]
  have hc :
      ((BB84ErrorTransform.basisChannel (selectedCount M) (bases M θ)).amplify (auxiliary M e)).toKraus.apply
        ((Kraus.single (Op.tensor (Op.ident (signalSpace (selectedCount M))) (Op.tensor U (Op.ident e)))).apply ρ) =
      (Kraus.single (Op.tensor (Op.ident (signalSpace (selectedCount M))) (Op.tensor U (Op.ident e)))).apply
        (((BB84ErrorTransform.basisChannel (selectedCount M) (bases M θ)).amplify (auxiliary M e)).toKraus.apply ρ) := by
    simp only [Kraus.single_apply]
    exact Kraus.commute_right
      (a := signalSpace (selectedCount M)) (b := signalSpace (selectedCount M)) (r := auxiliary M e)
      (BB84ErrorTransform.basisChannel (selectedCount M) (bases M θ)).toKraus (Op.tensor U (Op.ident e)) ρ
  have h := (congrArg (fun τ =>
      (discardMiddle (.register (Fintype.card (signalSpace (selectedCount M)).Basis))
        (signalSpace (remainderCount M)) e).toKraus.apply
          ((FirstRegister.channel (signalSpace (selectedCount M)) (auxiliary M e)).toKraus.apply τ)) hc).trans
    (FirstRegister.discard_local_record (signalSpace (selectedCount M)) (signalSpace (remainderCount M)) e U hU _)
  exact congrArg (fun τ => (classicalMap e g).toKraus.apply ((classicalMap e f).toKraus.apply τ)) h

def unmatchedGate {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis) :
    Operator (signalSpace (remainderCount M)) :=
  Op.tensor (blockGate (remainderCount M) (remainderBases M (BB84SiftingRandomness.bobBases θ M)))
    (blockGate (remainderCount M) (remainderBases M θ))

theorem unmatchedGate_isometry {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis) :
    (unmatchedGate M θ).conjTranspose * unmatchedGate M θ = 1 :=
  tensor_isometry _ _ (blockGate_isometry _ _) (blockGate_isometry _ _)

/-- The concrete Bob/Alice basis gates at unmatched positions, not just a
postulated operation, can be omitted only after their signals are discarded. -/
theorem unmatched_basis_irrelevant {n : Nat} {e : Space} (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat)
    (ρ : Operator (.tensor (signalSpace (selectedCount M)) (auxiliary M e))) :
    (referenceOutput M θ e S minKey tolerance).toKraus.apply
      ((Kraus.single (Op.tensor (Op.ident (signalSpace (selectedCount M)))
        (Op.tensor (unmatchedGate M θ) (Op.ident e)))).apply ρ) =
    (referenceOutput M θ e S minKey tolerance).toKraus.apply ρ :=
  unmatched_irrelevant M θ S minKey tolerance _ (unmatchedGate_isometry M θ) ρ

theorem public_finished_interpreted {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) :
    (BB84DeferredRaw.publicChannel n e).toKraus.apply
      ((delayedOutput M θ e S minKey tolerance).toKraus.apply (input A M).matrix) =
    (BB84DeferredRaw.publicChannel n e).toKraus.apply
      ((referenceOutput M θ e S minKey tolerance).toKraus.apply (input A M).matrix) :=
  congrArg (BB84DeferredRaw.publicChannel n e).toKraus.apply
    (finished_interpreted A M θ S minKey tolerance)

end
end Foundation.Quantum.QKD.BB84SiftedInput
