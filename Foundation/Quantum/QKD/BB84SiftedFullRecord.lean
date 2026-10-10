import Foundation.Quantum.QKD.BB84SiftedMeasurement
import Foundation.Quantum.QKD.BB84MixedPreparedRaw

/-! Restore full raw records from the selected measurement. Unmatched
measurement outcomes carry no raw key and are forgotten by physical channels. -/
namespace Foundation.Quantum.QKD.BB84SiftedInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

def restoredLabel {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat)
    (r : Fin (Fintype.card (signalSpace (selectedCount M)).Basis)) :
    Fin (Fintype.card (RawProtocol.Output n)) :=
  Fintype.equivFin (RawProtocol.Output n)
    (restoreOutput M θ ((Fintype.equivFin (RawProtocol.Output (selectedCount M))).symm
      (BB84DeferredRaw.rawLabel (bases M θ) S minKey tolerance
        ((Fintype.equivFin (signalSpace (selectedCount M)).Basis).symm r))))

theorem restored_label {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) (p : (signalSpace n).Basis) :
    restoredLabel M θ S minKey tolerance
      (selectedLabel M (Fintype.equivFin (signalSpace n).Basis p)) =
      BB84MixedPreparedRaw.label θ (BB84SiftingRandomness.bobBases θ M)
        (liftTest M S) minKey tolerance p := by
  have h := congrArg (Fintype.equivFin (RawProtocol.Output n))
    (restore_output M (liftTest M S) (lift_subset M S) θ (readBits p.2) (readBits p.1)
      minKey tolerance)
  simp only [restoredLabel, selectedLabel, Equiv.symm_apply_apply,
    BB84DeferredRaw.rawLabel, BB84MixedPreparedRaw.label]
  change Fintype.equivFin (RawProtocol.Output n)
    (restoreOutput M θ (RawProtocol.output (bases M θ) (bases M θ)
      (readBits (split M p.2).1) (readBits (split M p.1).1) S minKey tolerance)) = _
  have hb (x : (qubits n).Basis) : readBits (split M x).1 = bits M (readBits x) := by
    exact read_write _ _
  rw [hb, hb]
  simpa only [restrict_lift] using h

/-- Full original measurement and selected measurement have exactly the same
restored raw output after unmatched quantum signals are discarded. -/
theorem restored_measurement {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) (e : Space)
    (ρ : Operator (.tensor (signalSpace n) e)) :
    (classicalMap e (restoredLabel M θ S minKey tolerance)).toKraus.apply
      ((discardMiddle (.register (Fintype.card (signalSpace (selectedCount M)).Basis))
        (signalSpace (remainderCount M)) e).toKraus.apply
          ((FirstRegister.channel (signalSpace (selectedCount M)) (auxiliary M e)).toKraus.apply
            ((BasisChannel.channel (jointEquiv M e)).toKraus.apply ρ))) =
      (classicalMap e (fun r => BB84MixedPreparedRaw.label θ
        (BB84SiftingRandomness.bobBases θ M) (liftTest M S) minKey tolerance
          ((Fintype.equivFin (signalSpace n).Basis).symm r))).toKraus.apply
            ((FirstRegister.channel (signalSpace n) e).toKraus.apply ρ) := by
  rw [selected_record, classicalMap_compose]
  apply congrArg (fun f => (classicalMap e f).toKraus.apply
    ((FirstRegister.channel (signalSpace n) e).toKraus.apply ρ))
  funext r
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    restored_label M θ S minKey tolerance ((Fintype.equivFin (signalSpace n).Basis).symm r)

/-- The actual separated gate is the common matched gate together with the
actual, different unmatched Bob/Alice gates. -/
theorem selected_basis_factor {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (e : Space) (ρ : Operator (.tensor (signalSpace (selectedCount M)) (auxiliary M e))) :
    (selectedChannel M (BB84SiftingRandomness.bobBases θ M) θ e).toKraus.apply ρ =
      (((BB84ErrorTransform.basisChannel (selectedCount M) (bases M θ)).amplify (auxiliary M e)).toKraus.apply
        ((Kraus.single (Op.tensor (Op.ident (signalSpace (selectedCount M)))
          (Op.tensor (unmatchedGate M θ) (Op.ident e)))).apply ρ)) := by
  change (Kraus.single (selectedGate M (BB84SiftingRandomness.bobBases θ M) θ e)).apply ρ =
    (Kraus.single (Op.tensor (BB84ErrorTransform.basisGate (selectedCount M) (bases M θ))
      (Op.ident (auxiliary M e)))).apply
        ((Kraus.single (Op.tensor (Op.ident (signalSpace (selectedCount M)))
          (Op.tensor (unmatchedGate M θ) (Op.ident e)))).apply ρ)
  have hm : Op.tensor (BB84ErrorTransform.basisGate (selectedCount M) (bases M θ))
      (Op.ident (auxiliary M e)) *
        Op.tensor (Op.ident (signalSpace (selectedCount M))) (Op.tensor (unmatchedGate M θ) (Op.ident e)) =
      selectedGate M (BB84SiftingRandomness.bobBases θ M) θ e := by
    rw [Op.tensor_local_right]
    simp only [selectedGate, common_bases, BB84ErrorTransform.basisGate, unmatchedGate]
  rw [← hm]
  simp only [Kraus.single_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Push physical discard through the real two-stage classical restoration. -/
theorem reference_output_post {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) (e : Space)
    (ρ : Operator (.tensor (signalSpace (selectedCount M)) (auxiliary M e))) :
    (referenceOutput M θ e S minKey tolerance).toKraus.apply ρ =
      (classicalMap e (restoredLabel M θ S minKey tolerance)).toKraus.apply
        ((discardMiddle (.register (Fintype.card (signalSpace (selectedCount M)).Basis))
          (signalSpace (remainderCount M)) e).toKraus.apply
            ((FirstRegister.channel (signalSpace (selectedCount M)) (auxiliary M e)).toKraus.apply
              (((BB84ErrorTransform.basisChannel (selectedCount M) (bases M θ)).amplify (auxiliary M e)).toKraus.apply ρ))) := by
  simp only [referenceOutput, finish, BB84DeferredRaw.reference, restoreChannel,
    Channel.seq, Kraus.seq_apply]
  rw [classicalMap_discardMiddle, classicalMap_discardMiddle, classicalMap_compose]
  rfl

/-- The selected experiment, including unmatched discard, equals the full
independent-basis experiment for every joint input operator. -/
theorem full_reference {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) (e : Space)
    (ρ : Operator (.tensor (signalSpace n) e)) :
    (referenceOutput M θ e S minKey tolerance).toKraus.apply
      ((BasisChannel.channel (jointEquiv M e)).toKraus.apply ρ) =
      (BB84MixedPreparedRaw.reference θ (BB84SiftingRandomness.bobBases θ M) e
        (liftTest M S) minKey tolerance).toKraus.apply ρ := by
  have h := restored_measurement M θ S minKey tolerance e
    ((fullChannel (BB84SiftingRandomness.bobBases θ M) θ e).toKraus.apply ρ)
  rw [gate_apply, selected_basis_factor, ← reference_output_post, unmatched_basis_irrelevant] at h
  simpa only [BB84MixedPreparedRaw.reference, Channel.seq, Kraus.seq_apply] using h

/-- The actual attacked, selected source interpreted by the closed error-first
derivation produces the original uniform prepare/attack raw experiment. -/
theorem delayed_prepared {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) :
    (delayedOutput M θ e S minKey tolerance).toKraus.apply (input A M).matrix =
      (BB84MixedPreparedRaw.prepared A θ (BB84SiftingRandomness.bobBases θ M)
        (liftTest M S) minKey tolerance).matrix :=
  (finished_interpreted A M θ S minKey tolerance).trans
    ((full_reference M θ S minKey tolerance e (BB84PreparedInput.input A).matrix).trans
      (BB84MixedPreparedRaw.reference_prepared A θ (BB84SiftingRandomness.bobBases θ M)
        (liftTest M S) minKey tolerance))

/-- Connect the two existing closed derivations through the actual source,
restoring all original raw labels and retaining only the original Eve system. -/
theorem delayed_source {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (S : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) :
    (delayedOutput M θ e S minKey tolerance).toKraus.apply (input A M).matrix =
      ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
        (BB84RawSource.state A θ (BB84SiftingRandomness.bobBases θ M)
          (liftTest M S) minKey tolerance)).matrix :=
  (finished_interpreted A M θ S minKey tolerance).trans
    ((full_reference M θ S minKey tolerance e (BB84PreparedInput.input A).matrix).trans
      (BB84MixedPreparedRaw.source_interpreted A θ (BB84SiftingRandomness.bobBases θ M)
        (liftTest M S) minKey tolerance).symm)

end
end Foundation.Quantum.QKD.BB84SiftedInput
