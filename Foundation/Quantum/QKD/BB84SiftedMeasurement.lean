import Foundation.Quantum.QKD.BB84SiftedDiscard
import Foundation.Quantum.FirstRegisterTransport

/-! Full measurement and matched-signal measurement give the same retained
record after the unmatched signals are discarded. All identities hold on
arbitrary joint operators, including cross-position and Eve coherences. -/
namespace Foundation.Quantum.QKD.BB84SiftedInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

def signalEquiv {n : Nat} (M : Finset (Fin n)) :
    (signalSpace n).Basis ≃
      (Space.tensor (signalSpace (selectedCount M)) (signalSpace (remainderCount M))).Basis where
  toFun p := (((splitEquiv M p.1).1,(splitEquiv M p.2).1),
    ((splitEquiv M p.1).2,(splitEquiv M p.2).2))
  invFun p := ((splitEquiv M).symm (p.1.1,p.2.1),
    (splitEquiv M).symm (p.1.2,p.2.2))
  left_inv p := by
    rcases p with ⟨b,a⟩
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv p := by
    rcases p with ⟨⟨b,a⟩,r,s⟩
    simp only [Equiv.apply_symm_apply]

def selectedLabel {n : Nat} (M : Finset (Fin n)) :
    Fin (Fintype.card (signalSpace n).Basis) →
      Fin (Fintype.card (signalSpace (selectedCount M)).Basis) :=
  fun r => Fintype.equivFin (signalSpace (selectedCount M)).Basis
    ((signalEquiv M ((Fintype.equivFin (signalSpace n).Basis).symm r)).1)

/-- Quantum reindexing factors as signal reindexing and reassociation;
this is an equality of applied channels, not of Kraus representations. -/
theorem signal_associate {n : Nat} (M : Finset (Fin n)) (e : Space)
    (ρ : Operator (.tensor (signalSpace n) e)) :
    (BasisChannel.channel (FirstRegister.associate (signalSpace (selectedCount M))
      (signalSpace (remainderCount M)) e)).toKraus.apply
      (((BasisChannel.channel (signalEquiv M)).amplify e).toKraus.apply ρ) =
      (BasisChannel.channel (jointEquiv M e)).toKraus.apply ρ := by
  rw [BasisChannel.apply, BasisChannel.amplify_apply, BasisChannel.apply]
  rfl

/-- Measuring all original signals and forgetting unmatched outcomes equals
measuring only matched signals and physically discarding the unmatched ones. -/
theorem selected_record {n : Nat} (M : Finset (Fin n)) (e : Space)
    (ρ : Operator (.tensor (signalSpace n) e)) :
    (discardMiddle (.register (Fintype.card (signalSpace (selectedCount M)).Basis))
      (signalSpace (remainderCount M)) e).toKraus.apply
        ((FirstRegister.channel (signalSpace (selectedCount M)) (auxiliary M e)).toKraus.apply
          ((BasisChannel.channel (jointEquiv M e)).toKraus.apply ρ)) =
      (classicalMap e (selectedLabel M)).toKraus.apply
        ((FirstRegister.channel (signalSpace n) e).toKraus.apply ρ) := by
  have h := FirstRegister.selectedDiscard_full (signalSpace (selectedCount M))
    (signalSpace (remainderCount M)) e
      (((BasisChannel.channel (signalEquiv M)).amplify e).toKraus.apply ρ)
  simp only [FirstRegister.selectedDiscard, Channel.seq, Kraus.seq_apply] at h
  rw [signal_associate M e ρ] at h
  have ht := FirstRegister.transport (signalSpace n)
    (.tensor (signalSpace (selectedCount M)) (signalSpace (remainderCount M))) e (signalEquiv M) ρ
  rw [ht, classicalMap_compose] at h
  refine h.trans ?_
  apply congrArg (fun f : Fin (Fintype.card (signalSpace n).Basis) →
      Fin (Fintype.card (signalSpace (selectedCount M)).Basis) =>
    (classicalMap e f).toKraus.apply ((FirstRegister.channel (signalSpace n) e).toKraus.apply ρ))
  funext r
  exact congrArg (fun p : (Space.tensor (signalSpace (selectedCount M))
      (signalSpace (remainderCount M))).Basis =>
    Fintype.equivFin (signalSpace (selectedCount M)).Basis p.1)
      ((Fintype.equivFin (Space.tensor (signalSpace (selectedCount M))
        (signalSpace (remainderCount M))).Basis).symm_apply_apply _)

end
end Foundation.Quantum.QKD.BB84SiftedInput
