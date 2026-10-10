import Foundation.Quantum.QKD.AcceptedHashAbort
import Foundation.Quantum.QKD.PairwiseConditionalHashProcess

/-! Insufficient selected population forces the existing length guard to
abort. The original abort state is retained; only its accepted part is zero. -/
namespace Foundation.Quantum.QKD
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace RawProtocol

theorem too_short {n : Nat} (alice bob : Fin n → BB84Basis) (b c : Fin n → Fin 2)
    (T : Finset (Fin n)) (minKey tolerance : Nat) (h : n < minKey) :
    accepts alice bob b c T minKey tolerance = false := by
  have hc : (keyPositions alice bob T).card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (keyPositions alice bob T))
  simp only [accepts, decide_eq_false_iff_not]
  rintro ⟨_,hl,_⟩
  omega

end RawProtocol

namespace BB84SiftedInput
open Subnormalized

theorem reference_abort {n length : Nat} {e : Space} {S : Type} [Fintype S] [DecidableEq S]
    (M : Finset (Fin n)) (θ : Fin n → BB84Basis) (T : Finset (Fin (selectedCount M)))
    (minKey tolerance : Nat) (h : selectedCount M < minKey)
    (ρ : Density (.tensor (signalSpace (selectedCount M)) (auxiliary M e)))
    (p : PMF S) (hash : S → Finalization.RawKey n → IdealKey.Key length) :
    AcceptedHash.fromDensity ((referenceOutput M θ e T minKey tolerance).run ρ) p hash = zero := by
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
  rw [AcceptedHash.fromDensity_congr _ _ he]
  apply AcceptedHash.fromDensity_abort_map
  intro r
  simp only [out, f, BB84DeferredRaw.rawLabel, Equiv.symm_apply_apply, restoreOutput, RawProtocol.output]
  exact RawProtocol.too_short _ _ _ _ _ _ _ h

end BB84SiftedInput
end
end Foundation.Quantum.QKD
