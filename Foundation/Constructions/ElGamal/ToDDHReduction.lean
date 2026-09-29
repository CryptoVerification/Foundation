import Foundation.Constructions.ElGamal.INDCPA
import Foundation.Constructions.ElGamal.ToDDH
import Foundation.Relation.ReducesTo

open scoped ENNReal

/-- The ElGamal IND-CPA experiment on `I.scheme` is bounded by the DDH
experiment on the underlying `I.params` after simulating its adversary.

This relates two abstract semantics and the chosen reduction randomness. A
concrete backend must justify the bit distribution, ElGamal construction,
DDH challenge distributions, and advantage normalization. No group or
probability laws are proved by this structure. -/
structure ElGamalDDHCompatibility (M : Type → Type) [Monad M]
    (chooseBit : M Bool) (Sind : INDCPASemantics M)
    (Sddh : DDHSemantics M) : Prop where
  advantage_le : ∀ (n : Nat) (I : ElGamalInstance M)
    (A : INDCPAAdversary M I.scheme),
    Sind.advantage n I.scheme A ≤
      Sddh.advantage n I.params
        (ddhAdversaryOfINDCPA chooseBit I A)

/-- The simulator and identity loss, shared by the unrestricted abstract
reduction and reductions restricted to concrete ElGamal instances. The input
domain `X` only selects which instances carry a proved advantage relation. -/
def elGamalINDCPA_to_DDH_reductionOn (M : Type → Type) [Monad M]
    (chooseBit : M Bool) (Sind : INDCPASemantics M)
    (Sddh : DDHSemantics M)
    (X : Nat → Type 1) (embed : ∀ n, X n → ElGamalInstance M)
    (h : ∀ (n : Nat) (I : X n)
      (A : INDCPAAdversary M (embed n I).scheme),
      Sind.advantage n (embed n I).scheme A ≤
        Sddh.advantage n (embed n I).params
          (ddhAdversaryOfINDCPA chooseBit (embed n I) A)) :
    Reduction
      ((INDCPA M Sind).reindex X (fun n I => (embed n I).scheme))
      (DDH M Sddh) where
  mapInstance := fun I => (embed _ I).params
  reduce := fun I A => ddhAdversaryOfINDCPA chooseBit (embed _ I) A
  loss := AdvantageBound.id
  advantage_le := by
    intro n I A
    exact h n I A

/-- Nonidentity instance mapping and cryptographic adversary simulation give
a tight reduction once their advantage relation is supplied externally.
DDH security bounds therefore transfer to ElGamal IND-CPA. -/
def elGamalINDCPA_to_DDH_reduction (M : Type → Type) [Monad M]
    (chooseBit : M Bool) (Sind : INDCPASemantics M)
    (Sddh : DDHSemantics M)
    (h : ElGamalDDHCompatibility M chooseBit Sind Sddh) :
    Reduction (ElGamalINDCPA M Sind) (DDH M Sddh) :=
  elGamalINDCPA_to_DDH_reductionOn M chooseBit Sind Sddh
    (fun _ => ElGamalInstance M) (fun _ I => I) h.advantage_le

theorem elGamalINDCPA_reducesTo_DDH (M : Type → Type) [Monad M]
    (chooseBit : M Bool) (Sind : INDCPASemantics M)
    (Sddh : DDHSemantics M)
    (h : ElGamalDDHCompatibility M chooseBit Sind Sddh) :
    ReducesTo (ElGamalINDCPA M Sind) (DDH M Sddh) :=
  ⟨elGamalINDCPA_to_DDH_reduction M chooseBit Sind Sddh h⟩

theorem elGamalINDCPA_to_DDH_mapFamily_eq (M : Type → Type) [Monad M]
    (chooseBit : M Bool) (Sind : INDCPASemantics M)
    (Sddh : DDHSemantics M)
    (h : ElGamalDDHCompatibility M chooseBit Sind Sddh)
    (F : InstanceFamily (ElGamalINDCPA M Sind)) :
    (elGamalINDCPA_to_DDH_reduction M chooseBit Sind Sddh h).mapFamily F =
      (fun n => (F n).params) := by
  rfl
