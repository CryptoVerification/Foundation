import Foundation.Core.SecurityBound
import Foundation.Relation.ReducesTo
import Foundation.Notions.Signature.EUFCMA
import Foundation.Notions.Signature.StrongEUFCMA

open scoped ENNReal

/-- EUF success is contained in strong-EUF success for the same scheme and adversary.

Because the experiments are abstract, this relation supplies the resulting
advantage inequality externally. It does not prove event inclusion or the
correctness of either semantics. -/
structure EUFStrongCompatibility (M : Type → Type)
    (Seuf : EUFCMASemantics M) (Sstrong : StrongEUFCMASemantics M) : Prop where
  advantage_le : ∀ (n : Nat) (scheme : SignatureScheme M)
    (A : EUFCMAAdversary M scheme),
    Seuf.advantage n scheme A ≤ Sstrong.advantage n scheme A

/-- Identity mappings give a tight reduction from EUF-CMA to strong EUF-CMA.
Thus strong-EUF security implies EUF security. -/
def eufCMA_to_strongEUFCMA_reduction (M : Type → Type)
    (Seuf : EUFCMASemantics M) (Sstrong : StrongEUFCMASemantics M)
    (h : EUFStrongCompatibility M Seuf Sstrong) :
    Reduction (EUFCMA M Seuf) (StrongEUFCMA M Sstrong) where
  mapInstance := fun scheme => scheme
  reduce := fun _ A => A
  loss := AdvantageBound.id
  advantage_le := by
    intro n scheme A
    change Seuf.advantage n scheme A ≤ Sstrong.advantage n scheme A
    exact h.advantage_le n scheme A

theorem eufCMA_reducesTo_strongEUFCMA (M : Type → Type)
    (Seuf : EUFCMASemantics M) (Sstrong : StrongEUFCMASemantics M)
    (h : EUFStrongCompatibility M Seuf Sstrong) :
    ReducesTo (EUFCMA M Seuf) (StrongEUFCMA M Sstrong) :=
  ⟨eufCMA_to_strongEUFCMA_reduction M Seuf Sstrong h⟩

theorem eufCMA_to_strongEUFCMA_mapFamily_eq (M : Type → Type)
    (Seuf : EUFCMASemantics M) (Sstrong : StrongEUFCMASemantics M)
    (h : EUFStrongCompatibility M Seuf Sstrong)
    (F : InstanceFamily (EUFCMA M Seuf)) :
    (eufCMA_to_strongEUFCMA_reduction M Seuf Sstrong h).mapFamily F = F := by
  rfl
