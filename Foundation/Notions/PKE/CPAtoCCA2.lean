import Foundation.Core.SecurityBound
import Foundation.Relation.ReducesTo
import Foundation.Notions.PKE.INDCPA
import Foundation.Notions.PKE.INDCCA2

open scoped ENNReal

namespace INDCPAAdversary

/-- View a CPA adversary as a CCA2 adversary that ignores both decryption capabilities. -/
def toCCA2 {M : Type → Type} {scheme : PKE M}
    (A : INDCPAAdversary M scheme) : INDCCA2Adversary M scheme where
  State := A.State
  choose := fun _dec pk => A.choose pk
  guess := fun _dec state challenge => A.guess state challenge

end INDCPAAdversary

/-- The two semantics give equal advantage to an embedded CPA adversary.

When both semantics model the same underlying challenge experiment, ignoring
decryption capabilities leaves its advantage unchanged. This law relates these
two semantics only; it does not establish either one's general correctness. -/
structure INDCPACCA2Compatibility (M : Type → Type)
    (Scpa : INDCPASemantics M) (Scca2 : INDCCA2Semantics M) : Prop where
  advantage_eq : ∀ (n : Nat) (scheme : PKE M) (A : INDCPAAdversary M scheme),
    Scpa.advantage n scheme A = Scca2.advantage n scheme A.toCCA2

/-- A CPA adversary reduces to a CCA2 adversary with no advantage loss.
Security bounds therefore pass from IND-CCA2 to IND-CPA. -/
def indCPA_to_indCCA2_reduction (M : Type → Type)
    (Scpa : INDCPASemantics M) (Scca2 : INDCCA2Semantics M)
    (h : INDCPACCA2Compatibility M Scpa Scca2) :
    Reduction (INDCPA M Scpa) (INDCCA2 M Scca2) where
  mapInstance := fun scheme => scheme
  reduce := fun _ A => A.toCCA2
  loss := AdvantageBound.id
  advantage_le := by
    intro n scheme A
    change Scpa.advantage n scheme A ≤ Scca2.advantage n scheme A.toCCA2
    exact le_of_eq (h.advantage_eq n scheme A)

theorem indCPA_reducesTo_indCCA2 (M : Type → Type)
    (Scpa : INDCPASemantics M) (Scca2 : INDCCA2Semantics M)
    (h : INDCPACCA2Compatibility M Scpa Scca2) :
    ReducesTo (INDCPA M Scpa) (INDCCA2 M Scca2) :=
  ⟨indCPA_to_indCCA2_reduction M Scpa Scca2 h⟩

theorem indCPA_to_indCCA2_mapFamily_eq (M : Type → Type)
    (Scpa : INDCPASemantics M) (Scca2 : INDCCA2Semantics M)
    (h : INDCPACCA2Compatibility M Scpa Scca2)
    (F : InstanceFamily (INDCPA M Scpa)) :
    (indCPA_to_indCCA2_reduction M Scpa Scca2 h).mapFamily F = F := by
  rfl
