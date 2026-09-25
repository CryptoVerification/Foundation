import Foundation.Constructions.ElGamal.ToDDHReduction
import Foundation.Constructions.ElGamal.Examples

open scoped ENNReal

namespace Foundation.Constructions.ElGamal.Relations

open Foundation.Constructions.ElGamal.Examples (dummyInstance)

def chooseBit : Id Bool := pure true

def Sind : INDCPASemantics Id :=
  Foundation.Constructions.ElGamal.Examples.dummySemantics

def Sddh : DDHSemantics Id :=
  Foundation.Assumptions.DDH.Examples.dummySemantics

/-- A dummy API check, not a proof of standard ElGamal security from DDH. -/
theorem dummyCompatibility :
    ElGamalDDHCompatibility Id chooseBit Sind Sddh := by
  constructor
  intro n I A
  exact le_refl _

def R : Reduction (ElGamalINDCPA Id Sind) (DDH Id Sddh) :=
  elGamalINDCPA_to_DDH_reduction Id chooseBit Sind Sddh dummyCompatibility

theorem reducesTo : ReducesTo (ElGamalINDCPA Id Sind) (DDH Id Sddh) :=
  elGamalINDCPA_reducesTo_DDH Id chooseBit Sind Sddh dummyCompatibility

def Ifam : InstanceFamily (ElGamalINDCPA Id Sind) :=
  fun _ => dummyInstance

example : R.mapFamily Ifam = (fun n => (Ifam n).params) := by
  rfl

example : R.mapFamily Ifam =
    Foundation.Constructions.ElGamal.Examples.ddhFamily := by
  rfl

theorem boundOnElGamal (ε : Nat → ℝ≥0∞)
    (hDDH : BoundedByOn (DDH Id Sddh) (R.mapFamily Ifam) ε) :
    BoundedByOn (ElGamalINDCPA Id Sind) Ifam ε := by
  exact R.boundedByOn Ifam hDDH

theorem boundOnPKEFamily (ε : Nat → ℝ≥0∞)
    (hDDH : BoundedByOn (DDH Id Sddh) (R.mapFamily Ifam) ε) :
    BoundedByOn (INDCPA Id Sind) (fun n => (Ifam n).scheme) ε := by
  exact (elGamalINDCPA_boundedByOn_iff Id Sind Ifam ε).mp
    (boundOnElGamal ε hDDH)

example : BoundedByOn (INDCPA Id Sind)
    (fun n => (Ifam n).scheme) (fun _ => 0) := by
  apply boundOnPKEFamily
  exact Foundation.Assumptions.DDH.Examples.dummyFamilyBound

end Foundation.Constructions.ElGamal.Relations
