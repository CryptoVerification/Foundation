import Foundation.Constructions.ElGamal.INDCPA
import Foundation.Assumptions.DDH.Examples
import Foundation.Notions.PKE.Examples

open scoped ENNReal

namespace Foundation.Constructions.ElGamal.Examples

open Foundation.Notions.PKE.Examples (Plain)

def dummyParams : DDHParameters :=
  Foundation.Assumptions.DDH.Examples.dummyParameters

/-- Dummy operations check the ElGamal type shape, not its arithmetic. -/
def dummyConstruction : ElGamalConstruction Plain dummyParams where
  keygen := (true, true)
  encrypt := fun publicKey message => (publicKey, message)
  decrypt := fun _ ciphertext => some ciphertext.2

def dummyInstance : ElGamalInstance Plain where
  params := dummyParams
  construction := dummyConstruction

def dummySemantics : INDCPASemantics Plain :=
  Foundation.Notions.PKE.Examples.dummySemantics

def dummyGoal : CryptoGoal := ElGamalINDCPA Plain dummySemantics

def dummyFamily : InstanceFamily (ElGamalINDCPA Plain dummySemantics) :=
  fun _ => dummyInstance

def pkeFamily : InstanceFamily (INDCPA Plain dummySemantics) :=
  fun n => (dummyFamily n).scheme

def ddhFamily : InstanceFamily
    (DDH Plain Foundation.Assumptions.DDH.Examples.dummySemantics) :=
  fun n => (dummyFamily n).params

def dummyAdversary (n : Nat) : dummyGoal.Adversary n (dummyFamily n) where
  State := Bool
  choose := fun _ => (false, true, false)
  guess := fun state _ => state

theorem dummyFamilyBound :
    BoundedByOn (ElGamalINDCPA Plain dummySemantics) dummyFamily (fun _ => 0) := by
  intro n A
  exact le_refl _

theorem boundCorrespondence (ε : Nat → ℝ≥0∞) :
    BoundedByOn (ElGamalINDCPA Plain dummySemantics) dummyFamily ε ↔
      BoundedByOn (INDCPA Plain dummySemantics) pkeFamily ε := by
  exact elGamalINDCPA_boundedByOn_iff Plain dummySemantics dummyFamily ε

example (n : Nat) (A : INDCPAAdversary Plain (dummyFamily n).scheme) :
    dummyGoal.advantage n (dummyFamily n) A =
      (INDCPA Plain dummySemantics).advantage n (pkeFamily n) A := by
  rfl

end Foundation.Constructions.ElGamal.Examples
