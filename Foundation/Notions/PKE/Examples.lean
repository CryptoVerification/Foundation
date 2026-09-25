import Foundation.Core.SecurityBound
import Foundation.Notions.PKE.INDCPA

open scoped ENNReal

namespace Foundation.Notions.PKE.Examples

/-- A deterministic effect used only to check the interface. -/
def Plain (α : Type) : Type := α

def dummyPKE : PKE Plain where
  PublicKey := Unit
  SecretKey := Unit
  Message := Bool
  Ciphertext := Bool
  keygen := ((), ())
  encrypt := fun _ m => m
  decrypt := fun _ c => some c

def dummySemantics : INDCPASemantics Plain where
  advantage := fun _ _ _ => 0

def dummyGoal : CryptoGoal := INDCPA Plain dummySemantics

/-- A scheme family selects a scheme value at each security parameter. -/
def dummyFamily : Nat → PKE Plain := fun _ => dummyPKE

def fixedSchemeFamily : InstanceFamily (INDCPA Plain dummySemantics) :=
  dummyFamily

theorem fixedSchemeBound :
    BoundedByOn (INDCPA Plain dummySemantics) fixedSchemeFamily (fun _ => 0) := by
  intro n A
  exact le_refl _

/-- The second stage reads the state returned by the first stage. -/
def dummyAdversary (n : Nat) : dummyGoal.Adversary n (dummyFamily n) where
  State := Bool
  choose := fun _ => (false, true, true)
  guess := fun state _ => state

example (n : Nat) :
    dummyGoal.advantage n (dummyFamily n) (dummyAdversary n) = 0 := by
  rfl

end Foundation.Notions.PKE.Examples
