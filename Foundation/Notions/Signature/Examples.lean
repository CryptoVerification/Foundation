import Foundation.Core.SecurityBound
import Foundation.Notions.Signature.EUFCMA

open scoped ENNReal

namespace Foundation.Notions.Signature.Examples

/-- The identity effect is sufficient for this type-level example. -/
def Plain (α : Type) : Type := α

def dummyScheme : SignatureScheme Plain where
  PublicKey := Unit
  SecretKey := Unit
  Message := Bool
  Signature := Bool
  keygen := ((), ())
  sign := fun _ message => message
  verify := fun _ message signature => message == signature

def dummySemantics : EUFCMASemantics Plain where
  advantage := fun _ _ _ => 0

def dummyGoal : CryptoGoal := EUFCMA Plain dummySemantics

def dummyFamily : InstanceFamily (EUFCMA Plain dummySemantics) :=
  fun _ => dummyScheme

/-- This adversary uses signing access and outputs a forgery candidate. -/
def dummyAdversary (n : Nat) : dummyGoal.Adversary n (dummyFamily n) where
  forge := fun sign _ => (true, sign false)

theorem dummyFamilyBound :
    BoundedByOn (EUFCMA Plain dummySemantics) dummyFamily (fun _ => 0) := by
  intro n A
  exact le_refl _

example (n : Nat) :
    dummyGoal.advantage n (dummyFamily n) (dummyAdversary n) = 0 := by
  rfl

end Foundation.Notions.Signature.Examples
