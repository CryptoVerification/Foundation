import Foundation.Core.SecurityBound
import Foundation.Assumptions.DDH.DDH

open scoped ENNReal

namespace Foundation.Assumptions.DDH.Examples

/-- A deterministic effect for checking the DDH interfaces. -/
def Plain (α : Type) : Type := α

/-- These operations are only dummy syntax; no group law is claimed. -/
def dummyParameters : DDHParameters where
  Element := Bool
  Scalar := Bool
  generator := true
  power := fun element scalar => element && scalar
  mulScalar := fun a b => a && b
  mul := fun a b => a && b

def dummySemantics : DDHSemantics Plain where
  advantage := fun _ _ _ => 0

def dummyGoal : CryptoGoal := DDH Plain dummySemantics

def dummyFamily : InstanceFamily (DDH Plain dummySemantics) :=
  fun _ => dummyParameters

/-- The syntax can form the real challenge from two sampled scalars. -/
example (a b : dummyParameters.Scalar) :
    dummyParameters.Element × dummyParameters.Element × dummyParameters.Element :=
  (dummyParameters.power dummyParameters.generator a,
   dummyParameters.power dummyParameters.generator b,
   dummyParameters.power dummyParameters.generator
     (dummyParameters.mulScalar a b))

def dummyAdversary (n : Nat) : dummyGoal.Adversary n (dummyFamily n) where
  distinguish := fun x y z => x && y && z

theorem dummyFamilyBound :
    BoundedByOn (DDH Plain dummySemantics) dummyFamily (fun _ => 0) := by
  intro n A
  exact le_refl _

example (n : Nat) :
    dummyGoal.advantage n (dummyFamily n) (dummyAdversary n) = 0 := by
  rfl

end Foundation.Assumptions.DDH.Examples
