import Foundation.Examples.UniformAdversary
import Foundation.Resource.Measure

namespace Foundation.Examples.UniformPolynomialAdversary

open Foundation.Examples.UniformAdversary
  (goal family model constantZero_not_realizable uniform_secure)

universe u v

example {P : CryptoGoal.{u}} (C D : AdversaryClass P)
    (F : InstanceFamily P) (A : AdversaryFamily P F) :
    (C.inter D).admissible F A ↔
      C.admissible F A ∧ D.admissible F A := by
  rfl

example {P : CryptoGoal.{u}} (C : AdversaryClass P)
    (F : InstanceFamily P) (A : AdversaryFamily P F) :
    (C.inter (AdversaryClass.all P)).admissible F A ↔ C.admissible F A := by
  simp [AdversaryClass.inter, AdversaryClass.all]

example {P : CryptoGoal.{u}} (M : UniformAdversaryModel.{u, v} P)
    (R : ResourceMeasure P) (F : InstanceFamily P)
    (A : AdversaryFamily P F) :
    (M.uniformClass.inter R.polynomialClass).admissible F A ↔
      M.Realizable F A ∧ PolynomiallyBounded (R.profile F A) := by
  rfl

/-- A synthetic resource observation on the goal used by the uniformity
example. It does not measure program execution. -/
def quadraticMeasure : ResourceMeasure goal where
  profile := fun _ _ n => n * n + 3 * n + 7

private theorem quadratic_polynomiallyBounded (F : InstanceFamily goal)
    (A : AdversaryFamily goal F) :
    PolynomiallyBounded (quadraticMeasure.profile F A) := by
  exact PolynomiallyBounded.add
    (PolynomiallyBounded.add
      (PolynomiallyBounded.mul PolynomiallyBounded.id PolynomiallyBounded.id)
      (PolynomiallyBounded.mul (PolynomiallyBounded.const 3)
        PolynomiallyBounded.id))
    (PolynomiallyBounded.const 7)

/-- Realizability and polynomial resource growth are separate obligations. -/
example :
    (model.uniformClass.inter quadraticMeasure.polynomialClass).admissible
      family (model.realize family (3 : Nat)) := by
  have hUniform : model.Realizable family (model.realize family (3 : Nat)) :=
    ⟨(3 : Nat), rfl⟩
  have hPoly : PolynomiallyBounded
      (quadraticMeasure.profile family (model.realize family (3 : Nat))) :=
    quadratic_polynomiallyBounded family _
  exact ⟨hUniform, hPoly⟩

example :
    ¬ (model.uniformClass.inter quadraticMeasure.polynomialClass).admissible
      family (fun _ => (0 : Nat)) := by
  intro h
  exact constantZero_not_realizable h.1

/-- Security for families satisfying both conditions follows by narrowing
the existing uniform-realizability security statement. -/
example : SecureOnWithin goal
    (model.uniformClass.inter quadraticMeasure.polynomialClass) family := by
  apply SecureOnWithin.monoClass
    (C := model.uniformClass)
    (D := model.uniformClass.inter quadraticMeasure.polynomialClass)
    (F := family) ?_ uniform_secure
  intro F A hA
  exact hA.1

example {P : CryptoGoal.{u}} (C D : AdversaryClass P)
    (F : InstanceFamily P) (h : SecureOnWithin P D F) :
    SecureOnWithin P (C.inter D) F := by
  apply SecureOnWithin.monoClass
    (C := D) (D := C.inter D) (F := F) ?_ h
  intro G A hA
  exact hA.2

end Foundation.Examples.UniformPolynomialAdversary
