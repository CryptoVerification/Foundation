import Foundation.Resource.Adversary
import Foundation.Asymptotics.PolynomiallyBounded

universe u

/-- Observe one scalar resource of an entire adversary family on an instance
family. `profile F A n` is the resource usage at security parameter `n`.
The measure does not specify whether this is time, queries, memory, size, or
another resource, and imposes no correctness or growth condition. -/
structure ResourceMeasure (P : CryptoGoal.{u}) where
  profile : ∀ (F : InstanceFamily P), AdversaryFamily P F → Nat → Nat

namespace ResourceMeasure

/-- Admit exactly the adversary families whose measured resource profile is
eventually polynomially bounded in the security parameter. -/
def polynomialClass {P : CryptoGoal.{u}} (R : ResourceMeasure P) :
    AdversaryClass P where
  admissible := fun F A => PolynomiallyBounded (R.profile F A)

/-- A simple measure that reports no resource usage. -/
def zero (P : CryptoGoal.{u}) : ResourceMeasure P where
  profile := fun _ _ _ => 0

theorem zero_admissible (P : CryptoGoal.{u}) (F : InstanceFamily P)
    (A : AdversaryFamily P F) :
    ((zero P).polynomialClass).admissible F A :=
  PolynomiallyBounded.zero

end ResourceMeasure
