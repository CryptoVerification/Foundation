import Foundation.Core.SecurityBound

open scoped ENNReal

universe u

/-- One adversary at each security parameter, against the chosen instance
family `F`. -/
abbrev AdversaryFamily (P : CryptoGoal.{u}) (F : InstanceFamily P) : Type u :=
  (n : Nat) → P.Adversary n (F n)

/-- The asymptotic advantage function `n ↦ Adv_P(n, F n, A n)` of one
adversary family. -/
def advantageProfile (P : CryptoGoal.{u}) (F : InstanceFamily P)
    (A : AdversaryFamily P F) : Nat → ℝ≥0∞ :=
  fun n => P.advantage n (F n) (A n)

/-- An abstract admissibility condition on entire adversary families.
The computational model and resource condition are left unspecified. -/
structure AdversaryClass (P : CryptoGoal.{u}) where
  admissible : ∀ (F : InstanceFamily P), AdversaryFamily P F → Prop

namespace AdversaryClass

/-- A class that admits every adversary family. -/
def all (P : CryptoGoal.{u}) : AdversaryClass P where
  admissible := fun _ _ => True

/-- Admit exactly the adversary families satisfying both classes'
admissibility conditions. -/
def inter {P : CryptoGoal.{u}} (C D : AdversaryClass P) : AdversaryClass P where
  admissible := fun F A => C.admissible F A ∧ D.admissible F A

end AdversaryClass

/-- A concrete bound for every admissible adversary family on `F`.
The family is quantified before the security parameter. -/
def BoundedByOnWithin (P : CryptoGoal.{u}) (C : AdversaryClass P)
    (F : InstanceFamily P) (ε : Nat → ℝ≥0∞) : Prop :=
  ∀ (A : AdversaryFamily P F), C.admissible F A →
    ∀ n, advantageProfile P F A n ≤ ε n

namespace BoundedByOn

/-- A bound for each individual adversary also bounds every admissible
adversary family. -/
theorem within {P : CryptoGoal.{u}} {F : InstanceFamily P}
    {ε : Nat → ℝ≥0∞} (h : BoundedByOn P F ε)
    (C : AdversaryClass P) : BoundedByOnWithin P C F ε := by
  intro A _ n
  exact h n (A n)

end BoundedByOn

namespace BoundedByOnWithin

theorem mono {P : CryptoGoal.{u}} {C : AdversaryClass P}
    {F : InstanceFamily P} {ε δ : Nat → ℝ≥0∞}
    (h : BoundedByOnWithin P C F ε) (hεδ : ∀ n, ε n ≤ δ n) :
    BoundedByOnWithin P C F δ := by
  intro A hA n
  exact (h A hA n).trans (hεδ n)

end BoundedByOnWithin
