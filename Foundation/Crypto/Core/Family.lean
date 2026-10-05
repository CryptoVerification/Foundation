import Foundation.Crypto.Core.Goal

open scoped ENNReal

universe u

/-- One chosen instance of `P` at each security parameter. -/
abbrev InstanceFamily (P : CryptoGoal.{u}) : Type u :=
  (n : Nat) → P.Instance n

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

