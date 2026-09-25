import Mathlib.Data.ENNReal.Basic

open scoped ENNReal

universe u

/-- A security goal with an advantage for each adversary and instance. -/
structure CryptoGoal where
  Instance : Nat → Type u
  Adversary : (n : Nat) → Instance n → Type u
  advantage : (n : Nat) → (I : Instance n) → Adversary n I → ℝ≥0∞

namespace CryptoGoal

/-- Evaluate `P` on a new instance domain `X` by mapping each instance into
`P.Instance`. The adversary and advantage are those of `P` at the mapped
instance. -/
def reindex (P : CryptoGoal.{u}) (X : Nat → Type u)
    (f : ∀ n, X n → P.Instance n) : CryptoGoal.{u} where
  Instance := X
  Adversary := fun n x => P.Adversary n (f n x)
  advantage := fun n x A => P.advantage n (f n x) A

theorem reindex_id (P : CryptoGoal.{u}) :
    P.reindex P.Instance (fun _ I => I) = P := by
  cases P
  rfl

end CryptoGoal

/-- One chosen instance of `P` at each security parameter. -/
abbrev InstanceFamily (P : CryptoGoal.{u}) : Type u :=
  (n : Nat) → P.Instance n
