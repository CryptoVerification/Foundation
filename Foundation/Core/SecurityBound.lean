import Foundation.Core.Reduction

open scoped ENNReal

universe u v

/-- A concrete advantage bound uniform over all instances and adversaries. -/
def BoundedBy (P : CryptoGoal.{u}) (ε : Nat → ℝ≥0∞) : Prop :=
  ∀ (n : Nat) (I : P.Instance n) (A : P.Adversary n I),
    P.advantage n I A ≤ ε n

/-- A concrete advantage bound for one chosen instance family. -/
def BoundedByOn (P : CryptoGoal.{u}) (F : InstanceFamily P)
    (ε : Nat → ℝ≥0∞) : Prop :=
  ∀ (n : Nat) (A : P.Adversary n (F n)),
    P.advantage n (F n) A ≤ ε n

namespace CryptoGoal

/-- A family bound after reindexing is the original goal's bound on the
pointwise mapped family. -/
theorem boundedByOn_reindex_iff (P : CryptoGoal.{u}) (X : Nat → Type u)
    (f : ∀ n, X n → P.Instance n)
    (F : InstanceFamily (P.reindex X f)) (ε : Nat → ℝ≥0∞) :
    BoundedByOn (P.reindex X f) F ε ↔
      BoundedByOn P (fun n => f n (F n)) ε := by
  rfl

end CryptoGoal

namespace BoundedBy

theorem on {P : CryptoGoal.{u}} {ε : Nat → ℝ≥0∞}
    (h : BoundedBy P ε) (F : InstanceFamily P) : BoundedByOn P F ε := by
  intro n A
  exact h n (F n) A

end BoundedBy

namespace Reduction

/-- A bound for the target goal induces a bound for the source goal. -/
theorem boundedBy {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (R : Reduction P Q) {ε : Nat → ℝ≥0∞} (hQ : BoundedBy Q ε) :
    BoundedBy P (fun n => R.loss.eval n (ε n)) := by
  intro n I A
  calc
    P.advantage n I A
        ≤ R.loss.eval n (Q.advantage n (R.mapInstance I) (R.reduce I A)) :=
          R.advantage_le I A
    _ ≤ R.loss.eval n (ε n) :=
          R.loss.monotone n (hQ n (R.mapInstance I) (R.reduce I A))

/-- A bound on the mapped target family induces a bound on the source family. -/
theorem boundedByOn {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (R : Reduction P Q) (F : InstanceFamily P) {ε : Nat → ℝ≥0∞}
    (hQ : BoundedByOn Q (R.mapFamily F) ε) :
    BoundedByOn P F (fun n => R.loss.eval n (ε n)) := by
  intro n A
  calc
    P.advantage n (F n) A
        ≤ R.loss.eval n
            (Q.advantage n (R.mapInstance (F n)) (R.reduce (F n) A)) :=
          R.advantage_le (F n) A
    _ ≤ R.loss.eval n (ε n) :=
          R.loss.monotone n (hQ n (R.reduce (F n) A))

end Reduction
