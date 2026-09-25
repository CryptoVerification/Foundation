import Foundation.Core.Bound

open scoped ENNReal

universe u w t

/-- Turn a `P` adversary into a `Q` adversary with a quantitative advantage bound. -/
structure Reduction (P : CryptoGoal.{u}) (Q : CryptoGoal.{w}) where
  mapInstance : ∀ {n}, P.Instance n → Q.Instance n
  reduce : ∀ {n} (I : P.Instance n), P.Adversary n I → Q.Adversary n (mapInstance I)
  loss : AdvantageBound
  advantage_le : ∀ {n} (I : P.Instance n) (A : P.Adversary n I),
    P.advantage n I A ≤ loss.eval n (Q.advantage n (mapInstance I) (reduce I A))

namespace Reduction

/-- Identity transformation of instances, adversaries, and advantage. -/
def id (P : CryptoGoal.{u}) : Reduction P P where
  mapInstance := fun I => I
  reduce := fun _ A => A
  loss := AdvantageBound.id
  advantage_le := by
    intro _ _ _
    exact le_refl _

/-- Compose reductions from `P` to `Q` and from `Q` to `R`. -/
def comp {P : CryptoGoal.{u}} {Q : CryptoGoal.{w}}
    {R : CryptoGoal.{t}} (r₁ : Reduction P Q) (r₂ : Reduction Q R) :
    Reduction P R where
  mapInstance := fun I => r₂.mapInstance (r₁.mapInstance I)
  reduce := fun I A => r₂.reduce (r₁.mapInstance I) (r₁.reduce I A)
  loss := r₁.loss.comp r₂.loss
  advantage_le := by
    intro n I A
    calc
      P.advantage n I A
          ≤ r₁.loss.eval n
              (Q.advantage n (r₁.mapInstance I) (r₁.reduce I A)) :=
            r₁.advantage_le I A
      _ ≤ r₁.loss.eval n
            (r₂.loss.eval n
              (R.advantage n
                (r₂.mapInstance (r₁.mapInstance I))
                (r₂.reduce (r₁.mapInstance I) (r₁.reduce I A)))) :=
            r₁.loss.monotone n
              (r₂.advantage_le (r₁.mapInstance I) (r₁.reduce I A))

/-- Map a source instance family pointwise to the target goal. -/
def mapFamily {P : CryptoGoal.{u}} {Q : CryptoGoal.{w}}
    (R : Reduction P Q) (F : InstanceFamily P) : InstanceFamily Q :=
  fun n => R.mapInstance (F n)

theorem mapFamily_comp {P : CryptoGoal.{u}} {Q : CryptoGoal.{w}}
    {R : CryptoGoal.{t}} (r₁ : Reduction P Q) (r₂ : Reduction Q R)
    (F : InstanceFamily P) :
    (r₁.comp r₂).mapFamily F = r₂.mapFamily (r₁.mapFamily F) := by
  rfl

end Reduction
