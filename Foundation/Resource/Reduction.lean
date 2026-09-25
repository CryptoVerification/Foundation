import Foundation.Resource.Adversary

open scoped ENNReal

universe u v w

namespace Reduction

/-- Apply a reduction's adversary transformation at each security parameter.
The target adversaries face the mapped instance family. -/
def mapAdversaryFamily {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (R : Reduction P Q) (F : InstanceFamily P)
    (A : AdversaryFamily P F) : AdversaryFamily Q (R.mapFamily F) :=
  fun n => R.reduce (F n) (A n)

/-- The reduction's quantitative advantage inequality, evaluated on one
adversary family at one security parameter. -/
theorem advantageProfile_le {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (R : Reduction P Q) (F : InstanceFamily P)
    (A : AdversaryFamily P F) (n : Nat) :
    advantageProfile P F A n ≤
      R.loss.eval n
        (advantageProfile Q (R.mapFamily F)
          (R.mapAdversaryFamily F A) n) :=
  R.advantage_le (F n) (A n)

/-- Source admissibility implies admissibility of the transformed target
family. A future resource model can establish this for its chosen classes;
the property is separate from the quantitative `Reduction` structure. -/
structure PreservesAdmissibility {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (R : Reduction P Q) (CP : AdversaryClass P)
    (CQ : AdversaryClass Q) : Prop where
  preserves : ∀ (F : InstanceFamily P) (A : AdversaryFamily P F),
    CP.admissible F A →
      CQ.admissible (R.mapFamily F) (R.mapAdversaryFamily F A)

/-- Every reduction preserves admissibility into a class accepting all
target adversary families. -/
theorem preservesAdmissibility_allTarget
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (R : Reduction P Q) (CP : AdversaryClass P) :
    R.PreservesAdmissibility CP (AdversaryClass.all Q) := by
  constructor
  intro F A _
  trivial

/-- The identity reduction preserves every adversary class. -/
theorem id_preservesAdmissibility
    (P : CryptoGoal.{u}) (C : AdversaryClass P) :
    (Reduction.id P).PreservesAdmissibility C C := by
  constructor
  intro F A hA
  exact hA

/-- Admissibility preservation follows the order of reduction composition:
source to intermediate, then intermediate to target. -/
theorem comp_preservesAdmissibility
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}} {S : CryptoGoal.{w}}
    (r₁ : Reduction P Q) (r₂ : Reduction Q S)
    (CP : AdversaryClass P) (CQ : AdversaryClass Q)
    (CS : AdversaryClass S)
    (h₁ : r₁.PreservesAdmissibility CP CQ)
    (h₂ : r₂.PreservesAdmissibility CQ CS) :
    (r₁.comp r₂).PreservesAdmissibility CP CS := by
  constructor
  intro F A hA
  exact h₂.preserves (r₁.mapFamily F) (r₁.mapAdversaryFamily F A)
    (h₁.preserves F A hA)

end Reduction
