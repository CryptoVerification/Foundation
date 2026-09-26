import Foundation.Resource.Measure

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

/-- A pointwise quantitative bound on the resource usage of the transformed
adversary family. The coefficients and degrees are retained as data. -/
structure ResourceBound {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (R : Reduction P Q) (RP : ResourceMeasure P)
    (RQ : ResourceMeasure Q) where
  coefficient : Nat
  securityDegree : Nat
  sourceDegree : Nat
  bound : ∀ (F : InstanceFamily P) (A : AdversaryFamily P F) (n : Nat),
    RQ.profile (R.mapFamily F) (R.mapAdversaryFamily F A) n ≤
      coefficient * (n + 1) ^ securityDegree *
        (RP.profile F A n + 1) ^ sourceDegree

namespace ResourceBound

/-- The identity reduction preserves a measure up to the harmless bound
`s ≤ s + 1`. -/
def id (P : CryptoGoal.{u}) (RM : ResourceMeasure P) :
    (Reduction.id P).ResourceBound RM RM where
  coefficient := 1
  securityDegree := 0
  sourceDegree := 1
  bound := by
    intro F A n
    change RM.profile F A n ≤
      1 * (n + 1) ^ 0 * (RM.profile F A n + 1) ^ 1
    simp

/-- Compose a bound from `P` to `Q` with a bound from `Q` to `S`.
The resulting coefficient is `c₂ * (c₁ + 1)^d₂`, the security degree is
`k₂ + k₁ * d₂`, and the source degree is `d₁ * d₂`. -/
def comp {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {S : CryptoGoal.{w}} {R₁ : Reduction P Q} {R₂ : Reduction Q S}
    {RP : ResourceMeasure P} {RQ : ResourceMeasure Q}
    {RS : ResourceMeasure S}
    (B₁ : R₁.ResourceBound RP RQ)
    (B₂ : R₂.ResourceBound RQ RS) :
    (R₁.comp R₂).ResourceBound RP RS where
  coefficient := B₂.coefficient * (B₁.coefficient + 1) ^ B₂.sourceDegree
  securityDegree := B₂.securityDegree + B₁.securityDegree * B₂.sourceDegree
  sourceDegree := B₁.sourceDegree * B₂.sourceDegree
  bound := by
    intro F A n
    let s := RP.profile F A n
    let t := RQ.profile (R₁.mapFamily F) (R₁.mapAdversaryFamily F A) n
    let u := RS.profile ((R₁.comp R₂).mapFamily F)
      ((R₁.comp R₂).mapAdversaryFamily F A) n
    let X := (n + 1) ^ B₁.securityDegree * (s + 1) ^ B₁.sourceDegree
    have ht : t ≤ B₁.coefficient * X := by
      simpa only [t, X, s, mul_assoc] using B₁.bound F A n
    have hX : 1 ≤ X := by
      dsimp [X, s]
      calc
        1 = 1 * 1 := by simp
        _ ≤ (n + 1) ^ B₁.securityDegree *
            (RP.profile F A n + 1) ^ B₁.sourceDegree :=
          Nat.mul_le_mul
            (Nat.one_le_pow' B₁.securityDegree n)
            (Nat.one_le_pow' B₁.sourceDegree (RP.profile F A n))
    have htPlus : t + 1 ≤ (B₁.coefficient + 1) * X := by
      calc
        t + 1 ≤ B₁.coefficient * X + 1 := Nat.add_le_add_right ht 1
        _ ≤ B₁.coefficient * X + X := Nat.add_le_add_left hX _
        _ = (B₁.coefficient + 1) * X := by simp [Nat.add_mul]
    have hu : u ≤ B₂.coefficient * (n + 1) ^ B₂.securityDegree *
        (t + 1) ^ B₂.sourceDegree := by
      change RS.profile (R₂.mapFamily (R₁.mapFamily F))
        (R₂.mapAdversaryFamily (R₁.mapFamily F)
          (R₁.mapAdversaryFamily F A)) n ≤
          B₂.coefficient * (n + 1) ^ B₂.securityDegree *
            (RQ.profile (R₁.mapFamily F)
              (R₁.mapAdversaryFamily F A) n + 1) ^ B₂.sourceDegree
      exact B₂.bound (R₁.mapFamily F) (R₁.mapAdversaryFamily F A) n
    calc
      u ≤ B₂.coefficient * (n + 1) ^ B₂.securityDegree *
          (t + 1) ^ B₂.sourceDegree := hu
      _ ≤ B₂.coefficient * (n + 1) ^ B₂.securityDegree *
          ((B₁.coefficient + 1) * X) ^ B₂.sourceDegree :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htPlus _)
      _ = (B₂.coefficient * (B₁.coefficient + 1) ^ B₂.sourceDegree) *
          (n + 1) ^ (B₂.securityDegree + B₁.securityDegree * B₂.sourceDegree) *
          (RP.profile F A n + 1) ^ (B₁.sourceDegree * B₂.sourceDegree) := by
        dsimp [X, s]
        simp only [mul_pow, pow_mul, pow_add]
        ac_rfl

/-- The explicit blow-up expression is polynomially bounded whenever the
source resource profile is. -/
theorem majorant_polynomiallyBounded
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q} {RP : ResourceMeasure P}
    {RQ : ResourceMeasure Q} (B : R.ResourceBound RP RQ)
    (F : InstanceFamily P) (A : AdversaryFamily P F)
    (hSource : PolynomiallyBounded (RP.profile F A)) :
    PolynomiallyBounded (fun n =>
      B.coefficient * (n + 1) ^ B.securityDegree *
        (RP.profile F A n + 1) ^ B.sourceDegree) := by
  have hSourcePlusOne : PolynomiallyBounded
      (fun n => RP.profile F A n + 1) :=
    PolynomiallyBounded.add hSource (PolynomiallyBounded.const 1)
  have hSourcePower : PolynomiallyBounded
      (fun n => (RP.profile F A n + 1) ^ B.sourceDegree) :=
    PolynomiallyBounded.pow hSourcePlusOne B.sourceDegree
  have hParameterPlusOne : PolynomiallyBounded (fun n => n + 1) :=
    PolynomiallyBounded.add PolynomiallyBounded.id
      (PolynomiallyBounded.const 1)
  have hParameterPower : PolynomiallyBounded
      (fun n => (n + 1) ^ B.securityDegree) :=
    PolynomiallyBounded.pow hParameterPlusOne B.securityDegree
  exact PolynomiallyBounded.mul
    (PolynomiallyBounded.mul
      (PolynomiallyBounded.const B.coefficient) hParameterPower)
    hSourcePower

/-- A quantitative resource bound turns source polynomial-resource
admissibility into target polynomial-resource admissibility. -/
theorem preservesAdmissibility
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q} {RP : ResourceMeasure P}
    {RQ : ResourceMeasure Q} (B : R.ResourceBound RP RQ) :
    R.PreservesAdmissibility RP.polynomialClass RQ.polynomialClass := by
  constructor
  intro F A hA
  exact PolynomiallyBounded.mono (B.bound F A)
    (B.majorant_polynomiallyBounded F A hA)

end ResourceBound

end Reduction
