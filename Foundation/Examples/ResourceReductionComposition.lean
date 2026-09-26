import Foundation.Examples.ResourceReduction

namespace Foundation.Examples.ResourceReductionComposition

open Foundation.Examples.ResourceReduction
  (P Q R sourceMeasure targetMeasure)

abbrev S : CryptoGoal := Foundation.Examples.Relations.C

/-- A second dummy reduction with identity advantage loss. -/
def R₂ : Reduction Q S where
  mapInstance := fun _ => ()
  reduce := fun _ _ => (0 : Nat)
  loss := AdvantageBound.id
  advantage_le := by
    intro n I A
    exact le_refl _

def finalMeasure : ResourceMeasure S where
  profile := fun _ _ n => 3 * (n + 1) * ((n + 1) ^ 3 + 1) ^ 2

/-- The first synthetic target cost is `(n + 1)^3`, bounded by
`2 * (n + 1)^2 * (sourceCost + 1)`. -/
def firstBound : R.ResourceBound sourceMeasure targetMeasure where
  coefficient := 2
  securityDegree := 2
  sourceDegree := 1
  bound := by
    intro F A n
    change (n + 1) ^ 2 * (n + 1) ≤
      2 * (n + 1) ^ 2 * (n + 1) ^ 1
    have h : 1 * ((n + 1) ^ 2 * (n + 1)) ≤
        2 * ((n + 1) ^ 2 * (n + 1)) :=
      Nat.mul_le_mul_right _ (by decide : 1 ≤ 2)
    simpa only [one_mul, pow_one, mul_assoc] using h

/-- The final synthetic cost has the exact bound
`3 * (n + 1) * (intermediateCost + 1)^2`. -/
def secondBound : R₂.ResourceBound targetMeasure finalMeasure where
  coefficient := 3
  securityDegree := 1
  sourceDegree := 2
  bound := by
    intro F A n
    change 3 * (n + 1) * ((n + 1) ^ 3 + 1) ^ 2 ≤
      3 * (n + 1) ^ 1 * ((n + 1) ^ 2 * (n + 1) + 1) ^ 2
    simp [pow_succ]

def composedBound : (R.comp R₂).ResourceBound sourceMeasure finalMeasure :=
  firstBound.comp secondBound

example : composedBound.coefficient = 27 := by rfl
example : composedBound.securityDegree = 5 := by rfl
example : composedBound.sourceDegree = 2 := by rfl

example (F : InstanceFamily P) (A : AdversaryFamily P F) (n : Nat) :
    finalMeasure.profile ((R.comp R₂).mapFamily F)
        ((R.comp R₂).mapAdversaryFamily F A) n ≤
      composedBound.coefficient * (n + 1) ^ composedBound.securityDegree *
        (sourceMeasure.profile F A n + 1) ^ composedBound.sourceDegree :=
  composedBound.bound F A n

/-- The abstract and quantitative preservation routes reach the same type. -/
example : (R.comp R₂).PreservesAdmissibility
    sourceMeasure.polynomialClass finalMeasure.polynomialClass :=
  Reduction.comp_preservesAdmissibility R R₂
    sourceMeasure.polynomialClass targetMeasure.polynomialClass
    finalMeasure.polynomialClass
    firstBound.preservesAdmissibility secondBound.preservesAdmissibility

example : (R.comp R₂).PreservesAdmissibility
    sourceMeasure.polynomialClass finalMeasure.polynomialClass :=
  composedBound.preservesAdmissibility

/-- Both routes can feed the existing security transport theorem. -/
example (F : InstanceFamily P)
    (hS : SecureOnWithin S finalMeasure.polynomialClass
      ((R.comp R₂).mapFamily F)) :
    SecureOnWithin P sourceMeasure.polynomialClass F :=
  (R.comp R₂).secureOnWithin _ _ F
    composedBound.preservesAdmissibility
    (AdvantageBound.comp_preservesNegligible R.loss R₂.loss
      AdvantageBound.id_preservesNegligible
      AdvantageBound.id_preservesNegligible)
    hS

example (F : InstanceFamily P)
    (hS : SecureOnWithin S finalMeasure.polynomialClass
      ((R.comp R₂).mapFamily F)) :
    SecureOnWithin P sourceMeasure.polynomialClass F := by
  have hQ : SecureOnWithin Q targetMeasure.polynomialClass (R.mapFamily F) :=
    R₂.secureOnWithin _ _ (R.mapFamily F)
      secondBound.preservesAdmissibility
      AdvantageBound.id_preservesNegligible hS
  exact R.secureOnWithin _ _ F firstBound.preservesAdmissibility
    AdvantageBound.id_preservesNegligible hQ

end Foundation.Examples.ResourceReductionComposition
