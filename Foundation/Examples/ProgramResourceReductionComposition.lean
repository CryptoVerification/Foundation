import Foundation.Examples.ProgramResourceReduction
import Foundation.Examples.UniformResourceReduction

namespace Foundation.Examples.ProgramResourceReductionComposition

open Foundation.Examples.UniformReduction
  (P Q R sourceModel targetModel T)
open Foundation.Examples.UniformResourceReduction
  (S R₂ finalModel T₂)
open Foundation.Examples.ProgramResourceReduction
  (CP CQ B)

/-- The second target measure still depends on its program and parameter. -/
def CS : ProgramResourceMeasure finalModel where
  profile := fun _ prog n => (n + 1) * ((show Nat from prog) + n)

/-- A nontrivial bound for the second transformation. Its intermediate
source is exactly the program produced by the first transformation. -/
def B₂ : T₂.ResourceBound CQ CS where
  coefficient := 3
  securityDegree := 1
  sourceDegree := 2
  bound := by
    intro F prog n
    let p : Nat := show Nat from prog
    change (n + 1) * ((p + 1) + n) ≤
      3 * (n + 1) ^ 1 *
        ((n + 1) ^ 2 * (p + n) + 1) ^ 2
    have hBase : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow' 2 n
    have hCost : p + n ≤
        (n + 1) ^ 2 * (p + n) := by
      calc
        p + n = 1 * (p + n) := by simp
        _ ≤ (n + 1) ^ 2 * (p + n) :=
          Nat.mul_le_mul_right _ hBase
    let z := (n + 1) ^ 2 * (p + n) + 1
    have hInside : (p + 1) + n ≤ z ^ 2 := by
      have hz : (p + 1) + n ≤ z := by
        dsimp [z]
        omega
      have hzOne : 1 ≤ z := by dsimp [z]; omega
      nlinarith
    calc
      (n + 1) * ((p + 1) + n) ≤
          (n + 1) * z ^ 2 := Nat.mul_le_mul_left _ hInside
      _ = 1 * ((n + 1) * z ^ 2) := by simp
      _ ≤ 3 * ((n + 1) * z ^ 2) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 3 * (n + 1) ^ 1 *
          ((n + 1) ^ 2 * (p + n) + 1) ^ 2 := by
        simp only [pow_one]
        dsimp [z]
        ac_rfl

example : (Reduction.ProgramTransformation.id P sourceModel).ResourceBound CP CP :=
  Reduction.ProgramTransformation.ResourceBound.id P sourceModel CP

example : (Reduction.ProgramTransformation.ResourceBound.id P sourceModel CP).coefficient =
    1 := by rfl
example : (Reduction.ProgramTransformation.ResourceBound.id P sourceModel CP).securityDegree =
    0 := by rfl
example : (Reduction.ProgramTransformation.ResourceBound.id P sourceModel CP).sourceDegree =
    1 := by rfl

example : (Reduction.id P).PreservesAdmissibility
    (sourceModel.polynomialProgramClass CP)
    (sourceModel.polynomialProgramClass CP) :=
  (Reduction.ProgramTransformation.ResourceBound.id P sourceModel CP).preservesAdmissibility

example : (Reduction.id P).PreservesAdmissibility
    (sourceModel.polynomialProgramClass CP)
    (sourceModel.polynomialProgramClass CP) :=
  Reduction.id_preservesAdmissibility P (sourceModel.polynomialProgramClass CP)

example : (T.comp T₂).ResourceBound CP CS := B.comp B₂

example : (B.comp B₂).coefficient = 12 := by rfl
example : (B.comp B₂).securityDegree = 5 := by rfl
example : (B.comp B₂).sourceDegree = 2 := by rfl

example (F : InstanceFamily P) :
    (T.comp T₂).transform F (3 : Nat) = (5 : Nat) := by rfl

/-- The source witness `3` is explicitly transformed through `4` to `5`. -/
example (F : InstanceFamily P) :
    (finalModel.polynomialProgramClass CS).admissible
      ((R.comp R₂).mapFamily F)
      ((R.comp R₂).mapAdversaryFamily F
        (sourceModel.realize F (3 : Nat))) := by
  have hSource : (sourceModel.polynomialProgramClass CP).admissible F
      (sourceModel.realize F (3 : Nat)) := by
    refine ⟨(3 : Nat), rfl, ?_⟩
    exact PolynomiallyBounded.add
      (PolynomiallyBounded.const 3) PolynomiallyBounded.id
  exact (B.comp B₂).preservesAdmissibility.preserves F _ hSource

/-- The composed field supplies the pointwise inequality directly. -/
example (F : InstanceFamily P) (prog : sourceModel.Program F) (n : Nat) :
    CS.profile ((R.comp R₂).mapFamily F) ((T.comp T₂).transform F prog) n ≤
      (B.comp B₂).coefficient * (n + 1) ^ (B.comp B₂).securityDegree *
        (CP.profile F prog n + 1) ^ (B.comp B₂).sourceDegree :=
  (B.comp B₂).bound F prog n

/-- Composing quantitative witnesses preserves the same-witness class. -/
example : (R.comp R₂).PreservesAdmissibility
    (sourceModel.polynomialProgramClass CP)
    (finalModel.polynomialProgramClass CS) :=
  (B.comp B₂).preservesAdmissibility

/-- Sequential preservation reaches exactly the same conclusion type. -/
example : (R.comp R₂).PreservesAdmissibility
    (sourceModel.polynomialProgramClass CP)
    (finalModel.polynomialProgramClass CS) :=
  Reduction.comp_preservesAdmissibility R R₂
    (sourceModel.polynomialProgramClass CP)
    (targetModel.polynomialProgramClass CQ)
    (finalModel.polynomialProgramClass CS)
    B.preservesAdmissibility B₂.preservesAdmissibility

example (F : InstanceFamily P)
    (hS : SecureOnWithin S (finalModel.polynomialProgramClass CS)
      ((R.comp R₂).mapFamily F)) :
    SecureOnWithin P (sourceModel.polynomialProgramClass CP) F := by
  have hLoss : (R.comp R₂).loss.PreservesNegligible :=
    AdvantageBound.comp_preservesNegligible R.loss R₂.loss
      AdvantageBound.id_preservesNegligible
      AdvantageBound.id_preservesNegligible
  exact (R.comp R₂).secureOnWithin _ _ F
    (B.comp B₂).preservesAdmissibility hLoss hS

example (F : InstanceFamily P)
    (hS : SecureOnWithin S (finalModel.polynomialProgramClass CS)
      ((R.comp R₂).mapFamily F)) :
    SecureOnWithin P (sourceModel.polynomialProgramClass CP) F := by
  have hQ : SecureOnWithin Q (targetModel.polynomialProgramClass CQ)
      (R.mapFamily F) :=
    R₂.secureOnWithin _ _ (R.mapFamily F) B₂.preservesAdmissibility
      AdvantageBound.id_preservesNegligible hS
  exact R.secureOnWithin _ _ F B.preservesAdmissibility
    AdvantageBound.id_preservesNegligible hQ

end Foundation.Examples.ProgramResourceReductionComposition
