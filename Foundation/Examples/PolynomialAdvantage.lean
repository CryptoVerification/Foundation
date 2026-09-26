import Foundation.Security.Reduction
import Foundation.Examples.Relations

open scoped ENNReal

namespace Foundation.Examples.PolynomialAdvantage

private theorem quadraticProfile :
    PolynomiallyBounded (fun n => n * n + 3 * n + 7) := by
  apply PolynomiallyBounded.add
  · apply PolynomiallyBounded.add
    · exact PolynomiallyBounded.mul PolynomiallyBounded.id PolynomiallyBounded.id
    · exact PolynomiallyBounded.mul (PolynomiallyBounded.const 3) PolynomiallyBounded.id
  · exact PolynomiallyBounded.const 7

example (ε : Nat → ℝ≥0∞) (hε : Negligible ε) :
    Negligible (fun n => (7 : ℝ≥0∞) * ε n) :=
  Negligible.mul_polynomial hε (PolynomiallyBounded.const 7)

example (ε : Nat → ℝ≥0∞) (hε : Negligible ε) :
    Negligible (fun n => ((n * n + 3 * n + 7 : Nat) : ℝ≥0∞) * ε n) :=
  Negligible.mul_polynomial hε quadraticProfile

example :
    (AdvantageBound.polynomialMultiplier (fun _ => 7)).PreservesNegligible :=
  AdvantageBound.polynomialMultiplier_preservesNegligible
    (PolynomiallyBounded.const 7)

example :
    (AdvantageBound.polynomialMultiplier (fun n => n * n + 3 * n + 7)).PreservesNegligible :=
  AdvantageBound.polynomialMultiplier_preservesNegligible quadraticProfile

example (n : Nat) (x : ℝ≥0∞) :
    (AdvantageBound.polynomialMultiplier (fun _ => 1)).eval n x =
      AdvantageBound.id.eval n x := by
  simp [AdvantageBound.polynomialMultiplier, AdvantageBound.id]

-- The loss exists for an arbitrary profile, without a preservation claim.
noncomputable example : AdvantageBound :=
  AdvantageBound.polynomialMultiplier (fun n => 2 ^ n)

private def factor (n : Nat) : Nat := (n + 1) ^ 2

private theorem factor_polynomiallyBounded : PolynomiallyBounded factor := by
  have hbase : PolynomiallyBounded (fun n => n + 1) :=
    PolynomiallyBounded.add PolynomiallyBounded.id (PolynomiallyBounded.const 1)
  exact hbase.pow 2

/-- A dummy reduction with a polynomial, non-identity advantage loss.
Both goals have zero advantage; this checks the generic transport API. -/
noncomputable def dummyReduction : Reduction Foundation.Examples.Relations.A
    Foundation.Examples.Relations.B where
  mapInstance := fun _ => false
  reduce := fun _ _ => (0 : Fin 3)
  loss := AdvantageBound.polynomialMultiplier factor
  advantage_le := by
    intro n I A
    exact zero_le

example : dummyReduction.loss.eval 1 1 ≠ AdvantageBound.id.eval 1 1 := by
  norm_num [dummyReduction, factor, AdvantageBound.polynomialMultiplier, AdvantageBound.id]

example : dummyReduction.loss.PreservesNegligible :=
  AdvantageBound.polynomialMultiplier_preservesNegligible factor_polynomiallyBounded

/-- Unrestricted-class transport with a non-identity polynomial loss. -/
example (F : InstanceFamily Foundation.Examples.Relations.A)
    (hTarget : SecureOnWithin Foundation.Examples.Relations.B
      (AdversaryClass.all _) (dummyReduction.mapFamily F)) :
    SecureOnWithin Foundation.Examples.Relations.A (AdversaryClass.all _) F := by
  exact dummyReduction.secureOnWithin
    (AdversaryClass.all _) (AdversaryClass.all _) F
    (dummyReduction.preservesAdmissibility_allTarget (AdversaryClass.all _))
    (AdvantageBound.polynomialMultiplier_preservesNegligible factor_polynomiallyBounded)
    hTarget

end Foundation.Examples.PolynomialAdvantage
