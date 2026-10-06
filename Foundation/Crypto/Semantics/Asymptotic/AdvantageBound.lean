import Foundation.Crypto.Semantics.Asymptotic.Negligible
import Foundation.Crypto.Core.Bound

open scoped ENNReal

namespace AdvantageBound

/-- Multiply an advantage by a natural-valued parameter profile. The
profile need not be polynomially bounded to define this loss. -/
noncomputable def polynomialMultiplier (p : Nat → Nat) : AdvantageBound where
  eval := fun n x => (p n : ℝ≥0∞) * x
  monotone := by
    intro n x y h
    exact mul_le_mul_right h _

/-- Multiplicative loss plus an additive error. Concrete security does not
require the coefficient to be polynomial or the error to be negligible. -/
noncomputable def affine (coefficient : Nat → Nat) (error : Nat → ℝ≥0∞) :
    AdvantageBound where
  eval := fun n x => (coefficient n : ℝ≥0∞) * x + error n
  monotone := by
    intro n x y h
    exact add_le_add (mul_le_mul_right h _) (le_refl _)

/-- An advantage loss maps every negligible function to a negligible
function. Monotonicity alone does not imply this property. -/
def PreservesNegligible (L : AdvantageBound) : Prop :=
  ∀ (ε : Nat → ℝ≥0∞), Negligible ε →
    Negligible (fun n => L.eval n (ε n))

theorem id_preservesNegligible : AdvantageBound.id.PreservesNegligible := by
  intro ε hε
  exact hε

theorem polynomialMultiplier_preservesNegligible {p : Nat → Nat}
    (hp : PolynomiallyBounded p) :
    (AdvantageBound.polynomialMultiplier p).PreservesNegligible := by
  intro ε hε
  exact Negligible.mul_polynomial hε hp

theorem affine_preservesNegligible {coefficient : Nat → Nat}
    {error : Nat → ℝ≥0∞} (hc : PolynomiallyBounded coefficient)
    (he : Negligible error) :
    (AdvantageBound.affine coefficient error).PreservesNegligible := by
  intro ε hε
  exact (Negligible.mul_polynomial hε hc).add he

/-- `f.comp g` applies `g` first, then `f`, so preservation follows in
that same order. -/
theorem comp_preservesNegligible (f g : AdvantageBound)
    (hf : f.PreservesNegligible) (hg : g.PreservesNegligible) :
    (f.comp g).PreservesNegligible := by
  intro ε hε
  exact hf (fun n => g.eval n (ε n)) (hg ε hε)

end AdvantageBound
