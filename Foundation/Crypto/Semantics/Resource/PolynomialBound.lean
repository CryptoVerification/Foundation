import Foundation.Crypto.Semantics.Asymptotic.PolynomiallyBounded

namespace ResourcePolynomialBound

/-- Compose two resource inequalities independently of the measured objects.
The coefficient and both degrees agree with the existing reduction bounds. -/
theorem comp_le (n s t u c₁ k₁ d₁ c₂ k₂ d₂ : Nat)
    (ht : t ≤ c₁ * (n + 1) ^ k₁ * (s + 1) ^ d₁)
    (hu : u ≤ c₂ * (n + 1) ^ k₂ * (t + 1) ^ d₂) :
    u ≤ (c₂ * (c₁ + 1) ^ d₂) *
      (n + 1) ^ (k₂ + k₁ * d₂) * (s + 1) ^ (d₁ * d₂) := by
  let X := (n + 1) ^ k₁ * (s + 1) ^ d₁
  have ht' : t ≤ c₁ * X := by
    simpa only [X, mul_assoc] using ht
  have hX : 1 ≤ X := by
    exact Nat.mul_le_mul (Nat.one_le_pow' k₁ n) (Nat.one_le_pow' d₁ s)
  have htPlus : t + 1 ≤ (c₁ + 1) * X := by
    calc
      t + 1 ≤ c₁ * X + 1 := Nat.add_le_add_right ht' 1
      _ ≤ c₁ * X + X := Nat.add_le_add_left hX _
      _ = (c₁ + 1) * X := by simp [Nat.add_mul]
  calc
    u ≤ c₂ * (n + 1) ^ k₂ * (t + 1) ^ d₂ := hu
    _ ≤ c₂ * (n + 1) ^ k₂ * ((c₁ + 1) * X) ^ d₂ :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htPlus _)
    _ = (c₂ * (c₁ + 1) ^ d₂) *
        (n + 1) ^ (k₂ + k₁ * d₂) * (s + 1) ^ (d₁ * d₂) := by
      dsimp [X]
      simp only [mul_pow, pow_mul, pow_add]
      ac_rfl

/-- A polynomial source profile makes the resource majorant polynomial. -/
theorem polynomiallyBounded {source : Nat → Nat}
    (hSource : PolynomiallyBounded source) (coefficient securityDegree sourceDegree : Nat) :
    PolynomiallyBounded (fun n => coefficient * (n + 1) ^ securityDegree *
      (source n + 1) ^ sourceDegree) :=
  ((PolynomiallyBounded.const coefficient).mul
    ((PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).pow securityDegree)).mul
    ((hSource.add (PolynomiallyBounded.const 1)).pow sourceDegree)

end ResourcePolynomialBound
