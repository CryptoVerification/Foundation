import Foundation.Asymptotics.PolynomiallyBounded

open Filter

namespace Foundation.Examples.PolynomiallyBounded

example : PolynomiallyBounded (fun _ => 42) :=
  PolynomiallyBounded.const 42

example : PolynomiallyBounded (fun n => n + 7) :=
  PolynomiallyBounded.add PolynomiallyBounded.id
    (PolynomiallyBounded.const 7)

example : PolynomiallyBounded (fun n => n * n + 3 * n + 7) := by
  exact PolynomiallyBounded.add
    (PolynomiallyBounded.add
      (PolynomiallyBounded.mul PolynomiallyBounded.id PolynomiallyBounded.id)
      (PolynomiallyBounded.mul (PolynomiallyBounded.const 3)
        PolynomiallyBounded.id))
    (PolynomiallyBounded.const 7)

/-- An arbitrary finite prefix does not affect the growth condition. -/
example : PolynomiallyBounded
    (fun n => if n < 100 then 10 ^ 20 else n * n) := by
  apply (PolynomiallyBounded.congr (s := fun n => n * n) ?_).mpr
    (PolynomiallyBounded.mul PolynomiallyBounded.id PolynomiallyBounded.id)
  filter_upwards [eventually_ge_atTop 100] with n hn
  simp [Nat.not_lt.mpr hn]

end Foundation.Examples.PolynomiallyBounded
