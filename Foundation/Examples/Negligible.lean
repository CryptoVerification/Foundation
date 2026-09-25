import Foundation.Asymptotics.Negligible

open scoped ENNReal
open Filter

namespace Foundation.Examples.Negligible

example : Negligible (fun _ => 0) := Negligible.zero

/-- The first ten values can be arbitrary without affecting negligibility. -/
example : Negligible (fun n => if n < 10 then 1 else 0) := by
  apply (Negligible.congr (δ := fun _ => 0) ?_).mpr Negligible.zero
  filter_upwards [eventually_ge_atTop 10] with n hn
  simp [Nat.not_lt.mpr hn]

example : Negligible (fun _ => (0 : ℝ≥0∞) + 0) :=
  Negligible.add Negligible.zero Negligible.zero

end Foundation.Examples.Negligible
