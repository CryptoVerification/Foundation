import Foundation.Quantum.NuclearSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-! An actual infinite sum of rank-one operators on the sequence Hilbert space.
Its presentation has total trace expression one. Independence of presentation
is deliberately not assumed when stating this result. -/
namespace Foundation.Quantum.Infinite
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace

def coordinateVector (n : ℕ) : SequenceSpace := lp.single 2 n (1 : ℂ)

@[simp] theorem coordinateVector_norm (n : ℕ) : ‖coordinateVector n‖ = 1 := by
  simp [coordinateVector, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

/-- A geometrically decaying diagonal expansion, with every coordinate present. -/
def geometricSeries : NuclearSeries SequenceSpace SequenceSpace where
  left n := ((1 / 2 : ℂ) ^ n / 2) • coordinateVector n
  right := coordinateVector
  summable := by
    have h : Summable (fun n : ℕ => ‖(1 / 2 : ℂ) ^ n‖) :=
      (summable_geometric_of_norm_lt_one (x := (1 / 2 : ℂ)) (by norm_num)).norm
    simpa [norm_smul, norm_div] using h.div_const 2

@[simp] theorem geometricSeries_trace : geometricSeries.traceExpression = 1 := by
  have h := hasSum_geometric_of_norm_lt_one (ξ := (1 / 2 : ℂ)) (by norm_num)
  have hs : (∑' n : ℕ, (1 / 2 : ℂ) ^ n) = 2 := by
    convert h.tsum_eq using 1; norm_num
  simp only [NuclearSeries.traceExpression, geometricSeries, inner_smul_right]
  have hv (n : ℕ) : inner ℂ (coordinateVector n) (coordinateVector n) = 1 := by
    simp [coordinateVector]
  simp_rw [hv, mul_one]
  rw [tsum_div_const, hs]
  norm_num

/-- Every coordinate is an actual eigenvector with its nonzero geometric eigenvalue. -/
theorem geometricOperator_coordinate (m : ℕ) :
    geometricSeries.operator (coordinateVector m) =
      ((1 / 2 : ℂ) ^ m / 2) • coordinateVector m := by
  rw [NuclearSeries.operator_apply]
  simp [geometricSeries, coordinateVector, lp.inner_single_left,
    lp.single_apply, Pi.single_apply, apply_ite, eq_comm]

theorem geometricOperator_compact : IsCompactOperator geometricSeries.operator :=
  geometricSeries.operator_compact

end
end Foundation.Quantum.Infinite
