import Foundation.Quantum.TraceCompleteness
import Foundation.Quantum.InfiniteStates

/-! Finite rank-one partial sums converge in the representation-independent
nuclear norm, with the explicit tail mass as an error bound. -/
namespace Foundation.Quantum.Infinite
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Finset
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace NuclearSeries

def tail (S : NuclearSeries E E) (k : Nat) : NuclearSeries E E where
  left n := S.left (n+k)
  right n := S.right (n+k)
  summable := (summable_nat_add_iff k).mpr S.summable

def partialSum (S : NuclearSeries E E) (k : Nat) : TraceClass E :=
  ∑ n ∈ range k, TraceClass.ofSeries (single (S.left n) (S.right n))

theorem partial_operator (S : NuclearSeries E E) (k : Nat) :
    (S.partialSum k).operator = ∑ n ∈ range k, InnerProductSpace.rankOne ℂ (S.left n) (S.right n) := by
  change TraceClass.inclusion (∑ n ∈ range k, _) = _
  rw [map_sum]
  simp only [TraceClass.inclusion, LinearMap.coe_mk, AddHom.coe_mk, TraceClass.ofSeries, single_operator]

theorem tail_operator (S : NuclearSeries E E) (k : Nat) :
    (S.tail k).operator = S.operator - (S.partialSum k).operator := by
  rw [partial_operator]
  have h := S.summable_rankOne.sum_add_tsum_nat_add k
  apply eq_sub_iff_add_eq.mpr
  change (∑' n, InnerProductSpace.rankOne ℂ (S.left (n+k)) (S.right (n+k))) +
    (∑ n ∈ range k, InnerProductSpace.rankOne ℂ (S.left n) (S.right n)) = S.operator
  exact (add_comm _ _).trans h

theorem partial_error (S : NuclearSeries E E) (k : Nat) :
    ‖TraceClass.ofSeries S - S.partialSum k‖ ≤ (S.tail k).mass := by
  have he : TraceClass.ofSeries S - S.partialSum k = TraceClass.ofSeries (S.tail k) := by
    apply TraceClass.ext
    change S.operator - (S.partialSum k).operator = (S.tail k).operator
    exact (S.tail_operator k).symm
  rw [he]
  exact (TraceClass.ofSeries (S.tail k)).nuclearNorm_le_mass (S.tail k) rfl

theorem partial_tendsto (S : NuclearSeries E E) :
    Tendsto S.partialSum atTop (𝓝 (TraceClass.ofSeries S)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun k => (norm_sub_rev _ _).trans_le (S.partial_error k))
  exact tendsto_sum_nat_add (fun n => ‖S.left n‖ * ‖S.right n‖)

end NuclearSeries

theorem geometricSeries_mass : geometricSeries.mass = 1 := by
  simp only [NuclearSeries.mass, geometricSeries, norm_smul, coordinateVector_norm, mul_one,
    norm_div, norm_pow]
  norm_num
  rw [tsum_div_const, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)]
  norm_num


/-- Concrete geometric tails have an explicit dimension-independent error bound. -/
theorem geometric_tail_mass (k : Nat) : (geometricSeries.tail k).mass = (1/2 : ℝ)^k := by
  simp only [NuclearSeries.mass, NuclearSeries.tail, geometricSeries, norm_smul,
    coordinateVector_norm, mul_one, norm_div, norm_pow]
  norm_num
  simp_rw [pow_add]
  rw [tsum_div_const, tsum_mul_right,
    tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)]
  ring

theorem geometric_tail_trace (k : Nat) : (geometricSeries.tail k).traceExpression = (1/2 : ℂ)^k := by
  simp only [NuclearSeries.traceExpression, NuclearSeries.tail, geometricSeries, inner_smul_right]
  have hv (n : Nat) : inner ℂ (coordinateVector n) (coordinateVector n) = 1 := by
    simp [coordinateVector]
  simp_rw [hv, mul_one, pow_add]
  rw [tsum_div_const, tsum_mul_right,
    tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℂ)‖ < 1)]
  ring

/-- Exact error for truncating this genuine infinite-rank state to its first k coordinates. -/
theorem geometric_partial_error_exact (k : Nat) :
    ‖geometricDensity.state - geometricSeries.partialSum k‖ = (1/2 : ℝ)^k := by
  apply le_antisymm
  · exact (geometricSeries.partial_error k).trans_eq (geometric_tail_mass k)
  · let T := geometricDensity.state - geometricSeries.partialSum k
    have he : T = TraceClass.ofSeries (geometricSeries.tail k) := by
      apply TraceClass.ext
      change geometricSeries.operator - (geometricSeries.partialSum k).operator = _
      exact (geometricSeries.tail_operator k).symm
    have h := T.trace_norm_le
    rw [he, TraceClass.trace_ofSeries, geometric_tail_trace] at h
    change _ ≤ (TraceClass.ofSeries (geometricSeries.tail k)).nuclearNorm at h
    rw [norm_pow] at h
    norm_num at h
    change (1/2 : ℝ)^k ≤ T.nuclearNorm
    rwa [he]

/-- The infinite diagonal state has norm exactly one, rather than merely a finite upper bound. -/
theorem geometricDensity_norm : ‖geometricDensity.state‖ = 1 := by
  apply le_antisymm
  · change (TraceClass.ofSeries geometricSeries).nuclearNorm ≤ 1
    exact ((TraceClass.ofSeries geometricSeries).nuclearNorm_le_mass geometricSeries rfl).trans_eq geometricSeries_mass
  · have h := geometricDensity.state.trace_norm_le
    change 1 ≤ geometricDensity.state.nuclearNorm
    simpa only [geometricDensity.normalized, norm_one] using h

/-- Concrete finite-coordinate approximations converge in the new norm. -/
theorem geometric_partial_tendsto : Tendsto geometricSeries.partialSum atTop (𝓝 geometricDensity.state) :=
  geometricSeries.partial_tendsto

end
end Foundation.Quantum.Infinite
