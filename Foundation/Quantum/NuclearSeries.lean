import Foundation.Quantum.Infinite
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Absolutely summable rank-one expansions of actual bounded operators.
The trace expression is initially attached to a presentation: independence of
presentation and comparison with the trace norm remain separate theorems. -/
namespace Foundation.Quantum.Infinite
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The norm-product bound is the nuclear summability requirement. -/
structure NuclearSeries (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] where
  left : ℕ → F
  right : ℕ → E
  summable : Summable (fun n => ‖left n‖ * ‖right n‖)

namespace NuclearSeries

omit [CompleteSpace E] in
theorem summable_rankOne (S : NuclearSeries E F) :
    Summable (fun n => InnerProductSpace.rankOne ℂ (S.left n) (S.right n)) := by
  apply Summable.of_norm
  simpa only [InnerProductSpace.norm_rankOne] using S.summable

/-- The series converges in operator norm, rather than just formally. -/
def operator (S : NuclearSeries E F) : E →L[ℂ] F :=
  ∑' n, InnerProductSpace.rankOne ℂ (S.left n) (S.right n)

omit [CompleteSpace E] in
theorem operator_hasSum (S : NuclearSeries E F) :
    HasSum (fun n => InnerProductSpace.rankOne ℂ (S.left n) (S.right n)) S.operator :=
  S.summable_rankOne.hasSum

omit [CompleteSpace E] in
theorem operator_apply (S : NuclearSeries E F) (x : E) :
    S.operator x = ∑' n, inner ℂ (S.right n) x • S.left n := by
  exact (ContinuousLinearMap.apply ℂ F x).map_tsum S.summable_rankOne

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_operator_le (S : NuclearSeries E F) :
    ‖S.operator‖ ≤ ∑' n, ‖S.left n‖ * ‖S.right n‖ := by
  simpa only [operator, InnerProductSpace.norm_rankOne] using norm_tsum_le_tsum_norm (f := fun n => InnerProductSpace.rankOne ℂ (S.left n) (S.right n)) (by simpa only [InnerProductSpace.norm_rankOne] using S.summable)

omit [CompleteSpace E] in
/-- The diagonal trace expression is absolutely summable on each presentation. -/
theorem summable_trace (S : NuclearSeries E E) :
    Summable (fun n => inner ℂ (S.right n) (S.left n)) := by
  apply Summable.of_norm
  exact S.summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => by simpa only [mul_comm] using norm_inner_le_norm (S.right n) (S.left n))

def traceExpression (S : NuclearSeries E E) : ℂ := ∑' n, inner ℂ (S.right n) (S.left n)

/-- Bounded postprocessing preserves absolute rank-one summability. -/
def post (S : NuclearSeries E F) (T : F →L[ℂ] G) : NuclearSeries E G where
  left n := T (S.left n)
  right := S.right
  summable := (S.summable.mul_left ‖T‖).of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun n => by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (T.le_opNorm (S.left n)) (norm_nonneg (S.right n)))

omit [CompleteSpace E] [CompleteSpace G] in
theorem post_operator (S : NuclearSeries E F) (T : F →L[ℂ] G) :
    (S.post T).operator = T.comp S.operator := by
  have h := (ContinuousLinearMap.compL ℂ E F G T).map_tsum S.summable_rankOne
  change T.comp S.operator = ∑' n, T.comp (InnerProductSpace.rankOne ℂ (S.left n) (S.right n)) at h
  simp_rw [InnerProductSpace.comp_rankOne] at h
  exact h.symm

omit [CompleteSpace E] [CompleteSpace F] in
theorem rankOne_compact (x : F) (y : E) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ x y) := by
  have h : IsCompactOperator (id : ℂ → ℂ) := isCompactOperator_id
  have h' := (h.comp_clm (innerSL ℂ y)).continuous_comp
    (ContinuousLinearMap.toSpanSingleton ℂ x).continuous
  exact h'

omit [CompleteSpace E] in
/-- Absolute expansions are compact operators, proved by operator-norm limits. -/
theorem operator_compact (S : NuclearSeries E F) : IsCompactOperator S.operator := by
  apply isCompactOperator_of_tendsto S.operator_hasSum
  apply Filter.Eventually.of_forall
  intro J
  have h : (∑ n ∈ J, InnerProductSpace.rankOne ℂ (S.left n) (S.right n)) ∈
      compactOperator (RingHom.id ℂ) E F := by
    apply Submodule.sum_mem
    intro n _
    exact rankOne_compact (S.left n) (S.right n)
  exact h

/-- A rank-one expansion represents a genuine operator without an existence axiom. -/
def single (x : F) (y : E) : NuclearSeries E F where
  left n := if n = 0 then x else 0
  right n := if n = 0 then y else 0
  summable := by
    classical
    have hf : (fun n : ℕ => ‖if n = 0 then x else 0‖ * ‖if n = 0 then y else 0‖) =
        (fun n => if n = 0 then ‖x‖ * ‖y‖ else 0) := by
      funext n
      split_ifs <;> simp_all
    rw [hf]
    exact (hasSum_ite_eq 0 (‖x‖ * ‖y‖)).summable

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem single_operator (x : F) (y : E) :
    (single x y).operator = InnerProductSpace.rankOne ℂ x y := by
  classical
  change (∑' n : ℕ, InnerProductSpace.rankOne ℂ (if n = 0 then x else 0)
    (if n = 0 then y else 0)) = _
  simp only [apply_ite, map_zero]
  simp

omit [CompleteSpace E] in
@[simp] theorem single_traceExpression (x y : E) :
    (single x y).traceExpression = inner ℂ y x := by
  classical
  change (∑' n : ℕ, inner ℂ (if n = 0 then y else 0) (if n = 0 then x else 0)) = _
  simp only [apply_ite, inner_zero_right]
  simp

end NuclearSeries
end
end Foundation.Quantum.Infinite
