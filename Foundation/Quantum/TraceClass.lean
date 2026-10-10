import Foundation.Quantum.NuclearTrace
import Mathlib.Analysis.InnerProductSpace.Positive

/-! Trace-class operators via absolutely summable rank-one representations on
Hilbert space. The trace is independent of the chosen representation. The
trace norm and completeness of the resulting ideal are developed separately. -/
namespace Foundation.Quantum.Infinite
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ComplexOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Positivity is preserved by an absolutely convergent operator expansion. -/
theorem NuclearSeries.operator_positive (S : NuclearSeries E E)
    (h : ∀ n, (InnerProductSpace.rankOne ℂ (S.left n) (S.right n)).IsPositive) :
    S.operator.IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex S.operator).mpr
  intro x
  have hs : inner ℂ x (S.operator x) =
      ∑' n, inner ℂ x (InnerProductSpace.rankOne ℂ (S.left n) (S.right n) x) := by
    simpa only [NuclearSeries.operator, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, innerSL_apply_apply] using
      ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ E x)).map_tsum S.summable_rankOne
  have hr : 0 ≤ inner ℂ x (S.operator x) := by
    rw [hs]
    exact tsum_nonneg (fun n => (h n).inner_nonneg_right x)
  have hl : 0 ≤ inner ℂ (S.operator x) x := by
    rw [← inner_conj_symm]
    obtain ⟨hr0, hi0⟩ := Complex.nonneg_iff.mp hr
    apply Complex.nonneg_iff.mpr
    refine ⟨hr0, ?_⟩
    change 0 = -(inner ℂ x (S.operator x)).im
    rw [← hi0, neg_zero]
  obtain ⟨hreal, him⟩ := Complex.nonneg_iff.mp hl
  exact ⟨Complex.ext (by simp) (by simpa using him), hreal⟩

/-- Nuclear representation is a predicate on the actual operator, not extra observable data. -/
structure TraceClass (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  operator : E →L[ℂ] E
  representable : ∃ S : NuclearSeries E E, S.operator = operator

namespace TraceClass

def ofSeries (S : NuclearSeries E E) : TraceClass E := ⟨S.operator, S, rfl⟩

def trace (T : TraceClass E) : ℂ := T.representable.choose.traceExpression

@[simp] theorem trace_ofSeries (S : NuclearSeries E E) : (ofSeries S).trace = S.traceExpression :=
  NuclearSeries.trace_independent _ S (ofSeries S).representable.choose_spec

theorem trace_eq_diagonal {ι : Type*} (T : TraceClass E) (b : HilbertBasis ι ℂ E) :
    T.trace = ∑' i, inner ℂ (b i) (T.operator (b i)) := by
  rw [trace, T.representable.choose.trace_diagonal b, T.representable.choose_spec]

theorem trace_nonneg (T : TraceClass E) (h : T.operator.IsPositive) : 0 ≤ T.trace := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ E
  rw [T.trace_eq_diagonal b]
  exact tsum_nonneg (fun i => h.inner_nonneg_right (b i))

/-- Equal actual operators give equal traces, regardless of the existential witnesses. -/
theorem trace_congr (S T : TraceClass E) (h : S.operator = T.operator) : S.trace = T.trace :=
  NuclearSeries.trace_independent _ _
    (S.representable.choose_spec.trans (h.trans T.representable.choose_spec.symm))

end TraceClass

/-- An infinite-dimensional state has genuine positivity and representation-independent trace one. -/
structure TraceDensity (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  state : TraceClass E
  positive : state.operator.IsPositive
  normalized : state.trace = 1

/-- A normalized pure state exists on every Hilbert space with a unit vector. -/
def pureTraceDensity (x : E) (hx : ‖x‖ = 1) : TraceDensity E where
  state := TraceClass.ofSeries (NuclearSeries.single x x)
  positive := by
    change (NuclearSeries.single x x).operator.IsPositive
    rw [NuclearSeries.single_operator]
    exact InnerProductSpace.isPositive_rankOne_self x
  normalized := by
    rw [TraceClass.trace_ofSeries, NuclearSeries.single_traceExpression,
      inner_self_eq_norm_sq_to_K, hx]
    norm_num

end
end Foundation.Quantum.Infinite
