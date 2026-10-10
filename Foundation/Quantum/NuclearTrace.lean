import Foundation.Quantum.NuclearSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The trace of a nuclear expansion is independent of the expansion and of
an orthonormal Hilbert basis. Absolute double summability justifies exchange
of the two infinite sums; no finiteness of the Hilbert space is assumed. -/
namespace Foundation.Quantum.Infinite.NuclearSeries
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem coefficient_norms {ι : Type*} (b : HilbertBasis ι ℂ E) (x y : E) :
    (fun i => ‖inner ℂ x (b i) * inner ℂ (b i) y‖) =
      (fun i => ‖b.repr x i‖ * ‖b.repr y i‖) := by
  funext i
  rw [norm_mul, norm_inner_symm x (b i)]
  simp only [HilbertBasis.repr_apply_apply]

omit [CompleteSpace E] in
private theorem coefficient_bound {ι : Type*} (b : HilbertBasis ι ℂ E) (x y : E) :
    (Summable (fun i => ‖inner ℂ x (b i) * inner ℂ (b i) y‖)) ∧
      (∑' i, ‖inner ℂ x (b i) * inner ℂ (b i) y‖) ≤ ‖x‖ * ‖y‖ := by
  have hp : (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  simpa only [coefficient_norms, LinearIsometryEquiv.norm_map] using
    lp.tsum_mul_le_mul_norm hp (b.repr x) (b.repr y)

omit [CompleteSpace E] in
/-- Absolute summability on the product is the missing justification for the trace computation. -/
theorem trace_double_summable {ι : Type*} (S : NuclearSeries E E) (b : HilbertBasis ι ℂ E) :
    Summable (fun p : ℕ × ι =>
      inner ℂ (S.right p.1) (b p.2) * inner ℂ (b p.2) (S.left p.1)) := by
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun n => (coefficient_bound b (S.right n) (S.left n)).1, ?_⟩
  apply S.summable.of_nonneg_of_le (fun n => tsum_nonneg (fun i => norm_nonneg _))
  intro n
  simpa only [mul_comm] using (coefficient_bound b (S.right n) (S.left n)).2

/-- Any Hilbert basis computes the same trace expression of the represented operator. -/
theorem trace_diagonal {ι : Type*} (S : NuclearSeries E E) (b : HilbertBasis ι ℂ E) :
    S.traceExpression = ∑' i, inner ℂ (b i) (S.operator (b i)) := by
  let f : ℕ → ι → ℂ := fun n i =>
    inner ℂ (S.right n) (b i) * inner ℂ (b i) (S.left n)
  have hd : Summable (fun p : ℕ × ι => f p.1 p.2) := S.trace_double_summable b
  have hr (n : ℕ) : inner ℂ (S.right n) (S.left n) = ∑' i, f n i :=
    (b.tsum_inner_mul_inner (S.right n) (S.left n)).symm
  have hc (i : ι) : inner ℂ (b i) (S.operator (b i)) = ∑' n, f n i := by
    have h := ((innerSL ℂ (b i)).comp (ContinuousLinearMap.apply ℂ E (b i))).map_tsum
      S.summable_rankOne
    simpa only [operator, f, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply, InnerProductSpace.rankOne_apply, inner_smul_right] using h
  calc
    S.traceExpression = ∑' n, ∑' i, f n i := tsum_congr hr
    _ = ∑' i, ∑' n, f n i := hd.tsum_comm.symm
    _ = _ := tsum_congr (fun i => (hc i).symm)

/-- Equal operators have equal trace expressions even when their expansions differ. -/
theorem trace_independent (S T : NuclearSeries E E) (h : S.operator = T.operator) :
    S.traceExpression = T.traceExpression := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ E
  rw [S.trace_diagonal b, T.trace_diagonal b, h]

end
end Foundation.Quantum.Infinite.NuclearSeries
