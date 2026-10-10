import Foundation.Quantum.NuclearTrace
import Mathlib.Logic.Equiv.Nat

/-! Algebra and the two-sided ideal property of absolutely convergent
rank-one expansions. Cyclicity is proved before bundling trace-class algebra. -/
namespace Foundation.Quantum.Infinite.NuclearSeries
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Precomposition transports the right-hand vectors by the Hilbert adjoint. -/
def pre (S : NuclearSeries E F) (T : G →L[ℂ] E) : NuclearSeries G F where
  left := S.left
  right n := T.adjoint (S.right n)
  summable := (S.summable.mul_left ‖T.adjoint‖).of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun n => by
      nlinarith [mul_le_mul_of_nonneg_left (T.adjoint.le_opNorm (S.right n))
        (norm_nonneg (S.left n))])

theorem pre_operator (S : NuclearSeries E F) (T : G →L[ℂ] E) :
    (S.pre T).operator = S.operator.comp T := by
  have h := ((ContinuousLinearMap.compL ℂ G E F).flip T).map_tsum S.summable_rankOne
  change S.operator.comp T = ∑' n, (InnerProductSpace.rankOne ℂ (S.left n) (S.right n)).comp T at h
  simp_rw [InnerProductSpace.rankOne_comp] at h
  exact h.symm

/-- Multiplication by a scalar is represented on the first vector. -/
def scale (c : ℂ) (S : NuclearSeries E F) : NuclearSeries E F where
  left n := c • S.left n
  right := S.right
  summable := by simpa only [norm_smul, mul_assoc] using S.summable.mul_left ‖c‖

omit [CompleteSpace E] in
theorem scale_operator (c : ℂ) (S : NuclearSeries E F) :
    (S.scale c).operator = c • S.operator := by
  simp only [operator, scale, map_smul]
  exact S.summable_rankOne.tsum_const_smul c

/-- Interleaving two expansions keeps the index countable. -/
def add (S T : NuclearSeries E F) : NuclearSeries E F where
  left n := Sum.elim S.left T.left (Equiv.natSumNatEquivNat.symm n)
  right n := Sum.elim S.right T.right (Equiv.natSumNatEquivNat.symm n)
  summable := by
    let f : ℕ ⊕ ℕ → ℝ := fun k =>
      ‖Sum.elim S.left T.left k‖ * ‖Sum.elim S.right T.right k‖
    have hf : Summable f := Summable.sum f S.summable T.summable
    exact (Equiv.natSumNatEquivNat.symm.summable_iff (f := f)).mpr hf

omit [CompleteSpace E] in
theorem add_operator (S T : NuclearSeries E F) :
    (S.add T).operator = S.operator + T.operator := by
  let f : ℕ ⊕ ℕ → E →L[ℂ] F := Sum.elim
    (fun n => InnerProductSpace.rankOne ℂ (S.left n) (S.right n))
    (fun n => InnerProductSpace.rankOne ℂ (T.left n) (T.right n))
  have hs : HasSum f (S.operator + T.operator) := HasSum.sum S.operator_hasSum T.operator_hasSum
  have he : (S.add T).operator = ∑' n, f (Equiv.natSumNatEquivNat.symm n) := by
    apply tsum_congr
    intro n
    dsimp only [add]
    cases Equiv.natSumNatEquivNat.symm n <;> rfl
  exact he.trans ((Equiv.natSumNatEquivNat.symm.tsum_eq f).trans hs.tsum_eq)

omit [CompleteSpace E] in
theorem scale_trace (c : ℂ) (S : NuclearSeries E E) :
    (S.scale c).traceExpression = c * S.traceExpression := by
  simp only [traceExpression, scale, inner_smul_right]
  exact tsum_mul_left

omit [CompleteSpace E] in
theorem add_trace (S T : NuclearSeries E E) :
    (S.add T).traceExpression = S.traceExpression + T.traceExpression := by
  let f : ℕ ⊕ ℕ → ℂ := Sum.elim
    (fun n => inner ℂ (S.right n) (S.left n))
    (fun n => inner ℂ (T.right n) (T.left n))
  have hs : HasSum f (S.traceExpression + T.traceExpression) :=
    HasSum.sum S.summable_trace.hasSum T.summable_trace.hasSum
  have he : (S.add T).traceExpression = ∑' n, f (Equiv.natSumNatEquivNat.symm n) := by
    apply tsum_congr
    intro n
    dsimp only [add]
    cases Equiv.natSumNatEquivNat.symm n <;> rfl
  exact he.trans ((Equiv.natSumNatEquivNat.symm.tsum_eq f).trans hs.tsum_eq)

/-- The trace can be cycled past any bounded operation. -/
theorem trace_cyclic (S : NuclearSeries E F) (T : F →L[ℂ] E) :
    (S.post T).traceExpression = (S.pre T).traceExpression := by
  apply tsum_congr
  intro n
  exact (T.adjoint_inner_left (S.left n) (S.right n)).symm

end
end Foundation.Quantum.Infinite.NuclearSeries
