import Foundation.Quantum.QKD.Guessing

/-! Data processing for optimal quantum guessing. Any verified finite Kraus
channel on Eve's register pulls a complete guessing measurement back to a
complete measurement, so it cannot increase the guessing probability. -/
namespace Foundation.Quantum.QKD.Guessing
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X : Type} [Fintype X] {a b : Space}

/-- Apply a real physical channel to each conditional quantum block. -/
def post (ρ : CQ X a) (C : Channel a b) : CQ X b where
  block x := C.toKraus.apply (ρ.block x)
  positive x := C.toKraus.positive (ρ.positive x)
  normalized := by
    simp only [C.toKraus.trace_apply, C.complete, Matrix.one_mul]
    exact ρ.normalized

theorem dual_sum (K : Kraus a b) (M : X → Operator b) :
    (∑ x, K.dual (M x)) = K.dual (∑ x, M x) := by
  simp only [Kraus.dual, Matrix.mul_sum, Matrix.sum_mul]
  rw [Finset.sum_comm]

/-- Every output guessing strategy is implemented on the input by a complete measurement. -/
def pull (C : Channel a b) (M : Measurement X b) : Measurement X a where
  operator x := C.toKraus.dual (M.operator x)
  positive x := C.toKraus.dual_positive (M.positive x)
  complete := by rw [dual_sum, M.complete, Kraus.dual_one, C.complete]

theorem score_post (ρ : CQ X a) (C : Channel a b) (M : Measurement X b) :
    score (post ρ C) M = score ρ (pull C M) := by
  unfold score post pull
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg Complex.re (C.toKraus.trace_dual (ρ.block x) (M.operator x))

theorem guessBound_post (ρ : CQ X a) (C : Channel a b) (q : ℝ) (h : GuessBound ρ q) :
    GuessBound (post ρ C) q := by
  intro M
  rw [score_post]
  exact h (pull C M)

/-- Quantum processing of the retained side information cannot improve the optimal guess. -/
theorem guessingProbability_post (ρ : CQ X a) (C : Channel a b) :
    guessingProbability (post ρ C) ≤ guessingProbability ρ :=
  (guessingProbability_le_iff _ _).mpr (guessBound_post ρ C _ (score_le_guessingProbability ρ))

end
end Foundation.Quantum.QKD.Guessing
