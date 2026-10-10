import Foundation.Quantum.QKD.SubnormalizedPhysical

/-! Guessing bounds, quantum data processing and event restriction for
subnormalized states. The zero branch has zero success without renormalizing. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open Guessing
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X : Type} [Fintype X] {e a b : Space}

def Dominated (ρ : State X e) (σ : Density e) (q : ℝ) : Prop :=
  ∀ x, (((q : ℂ) • σ.matrix) - ρ.block x).PosSemidef

theorem score_le_dominated (ρ : State X e) (σ : Density e) (q : ℝ)
    (h : Dominated ρ σ q) (M : Measurement X e) : score ρ M ≤ q := by
  have hx (x : X) : (M.operator x * ρ.block x).trace.re ≤
      q * (M.operator x * σ.matrix).trace.re := by
    have hh := (Complex.nonneg_iff.mp (trace_product_nonneg (M.positive x) (h x))).1
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
      Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hh
    linarith
  calc
    score ρ M ≤ ∑ x, q * (M.operator x * σ.matrix).trace.re := Finset.sum_le_sum (fun x _ => hx x)
    _ = q := by rw [← Finset.mul_sum, measurement_total, mul_one]

def post (ρ : State X a) (C : Channel a b) : State X b where
  block x := C.toKraus.apply (ρ.block x)
  positive x := C.toKraus.positive (ρ.positive x)
  bounded := by
    simp only [C.toKraus.trace_apply, C.complete, Matrix.one_mul]
    exact ρ.bounded

theorem mass_post (ρ : State X a) (C : Channel a b) : mass (post ρ C) = mass ρ := by
  simp only [mass, post, C.toKraus.trace_apply, C.complete, Matrix.one_mul]

theorem score_post (ρ : State X a) (C : Channel a b) (M : Measurement X b) :
    score (post ρ C) M = score ρ (Guessing.pull C M) := by
  unfold score post Guessing.pull
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg Complex.re (C.toKraus.trace_dual (ρ.block x) (M.operator x))

theorem score_restrict_le (ρ : State X e) (P : X → Prop) [DecidablePred P] (M : Measurement X e) :
    score (restrict ρ P) M ≤ score ρ M := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P x
  · simp [restrict, hp]
  · simpa [restrict, hp] using
      (Complex.nonneg_iff.mp (trace_product_nonneg (M.positive x) (ρ.positive x))).1

variable [Nonempty X]

theorem probability_le_dominated (ρ : State X e) (σ : Density e) (q : ℝ)
    (h : Dominated ρ σ q) : probability ρ ≤ q :=
  csSup_le (range_nonempty ρ) (fun _ ⟨M,hM⟩ => hM ▸ score_le_dominated ρ σ q h M)

theorem probability_post (ρ : State X a) (C : Channel a b) :
    probability (post ρ C) ≤ probability ρ := by
  apply csSup_le (range_nonempty _)
  intro q hq
  obtain ⟨M,rfl⟩ := hq
  rw [score_post]
  exact score_le_probability _ _

theorem probability_restrict (ρ : State X e) (P : X → Prop) [DecidablePred P] :
    probability (restrict ρ P) ≤ probability ρ := by
  apply csSup_le (range_nonempty _)
  intro q hq
  obtain ⟨M,rfl⟩ := hq
  exact (score_restrict_le _ _ M).trans (score_le_probability _ M)

end
end Foundation.Quantum.QKD.Subnormalized
