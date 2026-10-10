import Foundation.Quantum.QKD.BB84KeyState
import Foundation.Quantum.Mixture

/-! Finite classical-quantum blocks and actual quantum guessing measurements.
The order domination bound is the multiplicative form used in conditional
min-entropy. Its implication for all guessing measurements is proved here;
optimal duality, logarithmic entropy, smoothing and leftover hashing remain
separate obligations. -/
namespace Foundation.Quantum.QKD.Guessing
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X : Type} [Fintype X] {e : Space}

/-- Subnormalized positive blocks, one for each classical value. -/
structure CQ (X : Type) [Fintype X] (e : Space) where
  block : X → Operator e
  positive : ∀ x, (block x).PosSemidef
  normalized : ∑ x, (block x).trace = 1

/-- A complete quantum measurement with one guessed value per outcome. -/
structure Measurement (X : Type) [Fintype X] (e : Space) where
  operator : X → Operator e
  positive : ∀ x, (operator x).PosSemidef
  complete : ∑ x, operator x = 1

def score (ρ : CQ X e) (M : Measurement X e) : ℝ :=
  ∑ x, ((M.operator x * ρ.block x).trace).re

theorem score_nonneg (ρ : CQ X e) (M : Measurement X e) : 0 ≤ score ρ M :=
  Finset.sum_nonneg (fun x _ => (Complex.nonneg_iff.mp (trace_product_nonneg (M.positive x) (ρ.positive x))).1)

/-- The sum of all measurement effects against a normalized state is one. -/
theorem measurement_total (M : Measurement X e) (σ : Density e) :
    ∑ x, (M.operator x * σ.matrix).trace.re = 1 := by
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, M.complete, Matrix.one_mul, σ.normalized]
  rfl

/-- A concrete operator-order certificate, not an arbitrary guessing bound. -/
def Dominated (ρ : CQ X e) (σ : Density e) (q : ℝ) : Prop :=
  ∀ x, (((q : ℂ) • σ.matrix) - ρ.block x).PosSemidef

/-- Positive domination bounds every physical guessing measurement. -/
theorem score_le_of_dominated (ρ : CQ X e) (σ : Density e) (q : ℝ)
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

/-- A guessing bound quantifies over all complete measurements on the quantum system. -/
def GuessBound (ρ : CQ X e) (q : ℝ) : Prop := ∀ M : Measurement X e, score ρ M ≤ q

theorem dominated_guessBound (ρ : CQ X e) (σ : Density e) (q : ℝ)
    (h : Dominated ρ σ q) : GuessBound ρ q := score_le_of_dominated ρ σ q h

/-- A constant guess is a real complete measurement, when X is inhabited. -/
def constantMeasurement [DecidableEq X] (x₀ : X) : Measurement X e where
  operator x := if x = x₀ then 1 else 0
  positive x := by split_ifs; exact Matrix.PosSemidef.one; exact Matrix.PosSemidef.zero
  complete := by simp

theorem score_constantMeasurement [DecidableEq X] (ρ : CQ X e) (x : X) :
    score ρ (constantMeasurement x) = (ρ.block x).trace.re := by
  simp [score, constantMeasurement, ite_mul, apply_ite]

/-- Each block is dominated by the marginal state, giving a universal upper bound one. -/
def marginal (ρ : CQ X e) : Density e where
  matrix := ∑ x, ρ.block x
  positive := Matrix.posSemidef_sum _ (fun x _ => ρ.positive x)
  normalized := by rw [Matrix.trace_sum, ρ.normalized]

theorem dominated_marginal (ρ : CQ X e) : Dominated ρ (marginal ρ) 1 := by
  classical
  intro x
  have hp := Matrix.posSemidef_sum (Finset.univ.erase x) (fun y _ => ρ.positive y)
  have heq : (∑ y ∈ Finset.univ.erase x, ρ.block y) = (∑ y, ρ.block y) - ρ.block x := by
    rw [eq_sub_iff_add_eq]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ x)
  simpa only [heq, marginal, Complex.ofReal_one, one_smul] using hp

theorem score_le_one (ρ : CQ X e) (M : Measurement X e) : score ρ M ≤ 1 :=
  score_le_of_dominated ρ (marginal ρ) 1 (dominated_marginal ρ) M

theorem CQ.nonempty (ρ : CQ X e) : Nonempty X := by
  classical
  by_contra hn
  have : IsEmpty X := not_nonempty_iff.mp hn
  have h := ρ.normalized
  simp at h

/-- Optimal guessing probability is the supremum over actual complete
 quantum measurements, not an external parameter. -/
def guessingProbability (ρ : CQ X e) : ℝ := sSup (Set.range (score ρ))

theorem score_range_nonempty (ρ : CQ X e) : (Set.range (score ρ)).Nonempty := by
  classical
  have : Nonempty X := ρ.nonempty
  exact ⟨_,⟨constantMeasurement (Classical.arbitrary X),rfl⟩⟩

theorem score_range_bddAbove (ρ : CQ X e) : BddAbove (Set.range (score ρ)) :=
  ⟨1,fun _ ⟨M,hM⟩ => hM ▸ score_le_one ρ M⟩

theorem score_le_guessingProbability (ρ : CQ X e) (M : Measurement X e) : score ρ M ≤ guessingProbability ρ :=
  le_csSup (score_range_bddAbove ρ) ⟨M,rfl⟩

theorem guessingProbability_le_iff (ρ : CQ X e) (q : ℝ) : guessingProbability ρ ≤ q ↔ GuessBound ρ q := by
  constructor
  · intro h M
    exact (score_le_guessingProbability ρ M).trans h
  · intro h
    exact csSup_le (score_range_nonempty ρ) (fun _ ⟨M,hM⟩ => hM ▸ h M)

theorem guessingProbability_nonneg (ρ : CQ X e) : 0 ≤ guessingProbability ρ := by
  classical
  have : Nonempty X := ρ.nonempty
  exact (score_nonneg ρ (constantMeasurement (Classical.arbitrary X))).trans (score_le_guessingProbability ρ _)

theorem guessingProbability_le_one (ρ : CQ X e) : guessingProbability ρ ≤ 1 :=
  (guessingProbability_le_iff ρ 1).mpr (fun M => score_le_one ρ M)

theorem guessingProbability_le_of_dominated (ρ : CQ X e) (σ : Density e) (q : ℝ)
    (h : Dominated ρ σ q) : guessingProbability ρ ≤ q :=
  (guessingProbability_le_iff ρ q).mpr (dominated_guessBound ρ σ q h)

end
end Foundation.Quantum.QKD.Guessing
