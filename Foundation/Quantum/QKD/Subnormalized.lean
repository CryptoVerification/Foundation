import Foundation.Quantum.QKD.GuessPublic
import Foundation.Quantum.QKD.GuessProcessing

/-! Subnormalized classical-quantum states. Branches are retained with their
original weight, so no division by an acceptance probability is performed.
Optimal guessing is defined for nonempty classical alphabets, including all
raw-key types used by BB84. The zero state and zero-probability branches exist. -/
namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
open scoped ComplexOrder
open Guessing
set_option backward.isDefEq.respectTransparency false
variable {X : Type} [Fintype X] {e : Space}

structure State (X : Type) [Fintype X] (e : Space) where
  block : X → Operator e
  positive : ∀ x, (block x).PosSemidef
  bounded : (∑ x, (block x).trace.re) ≤ 1

@[ext] theorem State.ext {ρ σ : State X e} (h : ρ.block = σ.block) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

def mass (ρ : State X e) : ℝ := ∑ x, (ρ.block x).trace.re

theorem mass_nonneg (ρ : State X e) : 0 ≤ mass ρ :=
  Finset.sum_nonneg (fun x _ => (Complex.nonneg_iff.mp (ρ.positive x).trace_nonneg).1)

theorem mass_le_one (ρ : State X e) : mass ρ ≤ 1 := ρ.bounded

def ofCQ (ρ : CQ X e) : State X e where
  block := ρ.block
  positive := ρ.positive
  bounded := by rw [← Complex.re_sum, ρ.normalized]; norm_num

theorem mass_ofCQ (ρ : CQ X e) : mass (ofCQ ρ) = 1 := by
  unfold mass ofCQ
  rw [← Complex.re_sum, ρ.normalized]
  rfl

/-- Restrict to an event, with its original subnormalized weight. -/
def restrict (ρ : State X e) (P : X → Prop) [DecidablePred P] : State X e where
  block x := if P x then ρ.block x else 0
  positive x := by split_ifs; exact ρ.positive x; exact Matrix.PosSemidef.zero
  bounded := by
    apply le_trans _ ρ.bounded
    apply Finset.sum_le_sum
    intro x _
    split_ifs
    · rfl
    · simpa using (Complex.nonneg_iff.mp (ρ.positive x).trace_nonneg).1

theorem mass_restrict (ρ : State X e) (P : X → Prop) [DecidablePred P] :
    mass (restrict ρ P) = ∑ x, if P x then (ρ.block x).trace.re else 0 := by
  simp [mass, restrict, apply_ite]

theorem mass_partition (ρ : State X e) (P : X → Prop) [DecidablePred P] :
    mass (restrict ρ P) + mass (restrict ρ (fun x => ¬ P x)) = mass ρ := by
  rw [mass_restrict, mass_restrict, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : P x <;> simp [h]

def score (ρ : State X e) (M : Measurement X e) : ℝ :=
  ∑ x, (M.operator x * ρ.block x).trace.re

theorem score_constantMeasurement [DecidableEq X] (ρ : State X e) (x : X) :
    score ρ (constantMeasurement x) = (ρ.block x).trace.re := by
  simp [score, constantMeasurement, ite_mul, apply_ite]

theorem score_nonneg (ρ : State X e) (M : Measurement X e) : 0 ≤ score ρ M :=
  Finset.sum_nonneg (fun x _ =>
    (Complex.nonneg_iff.mp (trace_product_nonneg (M.positive x) (ρ.positive x))).1)

/-- Every complete measurement effect is at most the identity. -/
theorem measurement_complement (M : Measurement X e) (x : X) : (1 - M.operator x).PosSemidef := by
  classical
  have hp := Matrix.posSemidef_sum (Finset.univ.erase x) (fun y _ => M.positive y)
  have heq : (∑ y ∈ Finset.univ.erase x, M.operator y) = 1 - M.operator x := by
    rw [eq_sub_iff_add_eq, ← M.complete]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ x)
  simpa only [heq] using hp

/-- Success is weighted by the probability of this branch. -/
theorem score_le_mass (ρ : State X e) (M : Measurement X e) : score ρ M ≤ mass ρ := by
  apply Finset.sum_le_sum
  intro x _
  have h := (Complex.nonneg_iff.mp
    (trace_product_nonneg (measurement_complement M x) (ρ.positive x))).1
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at h
  linarith

variable [Nonempty X]

def probability (ρ : State X e) : ℝ := sSup (Set.range (score ρ))

theorem range_nonempty (ρ : State X e) : (Set.range (score ρ)).Nonempty := by
  classical
  exact ⟨_,⟨constantMeasurement (Classical.arbitrary X),rfl⟩⟩

omit [Nonempty X] in
theorem range_bddAbove (ρ : State X e) : BddAbove (Set.range (score ρ)) :=
  ⟨mass ρ,fun _ ⟨M,hM⟩ => hM ▸ score_le_mass ρ M⟩

omit [Nonempty X] in
theorem score_le_probability (ρ : State X e) (M : Measurement X e) : score ρ M ≤ probability ρ :=
  le_csSup (range_bddAbove ρ) ⟨M,rfl⟩

theorem probability_nonneg (ρ : State X e) : 0 ≤ probability ρ := by
  classical
  exact (score_nonneg ρ (constantMeasurement (Classical.arbitrary X))).trans (score_le_probability ρ _)

theorem probability_le_mass (ρ : State X e) : probability ρ ≤ mass ρ :=
  csSup_le (range_nonempty ρ) (fun _ ⟨M,hM⟩ => hM ▸ score_le_mass ρ M)

theorem probability_zero_mass (ρ : State X e) (h : mass ρ = 0) : probability ρ = 0 :=
  le_antisymm (h ▸ probability_le_mass ρ) (probability_nonneg ρ)

omit [Nonempty X] in
theorem probability_ofCQ (ρ : CQ X e) : probability (ofCQ ρ) = guessingProbability ρ := rfl

end
end Foundation.Quantum.QKD.Subnormalized
