import Foundation.Quantum.QKD.Guessing

/-! Public finite information may multiply the optimal quantum guessing
probability by at most its alphabet size. The adversary may choose a different
complete quantum measurement after seeing each public value. This is an
actual counting bound, not a security or entropy premise. -/
namespace Foundation.Quantum.QKD.Guessing
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X L : Type} [Fintype X] [Fintype L] {e : Space}

/-- Forget a classical public register, retaining the quantum side information. -/
def hideLeak (ρ : CQ (X × L) e) : CQ X e where
  block x := ∑ l, ρ.block (x,l)
  positive x := Matrix.posSemidef_sum _ (fun l _ => ρ.positive (x,l))
  normalized := by
    simp only [Matrix.trace_sum]
    simpa only [Fintype.sum_prod_type] using ρ.normalized

/-- The measurement can depend on the publicly disclosed value. -/
def leakScore (ρ : CQ (X × L) e) (M : L → Measurement X e) : ℝ :=
  ∑ l, ∑ x, ((M l).operator x * ρ.block (x,l)).trace.re

theorem leakScore_nonneg (ρ : CQ (X × L) e) (M : L → Measurement X e) : 0 ≤ leakScore ρ M :=
  Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun x _ =>
    (Complex.nonneg_iff.mp (trace_product_nonneg ((M l).positive x) (ρ.positive (x,l)))).1))

/-- A single disclosed block is a positive part of the hidden marginal. -/
theorem hidden_remainder_positive (ρ : CQ (X × L) e) (x : X) (l : L) :
    ((hideLeak ρ).block x - ρ.block (x,l)).PosSemidef := by
  classical
  have hp := Matrix.posSemidef_sum (Finset.univ.erase l) (fun k _ => ρ.positive (x,k))
  have heq : (∑ k ∈ Finset.univ.erase l, ρ.block (x,k)) = (∑ k, ρ.block (x,k)) - ρ.block (x,l) := by
    rw [eq_sub_iff_add_eq]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ l)
  simpa only [heq,hideLeak] using hp

/-- Each public value contributes at most the prior optimal guessing probability. -/
theorem leak_branch_le (ρ : CQ (X × L) e) (M : L → Measurement X e) (l : L) :
    (∑ x, ((M l).operator x * ρ.block (x,l)).trace.re) ≤ guessingProbability (hideLeak ρ) := by
  apply le_trans _ (score_le_guessingProbability (hideLeak ρ) (M l))
  apply Finset.sum_le_sum
  intro x _
  have hh := (Complex.nonneg_iff.mp
    (trace_product_nonneg ((M l).positive x) (hidden_remainder_positive ρ x l))).1
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hh
  linarith

/-- Finite public leakage has an explicit multiplicative cost even when
 it is correlated with both the private classical input and Eve's quantum system. -/
theorem leakScore_le (ρ : CQ (X × L) e) (M : L → Measurement X e) :
    leakScore ρ M ≤ Fintype.card L * guessingProbability (hideLeak ρ) := by
  calc
    leakScore ρ M ≤ ∑ _ : L, guessingProbability (hideLeak ρ) :=
      Finset.sum_le_sum (fun l _ => leak_branch_le ρ M l)
    _ = _ := by simp

def leakedGuessingProbability (ρ : CQ (X × L) e) : ℝ := sSup (Set.range (leakScore ρ))

theorem leak_range_nonempty (ρ : CQ (X × L) e) : (Set.range (leakScore ρ)).Nonempty := by
  classical
  have : Nonempty X := (hideLeak ρ).nonempty
  exact ⟨_,⟨fun _ => constantMeasurement (Classical.arbitrary X),rfl⟩⟩

theorem leak_range_bddAbove (ρ : CQ (X × L) e) : BddAbove (Set.range (leakScore ρ)) :=
  ⟨_,fun _ ⟨M,hM⟩ => hM ▸ leakScore_le ρ M⟩

theorem leakScore_le_optimal (ρ : CQ (X × L) e) (M : L → Measurement X e) :
    leakScore ρ M ≤ leakedGuessingProbability ρ := le_csSup (leak_range_bddAbove ρ) ⟨M,rfl⟩

/-- The optimal guessing probability after public disclosure satisfies the same bound. -/
theorem leakage_chain (ρ : CQ (X × L) e) :
    leakedGuessingProbability ρ ≤ Fintype.card L * guessingProbability (hideLeak ρ) :=
  csSup_le (leak_range_nonempty ρ) (fun _ ⟨M,hM⟩ => hM ▸ leakScore_le ρ M)

/-- Operator domination before disclosure gives an explicit bound after disclosure. -/
theorem leakage_of_dominated (ρ : CQ (X × L) e) (σ : Density e) (q : ℝ)
    (h : Dominated (hideLeak ρ) σ q) : leakedGuessingProbability ρ ≤ Fintype.card L * q :=
  (leakage_chain ρ).trans (mul_le_mul_of_nonneg_left
    (guessingProbability_le_of_dominated _ σ q h) (Nat.cast_nonneg _))

end
end Foundation.Quantum.QKD.Guessing
