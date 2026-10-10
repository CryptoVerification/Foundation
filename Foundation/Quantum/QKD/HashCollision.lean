import Foundation.Quantum.QKD.SubnormalizedRelabel
import Foundation.Quantum.RecordObservation

/-! The operator collision calculation underlying quantum leftover hashing.
No trace-one condition is needed: positive blocks may already be weighted by
acceptance. A general PMF is allowed, with pairwise collision bounds checked
against that same distribution of the fresh seed. -/
namespace Foundation.Quantum.QKD.Collision
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] {e : Space}

/-- Quantum block at a hashed classical value. -/
def grouped [DecidableEq Y] (B : X → Operator e) (h : X → Y) (y : Y) : Operator e :=
  ∑ x, if h x = y then B x else 0

def pair (B : X → Operator e) (x x' : X) : ℝ := (B x * B x').trace.re

def input (B : X → Operator e) : ℝ := ∑ x, pair B x x

def total (B : X → Operator e) : ℝ := ((∑ x, B x) * (∑ x, B x)).trace.re

def collision (p : PMF S) (h : S → X → Y) (x x' : X) : ℝ :=
  (Foundation.Probability.eventProb p (fun s => h s x = h s x')).toReal

def output [DecidableEq Y] (p : PMF S) (h : S → X → Y) (B : X → Operator e) : ℝ :=
  ∑ s, (p s).toReal * ∑ y, ((grouped B (h s) y) * (grouped B (h s) y)).trace.re

omit [Fintype X] in
theorem pair_nonneg (B : X → Operator e) (hB : ∀ x, (B x).PosSemidef) (x x' : X) :
    0 ≤ pair B x x' := (Complex.nonneg_iff.mp (trace_product_nonneg (hB x) (hB x'))).1

theorem total_expansion (B : X → Operator e) : total B = ∑ x, ∑ x', pair B x x' := by
  simp only [total, pair, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  rw [Finset.sum_comm]

/-- The cross terms contain full quantum matrix products, not products of
classical probabilities. Hash equality determines exactly which survive. -/
theorem grouped_expansion [DecidableEq Y] (B : X → Operator e) (h : X → Y) :
    (∑ y, ((grouped B h y) * (grouped B h y)).trace.re) =
      ∑ x, ∑ x', if h x = h x' then pair B x x' else 0 := by
  simp only [grouped, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum,
    ite_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re,
    apply_ite]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro x' _
  by_cases hh : h x = h x'
  · simp only [hh, ite_true, pair]
    rw [Matrix.trace_mul_comm]
  · simp only [hh, Ne.symm hh, ite_false]

/-- Average operator collision is the exact pairwise collision expansion. -/
theorem output_expansion [DecidableEq Y] (p : PMF S) (h : S → X → Y) (B : X → Operator e) :
    output p h B = ∑ x, ∑ x', collision p h x x' * pair B x x' := by
  unfold output
  simp_rw [grouped_expansion]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x' _
  rw [collision, eventProb_toReal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : h s x = h s x' <;> simp [hs]

omit [Fintype X] [Fintype Y] in
theorem collision_self (p : PMF S) (h : S → X → Y) (x : X) : collision p h x x = 1 := by
  classical
  rw [collision, eventProb_toReal]
  simpa using Density.probability_weights p

/-- Sharp diagonal/off-diagonal collision bound for an almost universal family. -/
theorem output_le [DecidableEq Y] (p : PMF S) (h : S → X → Y) (B : X → Operator e)
    (hB : ∀ x, (B x).PosSemidef) (δ : ℝ)
    (hδ : ∀ x x', x ≠ x' → collision p h x x' ≤ δ) :
    output p h B ≤ (1-δ) * input B + δ * total B := by
  classical
  rw [output_expansion, total_expansion]
  have hrow (x : X) :
      (∑ x', collision p h x x' * pair B x x') ≤
        (1-δ) * pair B x x + δ * ∑ x', pair B x x' := by
    calc
      _ ≤ ∑ x', (if x' = x then 1 else δ) * pair B x x' := by
        apply Finset.sum_le_sum
        intro x' _
        by_cases hx : x' = x
        · subst x'
          simp [collision_self]
        · simp only [hx, ite_false]
          exact mul_le_mul_of_nonneg_right (hδ x x' (Ne.symm hx)) (pair_nonneg B hB x x')
      _ = _ := by
        have heq (x' : X) : (if x' = x then 1 else δ) * pair B x x' =
            (if x' = x then (1-δ) * pair B x x' else 0) + δ * pair B x x' := by
          by_cases hx : x' = x <;> simp [hx, sub_mul]
        simp_rw [heq]
        rw [Finset.sum_add_distrib]
        simp [Finset.mul_sum]
  calc
    _ ≤ ∑ x, ((1-δ) * pair B x x + δ * ∑ x', pair B x x') := Finset.sum_le_sum (fun x _ => hrow x)
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, input]

end
end Foundation.Quantum.QKD.Collision
