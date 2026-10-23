import Mathlib.Tactic

/-! Arithmetic certificates for a restricted nested rewinding model.

Entries are expected fresh-query and accepted-opening counts, outermost first.
`Linked` requires an injection from fresh parent queries to child completions.
Neither that injection nor the fair-coin inequality is asserted for arbitrary
cryptographic simulators. Those operational and computational bridges remain
separate proof obligations. This file does not establish novelty or a need for
infinity-categories. -/

namespace Foundation.Examples.NestedRewindingCost

def cost : ℕ → ℚ
  | 0 => 0
  | n + 1 => 2 + 2 * cost n

theorem cost_nonnegative (n : ℕ) : 0 ≤ cost n := by
  induction n with
  | zero => simp [cost]
  | succ n ih => simp only [cost]; linarith

theorem cost_closed (n : ℕ) : cost n + 2 = 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num [cost]
  | succ n ih => rw [cost, pow_succ]; linarith

abbrev Counts := ℚ × ℚ

def queries : List Counts → ℚ
  | [] => 0
  | (q, _) :: rest => q + queries rest

def accepted : List Counts → ℚ
  | [] => 0
  | (_, r) :: _ => r

def Linked : List Counts → Prop
  | [] => True
  | (q, _) :: rest => (rest ≠ [] → q ≤ accepted rest) ∧ Linked rest

def Fair : List Counts → Prop
  | [] => True
  | (q, r) :: rest => 2 * r ≤ q ∧ Fair rest

/-- Deviations are signed: negative deviations may strengthen the bound. -/
def defect : List Counts → ℚ
  | [] => 0
  | (q, r) :: rest => (cost rest.length + 1) * (2 * r - q) + defect rest

/-- Local flow constraints suffice for the corrected global cost bound. -/
theorem corrected_bound (ledger : List Counts) (linked : Linked ledger) :
    cost ledger.length * accepted ledger ≤ queries ledger + defect ledger := by
  induction ledger with
  | nil => simp [cost, accepted, queries, defect]
  | cons entry rest ih =>
    rcases entry with ⟨q, r⟩
    have tailBound := ih linked.2
    cases rest with
    | nil => norm_num [cost, accepted, queries, defect]
    | cons next rest =>
      have flow := linked.1 (by simp)
      have scaled := mul_le_mul_of_nonneg_left flow
        (cost_nonnegative ((next :: rest).length))
      simp only [List.length_cons, accepted, queries, defect, cost] at *
      nlinarith

theorem defect_nonpositive (ledger : List Counts) (fair : Fair ledger) :
    defect ledger ≤ 0 := by
  induction ledger with
  | nil => simp [defect]
  | cons entry rest ih =>
    rcases entry with ⟨q, r⟩
    have tailBound := ih fair.2
    have weightNonnegative : 0 ≤ cost rest.length + 1 := by
      have := cost_nonnegative rest.length
      linarith
    have localBound := mul_nonpos_of_nonneg_of_nonpos weightNonnegative
      (sub_nonpos.mpr fair.1)
    simp only [defect]
    linarith

theorem fair_cost_bound (ledger : List Counts) (linked : Linked ledger)
    (fair : Fair ledger) :
    cost ledger.length * accepted ledger ≤ queries ledger := by
  have corrected := corrected_bound ledger linked
  have nonpositive := defect_nonpositive ledger fair
  linarith

/-- Success probability is bounded by the expected number of root completions.
The hypotheses must be discharged by the caller's actual stochastic semantics. -/
theorem success_cost_bound (ledger : List Counts) (linked : Linked ledger)
    (fair : Fair ledger) (successProbability : ℚ)
    (success : successProbability ≤ accepted ledger) :
    cost ledger.length * successProbability ≤ queries ledger := by
  exact (mul_le_mul_of_nonneg_left success
    (cost_nonnegative ledger.length)).trans (fair_cost_bound ledger linked fair)

/-- Arithmetic used by a two-continuation extraction argument. Constructing
those continuations with the required conditional laws is not proved here. -/
theorem two_branch_excess (a b : ℚ) (aUpper : a ≤ 1) (bUpper : b ≤ 1) :
    a + b - 1 ≤ a * b := by
  have := mul_nonneg (sub_nonneg.mpr aUpper) (sub_nonneg.mpr bUpper)
  nlinarith

/-- A bound on the weighted local deviations transfers to success probability.
This is conditional arithmetic, not a cryptographic reduction theorem. -/
theorem bounded_defect_transfer (ledger : List Counts) (linked : Linked ledger)
    (p q advantage : ℚ) (success : p ≤ accepted ledger)
    (defectBound : defect ledger ≤ q * (cost ledger.length / 2) * advantage) :
    cost ledger.length * p ≤
      queries ledger + q * (cost ledger.length / 2) * advantage := by
  have rootBound := mul_le_mul_of_nonneg_left success
    (cost_nonnegative ledger.length)
  have corrected := corrected_bound ledger linked
  linarith

/-- The recursive guessing strategy has a matching arithmetic cost profile. -/
def optimalLedger : ℕ → List Counts
  | 0 => []
  | n + 1 => (2, 1) :: (optimalLedger n).map (fun p => (2 * p.1, 2 * p.2))

theorem queries_map_scale (ledger : List Counts) (a : ℚ) :
    queries (ledger.map (fun p => (a * p.1, a * p.2))) = a * queries ledger := by
  induction ledger with
  | nil => simp [queries]
  | cons entry rest ih => simp [queries, ih, mul_add]

theorem optimal_ledger_cost (n : ℕ) : queries (optimalLedger n) = cost n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [optimalLedger, queries, queries_map_scale, ih, cost]

end Foundation.Examples.NestedRewindingCost
