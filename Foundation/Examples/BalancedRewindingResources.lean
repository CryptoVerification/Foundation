import Foundation.Examples.LocalRewindingCompiler

/-! Resource arithmetic for balanced two-session rewinding.

A private permutation of an independent uniform tag makes each first-challenge
class have equal mass, even when the permutation depends on group commitments.
Full stochastic execution and the Schnorr transcript law are proved separately.
Snapshot and restoration costs are explicit: preparation savings alone do not
establish a wall-clock improvement or optimality among simulators.
-/

namespace Foundation.Examples.BalancedRewindingResources

open scoped BigOperators
open Foundation.Examples.LocalRewindingCompiler

theorem permutation_fiber_count {C : Type*} [Fintype C] [DecidableEq C]
    (permutation : Equiv.Perm C) (challenge : C) :
    (∑ tag, if permutation tag = challenge then (1 : ℚ) else 0) = 1 := by
  simp [← Equiv.eq_symm_apply]

theorem permutation_fiber_mass {C : Type*} [Fintype C] [DecidableEq C]
    (permutation : Equiv.Perm C) (challenge : C) :
    (∑ tag, if permutation tag = challenge then 1 / (Fintype.card C : ℚ) else 0) =
      1 / (Fintype.card C : ℚ) := by
  have pointwise (tag : C) :
      (if permutation tag = challenge then 1 / (Fintype.card C : ℚ) else 0) =
      (if permutation tag = challenge then (1 : ℚ) else 0) / (Fintype.card C : ℚ) := by
    split_ifs <;> simp
  simp_rw [pointwise]
  rw [← Finset.sum_div, permutation_fiber_count]

theorem balanced_denominator (k p : ℚ) (kNonzero : k ≠ 0) :
    retryDenominator p (1 / k) = (k - 1 + p) / k := by
  unfold retryDenominator
  field_simp
  ring

theorem balanced_exit_normalization (law k p : ℚ)
    (kNonzero : k ≠ 0) (pNonzero : p ≠ 0) (weightNonzero : k - 1 + p ≠ 0) :
    (law * p / (k * retryDenominator p (1 / k))) / (p / (k - 1 + p)) = law := by
  rw [balanced_denominator k p kNonzero]
  field_simp

theorem expected_a_preparations (k p : ℚ) (pNonzero : p ≠ 0)
    (weightNonzero : k - 1 + p ≠ 0) :
    1 / (p / (k - 1 + p)) = (k - 1 + p) / p := by
  field_simp

theorem expected_b_preparations (k p : ℚ) (kNonzero : k ≠ 0)
    (pNonzero : p ≠ 0) (weightNonzero : k - 1 + p ≠ 0) :
    (1 / retryDenominator p (1 / k)) / (p / (k - 1 + p)) = k / p := by
  rw [balanced_denominator k p kNonzero]
  field_simp

theorem preparation_saving (k p : ℚ) (pNonzero : p ≠ 0) :
    k / p - (k - 1 + p) / p = (1 - p) / p := by
  field_simp
  ring

def fullCost (k p a b qa qb root : ℚ) : ℚ :=
  (k / p) * (a + b + qa) + (1 / p) * qb + (k / p - 1) * root

def reuseCost (k p a b qa qb root restoreB snapshot : ℚ) : ℚ :=
  ((k - 1 + p) / p) * (a + snapshot) + (k / p) * (b + qa) +
    (1 / p) * qb + ((k - 1) / p) * root + ((1 - p) / p) * restoreB

theorem weighted_cost_gap (k p a b qa qb root restoreB snapshot : ℚ)
    (pNonzero : p ≠ 0) :
    fullCost k p a b qa qb root - reuseCost k p a b qa qb root restoreB snapshot =
      ((1 - p) * (a + root - restoreB) - snapshot * (k - 1 + p)) / p := by
  unfold fullCost reuseCost
  field_simp
  ring

theorem improvement_iff (k p a b qa qb root restoreB snapshot : ℚ)
    (pPositive : 0 < p) :
    reuseCost k p a b qa qb root restoreB snapshot < fullCost k p a b qa qb root ↔
      snapshot * (k - 1 + p) < (1 - p) * (a + root - restoreB) := by
  have gap := weighted_cost_gap k p a b qa qb root restoreB snapshot (ne_of_gt pPositive)
  have positive_iff := div_pos_iff_of_pos_right pPositive
    (a := (1 - p) * (a + root - restoreB) - snapshot * (k - 1 + p))
  constructor
  · intro better
    have positive : 0 < fullCost k p a b qa qb root -
        reuseCost k p a b qa qb root restoreB snapshot := sub_pos.mpr better
    rw [gap] at positive
    have numerator := positive_iff.mp positive
    linarith
  · intro bound
    have numerator : 0 < (1 - p) * (a + root - restoreB) - snapshot * (k - 1 + p) := by
      linarith
    have positive := positive_iff.mpr numerator
    rw [← gap] at positive
    exact sub_pos.mp positive

theorem binary_resources :
    ((2 - 1 + (1 / 2 : ℚ)) / (1 / 2) = 3) ∧
    ((2 : ℚ) / (1 / 2) = 4) ∧
    ((2 + 1 : ℚ) / (1 / 2) = 6) := by
  norm_num

theorem binary_equal_restore_gap (a b qa qb restore snapshot : ℚ) :
    fullCost 2 (1 / 2) a b qa qb restore -
      reuseCost 2 (1 / 2) a b qa qb restore restore snapshot = a - 3 * snapshot := by
  unfold fullCost reuseCost
  ring

end Foundation.Examples.BalancedRewindingResources
