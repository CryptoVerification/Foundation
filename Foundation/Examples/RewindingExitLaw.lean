import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Finite exit-kernel normalization. This is the algebra of a regenerative
restart argument, not an operational semantics or a generic ZK theorem. -/

namespace Foundation.Examples.RewindingExitLaw

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

def exitTotal (proposal : X → ℚ) (kernel : X → Y → ℚ) : ℚ :=
  ∑ x, ∑ y, proposal x * kernel x y

def exitLaw (proposal : X → ℚ) (kernel : X → Y → ℚ) (x : X) (y : Y) : ℚ :=
  proposal x * kernel x y / exitTotal proposal kernel

theorem balanced_total (proposal target survive : X → ℚ) (kernel : X → Y → ℚ)
    (scale : ℚ) (targetMass : ∑ x, target x = 1)
    (rowMass : ∀ x, ∑ y, kernel x y = survive x)
    (balance : ∀ x, proposal x * survive x = scale * target x) :
    exitTotal proposal kernel = scale := by
  unfold exitTotal
  calc
    _ = ∑ x, proposal x * survive x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum, rowMass]
    _ = ∑ x, scale * target x := by
      apply Finset.sum_congr rfl
      intro x _
      exact balance x
    _ = scale := by rw [← Finset.mul_sum, targetMass, mul_one]

/-- Local normalized laws compose correctly here only with the additional
mass-balance equation. Nonnegative probabilities and operational restart
behavior must be supplied separately when applying this algebra. -/
theorem balanced_joint_law (proposal target survive : X → ℚ)
    (conditional : X → Y → ℚ) (scale : ℚ)
    (targetMass : ∑ x, target x = 1)
    (conditionalMass : ∀ x, ∑ y, conditional x y = 1)
    (balance : ∀ x, proposal x * survive x = scale * target x)
    (nonzero : scale ≠ 0) (x : X) (y : Y) :
    exitLaw proposal (fun x y => survive x * conditional x y) x y =
      target x * conditional x y := by
  have total := balanced_total proposal target survive
    (fun x y => survive x * conditional x y) scale targetMass
    (by intro x; rw [← Finset.mul_sum, conditionalMass, mul_one]) balance
  unfold exitLaw
  rw [total, ← mul_assoc, balance]
  field_simp

/-- With an unchanged proposal, exact preservation of a positive-mass context
requires its survival mass to equal the common normalization constant. -/
theorem unchanged_proposal_requires_constant_mass (target survive total : ℚ)
    (targetNonzero : target ≠ 0) (totalNonzero : total ≠ 0)
    (preserved : target * survive / total = target) : survive = total := by
  have equation := (div_eq_iff totalNonzero).mp preserved
  exact mul_left_cancel₀ targetNonzero equation

theorem biased_tag_probability :
    ((1 / 2 : ℚ) * (1 / 2)) /
      ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 3)) = 3 / 5 := by norm_num

theorem reweighted_tag_probability :
    ((2 / 5 : ℚ) * (1 / 2)) /
      ((2 / 5) * (1 / 2) + (3 / 5) * (1 / 3)) = 1 / 2 := by norm_num

theorem biased_policy_cost :
    ((1 / 2 : ℚ) * (5 / 2) + (1 / 2) * 2) /
      ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 3)) = 27 / 5 := by norm_num

theorem reweighted_policy_cost :
    ((2 / 5 : ℚ) * (5 / 2) + (3 / 5) * 2) /
      ((2 / 5) * (1 / 2) + (3 / 5) * (1 / 3)) = 11 / 2 := by norm_num

end Foundation.Examples.RewindingExitLaw
