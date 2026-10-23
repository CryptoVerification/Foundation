import Mathlib.Tactic

/-! A finite, mixed-scope rewinding benchmark.

The transition system models a fixed guessing policy, not all cryptographic
simulators. General history compression, almost-sure absorption, and the
Schnorr embedding are discussed separately in the research note. The local
arithmetic and the strict affine-certificate gap are checked here.
-/

namespace Foundation.Examples.CrossingRewindingCost

inductive State
  | empty | a | b | ab | done
  deriving DecidableEq

@[simp] theorem empty_ne_done : State.empty ≠ State.done := by decide
@[simp] theorem a_ne_done : State.a ≠ State.done := by decide
@[simp] theorem b_ne_done : State.b ≠ State.done := by decide
@[simp] theorem ab_ne_done : State.ab ≠ State.done := by decide

def success : State → State
  | .empty => .a
  | .a => .ab
  | .b => .ab
  | .ab => .done
  | .done => .done

def failure : State → State
  | .empty => .empty
  | .a => .empty
  | .b => .empty
  | .ab => .b
  | .done => .done

def bits : State → ℚ × ℚ × ℚ
  | .empty => (0, 0, 0)
  | .a => (1, 0, 0)
  | .b => (0, 1, 0)
  | .ab => (1, 1, 0)
  | .done => (1, 1, 1)

def affine (a b c : ℚ) (s : State) : ℚ :=
  a * (bits s).1 + b * (bits s).2.1 + c * (bits s).2.2

def potential (s : State) : ℚ :=
  2 * (bits s).1 + 2 * (bits s).2.1 + 6 * (bits s).2.2 +
    2 * (bits s).1 * (bits s).2.1

def drift (f : State → ℚ) (s : State) : ℚ :=
  (f (success s) + f (failure s)) / 2 - f s

theorem potential_nonnegative (s : State) : 0 ≤ potential s := by
  cases s <;> norm_num [potential, bits]

theorem potential_empty : potential .empty = 0 := by norm_num [potential, bits]

theorem potential_done : potential .done = 12 := by norm_num [potential, bits]

theorem exact_local_drift (s : State) (active : s ≠ .done) :
    drift potential s = 1 := by
  cases s <;> norm_num [drift, potential, success, failure, bits] at *

/-- This is a limitation of affine potentials on these state coordinates,
not a limitation of ordinary categories or of arbitrary shared proofs. -/
theorem affine_certificate_upper (a b c : ℚ)
    (certificate : ∀ s, s ≠ .done → drift (affine a b c) s ≤ 1) :
    affine a b c .done ≤ 10 := by
  have first := certificate .empty (by decide)
  have second := certificate .a (by decide)
  have third := certificate .ab (by decide)
  norm_num [drift, affine, success, failure, bits] at first second third ⊢
  linarith

theorem affine_ten_attained (s : State) (active : s ≠ .done) :
    drift (affine 2 4 4) s ≤ 1 := by
  cases s <;> norm_num [drift, affine, success, failure, bits] at *

def expectedCalls : ℕ → State → ℚ
  | 0, _ => 0
  | n + 1, s => if s = .done then 0 else
      1 + (expectedCalls n (success s) + expectedCalls n (failure s)) / 2

def terminalPotential : ℕ → State → ℚ
  | 0, s => potential s
  | n + 1, s => if s = .done then potential .done else
      (terminalPotential n (success s) + terminalPotential n (failure s)) / 2

def completed : ℕ → State → ℚ
  | 0, s => if s = .done then 1 else 0
  | n + 1, s => if s = .done then 1 else
      (completed n (success s) + completed n (failure s)) / 2

theorem stopped_cost_identity (n : ℕ) (s : State) :
    expectedCalls n s = terminalPotential n s - potential s := by
  induction n generalizing s with
  | zero => simp [expectedCalls, terminalPotential]
  | succ n ih =>
    by_cases active : s = .done
    · simp [expectedCalls, terminalPotential, active]
    · have localDrift := exact_local_drift s active
      simp only [expectedCalls, terminalPotential, if_neg active]
      rw [ih (success s), ih (failure s)]
      dsimp [drift] at localDrift
      linarith

theorem terminal_lower (n : ℕ) (s : State) :
    12 * completed n s ≤ terminalPotential n s := by
  induction n generalizing s with
  | zero =>
    cases s <;> norm_num [completed, terminalPotential, potential, bits]
  | succ n ih =>
    by_cases active : s = .done
    · norm_num [completed, terminalPotential, active, potential, bits]
    · have one := ih (success s)
      have two := ih (failure s)
      simp only [completed, terminalPotential, if_neg active]
      linarith

theorem finite_success_bound (n : ℕ) :
    12 * completed n .empty ≤ expectedCalls n .empty := by
  have lower := terminal_lower n .empty
  have identity := stopped_cost_identity n .empty
  rw [potential_empty] at identity
  linarith

theorem three_step_completion (s : State) : 1 / 8 ≤ completed 3 s := by
  cases s <;> norm_num [completed, success, failure]

/-- For prefix unions, every triple has an excluded singleton pattern.
This relation reduces a cubic monomial to pair interactions. -/
theorem cubic_reduction (x a b : ℚ) (covered : x * (1 - a) * (1 - b) = 0) :
    x * a * b = x * a + x * b - x := by
  nlinarith [covered]

end Foundation.Examples.CrossingRewindingCost
