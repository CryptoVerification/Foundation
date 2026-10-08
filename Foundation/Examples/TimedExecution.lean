import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyTimedExecution

namespace Foundation.Probability.TimedExecution.Examples
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

-- A random first transition chooses a one-step or a two-step path to 2.
-- State 2 is an intermediate boundary: its next real step reaches 3.
noncomputable def step : Nat → PMF Nat
  | 0 => sampleBit.map (fun bit => if bit then 1 else 2)
  | 1 => PMF.pure 2
  | _ => PMF.pure 3

def middle (state : Nat) : Bool := state == 2
def final (state : Nat) : Bool := state == 3

noncomputable def first := Block.stopped step middle 2 0
noncomputable def second (state : Nat) := Block.stopped step final 1 state

theorem first_outcome : first.outcome = sampleBit.map (fun bit => if bit then (2, 2) else (2, 1)) := by
  change ((sampleBit.map (fun bit => if bit then 1 else 2)).bind
    (fun next => (runToBoundary step middle 1 next).map (fun result => (result.1, result.2 + 1)))) = _
  rw [PMF.bind_map]
  conv_rhs => rw [PMF.map]
  congr 1
  funext bit
  cases bit <;> simp [ runToBoundary, middle, step, PMF.pure_bind, PMF.pure_map]

noncomputable def combined := first.compose second 1 (by intro result h; exact Nat.le_refl 1)

example : combined.budget = 3 := rfl

theorem combined_outcome : combined.outcome = sampleBit.map (fun bit => if bit then (3, 3) else (3, 2)) := by
  change (first.outcome.bind _ ) = _
  rw [first_outcome, PMF.bind_map]
  conv_rhs => rw [PMF.map]
  congr 1
  funext bit
  cases bit <;> simp [ second, Block.stopped, runToBoundary,
    final, step, PMF.pure_bind, PMF.pure_map]

-- Apply the general absorbing-endpoint theorem to both random durations.
example (horizon : Nat) (h : 3 ≤ horizon) : eval step horizon 0 = PMF.pure 3 := by
  have ha : ∀ result ∈ combined.outcome.support, step result.1 = PMF.pure result.1 := by
    intro result hr
    rw [combined_outcome, PMF.mem_support_map_iff] at hr
    obtain ⟨bit, _, he⟩ := hr
    subst result
    cases bit <;> rfl
  rw [combined.final_law ha horizon h, combined_outcome, PMF.map_comp]
  have hf : (Prod.fst ∘ (fun bit : Bool => if bit then (3, 3) else (3, 2))) =
      (fun _ : Bool => (3 : Nat)) := by funext bit; cases bit <;> rfl
  rw [hf]
  exact PMF.map_const _ _

-- Exhausting zero fuel does not prove arrival at a boundary.
example : ¬ (Block.stopped step middle 0 0).Completes middle := by
  intro h
  have hh := h (0, 0) (by simp [Block.stopped, runToBoundary])
  contradiction

-- An intermediate boundary must continue with its residual budget.
example : eval step 1 2 = PMF.pure 3 := by simp [eval, step]
example : runToBoundary step middle 1 2 = PMF.pure (2, 0) := by
  simp [runToBoundary, middle]

end Foundation.Probability.TimedExecution.Examples
