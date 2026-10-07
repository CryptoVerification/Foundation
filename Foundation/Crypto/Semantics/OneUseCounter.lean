import Foundation.Crypto.Semantics.Invariant
import Foundation.Crypto.Semantics.Simulation

/-! Ghost counting of a one-use event in any probabilistic machine. The
counter is proof instrumentation, not a hidden runtime operation or resource. -/
namespace Foundation.Probability.TimedExecution.OneUseCounter
universe u
variable {State : Type u}

noncomputable def countedStep (step : State → PMF State) (event : State → Bool)
    (start : State × Nat) : PMF (State × Nat) :=
  (step start.1).map (fun next => (next, start.2 + if event start.1 then 1 else 0))

def allowance (used : Bool) : Nat := if used then 0 else 1

theorem preserves (step : State → PMF State) (used event : State → Bool)
    (hEvent : ∀ start, event start = true → used start = false)
    (hStatus : ∀ start next, next ∈ (step start).support →
      used next = (used start || event start)) :
    Preserves (countedStep step event) (fun frame => frame.2 + allowance (used frame.1) ≤ 1) := by
  intro start hStart result hResult
  rw [countedStep, PMF.mem_support_map_iff] at hResult
  obtain ⟨next, hNext, he⟩ := hResult
  subst result
  have hn := hStatus start.1 next hNext
  cases hu : used start.1 <;> cases hv : event start.1 <;>
    simp_all [allowance]

theorem at_most_one (step : State → PMF State) (used event : State → Bool)
    (hEvent : ∀ start, event start = true → used start = false)
    (hStatus : ∀ start next, next ∈ (step start).support →
      used next = (used start || event start))
    (fuel : Nat) (start : State) (result : State × Nat)
    (hResult : result ∈ (eval (countedStep step event) fuel (start, 0)).support) : result.2 ≤ 1 := by
  have h := eval_preserves (countedStep step event)
    (fun frame => frame.2 + allowance (used frame.1) ≤ 1)
    (preserves step used event hEvent hStatus) fuel (start, 0) result
    (by cases used start <;> simp [allowance]) hResult
  omega

/-- The counter does not alter the actual machine's marginal execution. -/
theorem marginal (step : State → PMF State) (event : State → Bool)
    (fuel : Nat) (start : State × Nat) :
    (eval (countedStep step event) fuel start).map Prod.fst = eval step fuel start.1 := by
  exact eval_map (countedStep step event) step Prod.fst
    (fun frame => by
      simp only [countedStep, PMF.map_comp, Function.comp_def]
      exact PMF.map_id _) fuel start

end Foundation.Probability.TimedExecution.OneUseCounter
