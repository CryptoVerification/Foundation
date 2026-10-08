import Foundation.Crypto.Semantics.BoundaryStability

/-! Exact first-arrival time from a local countdown. The boundary need
not be absorbing: subsequent execution may continue after the handoff.
Branching and the complete physical endpoint distribution are preserved. -/
namespace Foundation.Probability.TimedExecution
universe u
variable {State : Type u}

theorem runToBoundary_countdown_joint (step : State → PMF State)
    (boundary : State → Bool) (remaining : State → Nat)
    (zero : ∀ state, boundary state = true ↔ remaining state = 0)
    (decreases : ∀ state, boundary state = false →
      ∀ next ∈ (step state).support, remaining next + 1 = remaining state)
    (start : State) :
    runToBoundary step boundary (remaining start) start =
      (eval step (remaining start) start).map (fun state => (state, remaining start)) := by
  generalize hn : remaining start = count
  induction count generalizing start with
  | zero => simp [runToBoundary, eval, PMF.pure_map]
  | succ count ih =>
      have hb : boundary start = false := by
        cases h : boundary start
        · rfl
        · have := (zero start).1 h; omega
      simp only [runToBoundary, hb, Bool.false_eq_true, ↓reduceIte, eval,
        PMF.map_bind]
      rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext next hNext
      have hnNext : remaining next = count := by
        have := decreases start hb next hNext
        omega
      rw [ih next hnNext, PMF.map_comp]
      rfl

end Foundation.Probability.TimedExecution
