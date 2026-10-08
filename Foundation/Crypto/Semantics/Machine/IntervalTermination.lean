import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.ProcedureIntervalTermination

/-! The ordinary finite-code machine stopping certificate can be reused
after dividing execution into positive-fuel intervals. Random instructions,
full physical tapes and the original program counter remain unchanged. -/
namespace Machine.IntervalTermination
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

theorem absorbing (code : Program) (state : Configuration) (h : state.halted = true) :
    stepPMF code state = PMF.pure state := by
  simp [stepPMF, next, h]

noncomputable def interval (code : Program) (fuel : Nat) :=
  TimedExecution.Procedure.interval (stepPMF code) (stepPMF code)
    Configuration.halted Configuration.halted id (fun _ => rfl)
    (fun _ _ => (PMF.map_id _).symm) fuel

/-- Import the usual finite native execution proof directly. Stopping
of the new interval iteration is derived, rather than separately assumed. -/
theorem stops (code : Program) (fuel : Nat) (hFuel : 0 < fuel) (start : Configuration)
    (bound rounds : Nat) (hRounds : bound ≤ rounds)
    (hStop : ∀ final ∈ (evalConfigWithin code start bound).support, final.halted = true)
    (final : Configuration)
    (hFinal : final ∈ (TimedExecution.eval (interval code fuel).semantics rounds start).support) :
    final.halted = true :=
  TimedExecution.Procedure.interval_stops_of_source (stepPMF code) (stepPMF code)
    Configuration.halted Configuration.halted id (fun _ => rfl) (fun _ _ => (PMF.map_id _).symm)
    (absorbing code) (absorbing code) fuel hFuel start bound rounds hRounds
    (fun final hs => hStop final (by rwa [timed_eval_eq] at hs)) final hFinal

/-- The distribution after all interval rounds equals the distribution
of the original finite code at any horizon above the composed budget. -/
theorem run (code : Program) (fuel : Nat) (hFuel : 0 < fuel) (start : Configuration)
    (bound rounds : Nat) (hRounds : bound ≤ rounds)
    (hStop : ∀ final ∈ (evalConfigWithin code start bound).support, final.halted = true)
    (horizon : Nat) (hBudget : rounds * fuel ≤ horizon) :
    evalConfigWithin code start horizon = TimedExecution.eval (interval code fuel).semantics rounds start := by
  have h := TimedExecution.Procedure.interval_iteration_run (stepPMF code) (stepPMF code)
    Configuration.halted Configuration.halted id (fun _ => rfl) (fun _ _ => (PMF.map_id _).symm)
    (absorbing code) (absorbing code) fuel hFuel start bound rounds hRounds
    (fun final hs => hStop final (by rwa [timed_eval_eq] at hs)) horizon hBudget
  simpa only [timed_eval_eq, PMF.map_id, id_eq, interval] using h

end Machine.IntervalTermination
