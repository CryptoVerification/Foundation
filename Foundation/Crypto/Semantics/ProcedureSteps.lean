import Foundation.Crypto.Semantics.ProcedureIteration

/-! Instantiate repeated contracts with actual transitions. The resulting
value and accumulated cost equal the original machine's finite execution. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u
variable {State : Type u} (step : State → PMF State)

noncomputable def transition : Procedure step State State :=
  Procedure.ofFixed step id (fun _ result => result) step (fun _ => 1)
    (fun start => by
      simp only [TimedExecution.eval, PMF.bind_pure]
      exact (PMF.map_id _).symm)

theorem transition_bound (start : State) : (transition step).budget start ≤ 1 := Nat.le_refl 1

theorem transition_return (start result : State) (_ : result ∈ ((transition step).semantics start).support) :
    (transition step).exit start result = (transition step).entry result := rfl

noncomputable def steps (rounds : Nat) :=
  (transition step).iterate 1 (transition_bound step) (transition_return step) rounds

theorem steps_budget (rounds : Nat) (start : State) :
    (steps step rounds).budget start = rounds := by
  unfold steps
  rw [iterate_budget, Nat.mul_one]

theorem steps_semantics (rounds : Nat) (start : State) :
    (steps step rounds).semantics start = TimedExecution.eval step rounds start := by
  induction rounds generalizing start with
  | zero => rfl
  | succ rounds ih =>
      unfold steps
      rw [iterate_semantics_succ]
      change (step start).bind (fun next => (steps step rounds).semantics next) = _
      rw [TimedExecution.eval]
      congr 1
      funext next
      exact ih next

theorem steps_costed (rounds : Nat) (start : State) :
    (steps step rounds).costed start =
      (TimedExecution.eval step rounds start).map (fun result => (result, rounds)) := by
  induction rounds generalizing start with
  | zero => simp [steps, iterate, iteration, Procedure.ofFixed, TimedExecution.eval, PMF.pure_map]
  | succ rounds ih =>
      unfold steps
      rw [iterate_costed_succ]
      change ((step start).map (fun next => (next, 1))).bind
        (fun first => ((steps step rounds).costed first.1).map (fun second => (second.1, first.2 + second.2))) = _
      simp only [PMF.bind_map, Function.comp_def, ih, PMF.map_comp, TimedExecution.eval, PMF.map_bind]
      congr 1
      funext next
      simp only [Nat.one_add]
end Foundation.Probability.TimedExecution.Procedure
