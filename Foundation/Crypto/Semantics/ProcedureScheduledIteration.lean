import Foundation.Crypto.Semantics.CostedIteration
import Foundation.Crypto.Semantics.ProcedureCompletion

/-! Indexed adaptive composition in one unchanged physical transition system.
The analysis may use different contracts and bounds at each round. A round
receives the actual preceding value; only checked physical handoffs compose.
Round indices are proof metadata, not uncharged runtime branch instructions.
Costs are summed jointly with results and are never replaced by the caps. -/
namespace Foundation.Probability.CostedIteration
universe u v
variable {Value : Type u} {Public : Type v}

noncomputable def scheduled (kernel : Nat → Value → PMF (Value × Nat)) : Nat → Nat → Value → PMF (Value × Nat)
  | _, 0, start => PMF.pure (start, 0)
  | index, rounds + 1, start => (kernel index start).bind fun first =>
      (scheduled kernel (index + 1) rounds first.1).map (fun second => (second.1, first.2 + second.2))

theorem scheduled_map (source : Nat → Value → PMF (Value × Nat))
    (target : Nat → Public → PMF (Public × Nat)) (view : Value → Public)
    (hRound : ∀ index start, (source index start).map (project view) = target index (view start))
    (index rounds : Nat) (start : Value) :
    (scheduled source index rounds start).map (project view) = scheduled target index rounds (view start) := by
  induction rounds generalizing index start with
  | zero => simp [scheduled, project, PMF.pure_map]
  | succ rounds ih =>
      rw [scheduled, scheduled, ← hRound index start]
      simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, project]
      congr 1
      funext first
      have h := congrArg (fun distribution => distribution.map (fun second => (second.1, first.2 + second.2)))
        (ih (index + 1) first.1)
      simpa only [PMF.map_comp, Function.comp_def, project] using h

end Foundation.Probability.CostedIteration

namespace Foundation.Probability.TimedExecution.Procedure
universe u v w
variable {State : Type u} {Value : Type v} {Public : Type w} {step : State → PMF State}

def scheduledBudget (cap : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | index, rounds + 1 => cap index + scheduledBudget cap (index + 1) rounds

theorem scheduledBudget_const (bound index rounds : Nat) :
    scheduledBudget (fun _ => bound) index rounds = rounds * bound := by
  induction rounds generalizing index with
  | zero => simp [scheduledBudget]
  | succ rounds ih => simp [scheduledBudget, ih, Nat.add_mul, Nat.add_comm]

theorem scheduledBudget_le (cap : Nat → Nat) (bound index rounds : Nat)
    (hCap : ∀ offset, offset < rounds → cap (index + offset) ≤ bound) :
    scheduledBudget cap index rounds ≤ rounds * bound := by
  induction rounds generalizing index with
  | zero => simp [scheduledBudget]
  | succ rounds ih =>
      have hFirst := hCap 0 (by omega)
      simp only [Nat.add_zero] at hFirst
      have hNext : ∀ offset, offset < rounds → cap (index + 1 + offset) ≤ bound := by
        intro offset hs
        have h := hCap (offset + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hRest := ih (index + 1) hNext
      simp only [scheduledBudget, Nat.add_mul, Nat.one_mul]
      omega

variable (P : Nat → Procedure step Value Value) (entry : Value → State)
    (hEntry : ∀ index input, (P index).entry input = entry input)
    (hReturn : ∀ index input output, output ∈ ((P index).semantics input).support → (P index).exit input output = entry output)
    (cap : Nat → Nat) (hCap : ∀ index input, (P index).budget input ≤ cap index)

noncomputable def scheduledChain : (index rounds : Nat) → Chain (step := step) entry (scheduledBudget cap index rounds)
  | _, 0 =>
      ⟨Procedure.ofFixed step entry (fun _ output => entry output) PMF.pure (fun _ => 0)
        (fun _ => by simp [eval, PMF.pure_map]), (fun _ => rfl), (fun _ _ => rfl), (fun _ => rfl)⟩
  | index, rounds + 1 =>
      let previous := scheduledChain (index + 1) rounds
      let first := ((P index).observe id (fun _ output => entry output)
        (fun input output hs => (hReturn index input output hs).symm)).withBudget (fun _ => cap index) (hCap index)
      let both := first.seq previous.execution (fun _ middle _ => previous.entry_eq middle)
        (fun _ => scheduledBudget cap (index + 1) rounds)
        (fun _ middle _ => le_of_eq (previous.budget_eq middle))
      let result := both.observe Prod.snd (fun _ output => entry output)
        (fun _ output _ => (previous.exit_eq output.1 output.2).symm)
      ⟨result, hEntry index, (fun _ _ => rfl), (fun _ => rfl)⟩

noncomputable def scheduled (index rounds : Nat) :=
  (scheduledChain P entry hEntry hReturn cap hCap index rounds).execution

theorem scheduled_entry (index rounds : Nat) (input : Value) :
    (scheduled P entry hEntry hReturn cap hCap index rounds).entry input = entry input :=
  (scheduledChain P entry hEntry hReturn cap hCap index rounds).entry_eq input

theorem scheduled_exit (index rounds : Nat) (input output : Value) :
    (scheduled P entry hEntry hReturn cap hCap index rounds).exit input output = entry output :=
  (scheduledChain P entry hEntry hReturn cap hCap index rounds).exit_eq input output

theorem scheduled_budget (index rounds : Nat) (input : Value) :
    (scheduled P entry hEntry hReturn cap hCap index rounds).budget input = scheduledBudget cap index rounds :=
  (scheduledChain P entry hEntry hReturn cap hCap index rounds).budget_eq input

theorem scheduled_semantics_zero (index : Nat) (input : Value) :
    (scheduled P entry hEntry hReturn cap hCap index 0).semantics input = PMF.pure input := rfl

theorem scheduled_semantics_succ (index rounds : Nat) (input : Value) :
    (scheduled P entry hEntry hReturn cap hCap index (rounds + 1)).semantics input =
      ((P index).semantics input).bind (fun middle =>
        (scheduled P entry hEntry hReturn cap hCap (index + 1) rounds).semantics middle) := by
  simp only [scheduled, scheduledChain, observe, withBudget, Procedure.seq, PMF.map_bind,
    PMF.map_comp, Function.comp_def, PMF.bind_map]
  simp only [show (fun x : Value => x) = id by rfl, PMF.map_id]
  rfl

theorem scheduled_costed_succ (index rounds : Nat) (input : Value) :
    (scheduled P entry hEntry hReturn cap hCap index (rounds + 1)).costed input =
      ((P index).costed input).bind (fun first =>
        ((scheduled P entry hEntry hReturn cap hCap (index + 1) rounds).costed first.1).map
          (fun second => (second.1, first.2 + second.2))) := by
  simp only [scheduled, scheduledChain, observe, withBudget, Procedure.seq, PMF.map_bind,
    PMF.map_comp, Function.comp_def, PMF.bind_map]
  rfl

theorem scheduled_costed (index rounds : Nat) (input : Value) :
    (scheduled P entry hEntry hReturn cap hCap index rounds).costed input =
      CostedIteration.scheduled (fun index => (P index).costed) index rounds input := by
  induction rounds generalizing index input with
  | zero => simp [scheduled, scheduledChain, Procedure.ofFixed, CostedIteration.scheduled, PMF.pure_map]
  | succ rounds ih =>
      rw [scheduled_costed_succ, CostedIteration.scheduled]
      congr 1
      funext first
      rw [ih]

theorem scheduled_public_cost (kernel : Nat → Public → PMF (Public × Nat)) (view : Value → Public)
    (hRound : ∀ index input, ((P index).costed input).map (CostedIteration.project view) = kernel index (view input))
    (index rounds : Nat) (input : Value) :
    ((scheduled P entry hEntry hReturn cap hCap index rounds).costed input).map (CostedIteration.project view) =
      CostedIteration.scheduled kernel index rounds (view input) := by
  rw [scheduled_costed]
  exact CostedIteration.scheduled_map _ _ view hRound index rounds input

theorem scheduled_final_run (terminal : State → Prop)
    (hAbsorb : ∀ state, terminal state → step state = PMF.pure state)
    (index rounds : Nat) (input : Value)
    (hComplete : ∀ output ∈ ((scheduled P entry hEntry hReturn cap hCap index rounds).semantics input).support,
      terminal (entry output)) (horizon : Nat) (hTime : scheduledBudget cap index rounds ≤ horizon) :
    eval step horizon (entry input) =
      ((scheduled P entry hEntry hReturn cap hCap index rounds).semantics input).map entry := by
  have h := (scheduled P entry hEntry hReturn cap hCap index rounds).final_run input
    (fun output hs => by rw [scheduled_exit]; exact hAbsorb _ (hComplete output hs)) horizon
    (by rw [scheduled_budget]; exact hTime)
  have hExit : (scheduled P entry hEntry hReturn cap hCap index rounds).exit input = entry :=
    funext (scheduled_exit P entry hEntry hReturn cap hCap index rounds input)
  rw [scheduled_entry, hExit] at h
  exact h

end Foundation.Probability.TimedExecution.Procedure
