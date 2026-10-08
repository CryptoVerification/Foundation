import Foundation.Crypto.Semantics.Machine.ClosedSubroutineProbability
import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.ProcedureBoundary

/-! Operational contracts for actual native subroutine calls. Source halts
become active returns with unchanged tapes. First-arrival costs are retained,
so the caller executes its continuation with all remaining time. -/
namespace Machine.SubroutineContract
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false
theorem timed_return_eval_eq (code : Program) (returnPc : Nat) (start : Configuration) (fuel : Nat) :
    TimedExecution.eval (returnStepPMF code returnPc) fuel start = evalReturnWithin code returnPc start fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [TimedExecution.eval, evalReturnWithin_succ_head]
      congr 1
      funext next
      exact ih next

variable {Input : Type u} {Output : Type v}
    (P : Machine.Procedure Input Output) (pre suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc < P.code.length → pre.length + pc ≠ returnPc)
    (hClosed : ∀ start next, start.pc < P.code.length → Step P.code start next →
      next.halted = false → next.pc < P.code.length)
    (hEntry : ∀ input, (P.execution.entry input).pc < P.code.length)
    (hActive : ∀ input, (P.execution.entry input).halted = false)
    (hHalt : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).halted = true)

noncomputable def stopped : TimedExecution.Procedure
    (returnStepPMF (Program.withSubroutine pre P.code suffix returnPc) returnPc) Input Configuration :=
  TimedExecution.Procedure.ofFixed _
    (fun input => (P.execution.entry input).rebasePc pre.length)
    (fun _ machine => machine)
    (fun input => (P.execution.semantics input).map
      (fun output => (P.execution.exit input output).resumeAt returnPc))
    P.execution.budget
    (fun input => by
      rw [timed_return_eval_eq,
        Program.evalReturnWithin_configuration_eq_of_closed pre P.code suffix returnPc
          hLayout hClosed _ (hEntry input) (hActive input),
        P.final_run input (hHalt input) (P.execution.budget input) (Nat.le_refl _), PMF.map_comp]
      simp only [PMF.map_comp, Function.comp_def]
      rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext output ho
      simp [hHalt input output ho])

/-- An actual caller-stage contract, ending at the active return address.
The exact physical return configuration is its logical result. -/
noncomputable def call : TimedExecution.Procedure
    (stepPMF (Program.withSubroutine pre P.code suffix returnPc)) Input Configuration :=
  (stopped P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).liftBoundary
    (fun machine => machine.pc == returnPc)
    (by
      intro input machine hm
      change machine ∈ ((P.execution.semantics input).map
        (fun output => (P.execution.exit input output).resumeAt returnPc)).support at hm
      rw [PMF.mem_support_map_iff] at hm
      obtain ⟨output, _, rfl⟩ := hm
      change (((P.execution.exit input output).resumeAt returnPc).pc == returnPc) = true
      simp [Configuration.resumeAt])
    (fun machine hm => by
      have he : machine.pc = returnPc := by simpa using hm
      simp [returnStepPMF, he])
    (fun _ machine => machine) (fun _ _ => rfl)
    (stepPMF (Program.withSubroutine pre P.code suffix returnPc))
    (fun machine => machine.pc == returnPc) id (fun _ => rfl)
    (fun machine hm => by
      have hn : machine.pc ≠ returnPc := by simpa using hm
      simp [returnStepPMF, hn, PMF.map_id])

theorem call_budget (input : Input) :
    (call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).budget input =
      P.execution.budget input := rfl

theorem call_semantics (input : Input) :
    (call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).semantics input =
      (P.execution.semantics input).map
        (fun output => (P.execution.exit input output).resumeAt returnPc) := rfl

/-- The costed call is exactly the original caller's first-arrival execution.
Boundary padding and continuation instructions are not charged to the callee. -/
theorem call_costed (input : Input) :
    (call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).costed input =
      runToBoundary (stepPMF (Program.withSubroutine pre P.code suffix returnPc))
        (fun machine => machine.pc == returnPc) (P.execution.budget input)
        ((P.execution.entry input).rebasePc pre.length) := by
  have h := runToBoundary_map
    (returnStepPMF (Program.withSubroutine pre P.code suffix returnPc) returnPc)
    (stepPMF (Program.withSubroutine pre P.code suffix returnPc))
    (fun machine => machine.pc == returnPc) (fun machine => machine.pc == returnPc) id
    (fun _ => rfl)
    (fun machine hm => by
      have hn : machine.pc ≠ returnPc := by simpa using hm
      simp [returnStepPMF, hn, PMF.map_id])
    (P.execution.budget input) ((P.execution.entry input).rebasePc pre.length)
  change runToBoundary _ _ _ _ = (runToBoundary _ _ _ _).map id at h
  rw [PMF.map_id] at h
  change (runToBoundary _ _ _ _).map id = _
  rw [PMF.map_id]
  exact h.symm

/-- Every supported endpoint is an active return, with source tapes intact. -/
theorem call_returns (input : Input) (machine : Configuration)
    (h : machine ∈ ((call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).semantics input).support) :
    machine.pc = returnPc ∧ machine.halted = false ∧
      ∃ output ∈ (P.execution.semantics input).support,
        machine.inputTape = (P.execution.exit input output).inputTape ∧
        machine.outputTape = (P.execution.exit input output).outputTape := by
  rw [call_semantics, PMF.mem_support_map_iff] at h
  obtain ⟨output, ho, rfl⟩ := h
  exact ⟨rfl, rfl, output, ho, rfl, rfl⟩

/-- The original caller continues from the real return state with precisely
its remaining time. The returned subroutine is not frozen in the caller. -/
theorem call_resume (input : Input) (horizon : Nat) (hTime : P.execution.budget input ≤ horizon) :
    TimedExecution.eval (stepPMF (Program.withSubroutine pre P.code suffix returnPc)) horizon
      ((P.execution.entry input).rebasePc pre.length) =
      ((call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).costed input).bind
        (fun result => TimedExecution.eval
          (stepPMF (Program.withSubroutine pre P.code suffix returnPc)) (horizon - result.2) result.1) :=
  (call P pre suffix returnPc hLayout hClosed hEntry hActive hHalt).law input horizon hTime

end Machine.SubroutineContract
