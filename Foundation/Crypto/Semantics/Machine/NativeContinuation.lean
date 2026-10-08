import Foundation.Crypto.Semantics.ProcedureCompletion
import Foundation.Crypto.Semantics.ProcedureBoundary
import Foundation.Crypto.Semantics.ProcedureSimulation
import Foundation.Crypto.Semantics.Framing
import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.Machine.SubroutineSimulation

/-! A charged handoff from a completed probabilistic producer to fixed native
code. Both physical tapes, including their head positions, are inherited.
The producer state is retained outside the native machine's accessible state.
A projection must select an already existing public machine, not prepare a new
encoding; that physical layout obligation is explicit in applications. -/
namespace Machine.NativeContinuation
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

inductive Control (State : Type u) where
  | producing : State → Control State
  | observing : State → Configuration → Control State

variable {State : Type u} (sourceStep : State → PMF State)
    (boundary : State → Bool) (publicMachine : State → Configuration) (code : Program)

noncomputable def step : Control State → PMF (Control State)
  | Control.producing state =>
      if boundary state then PMF.pure (Control.observing state ((publicMachine state).resumeAt 0))
      else (sourceStep state).map Control.producing
  | Control.observing saved machine => (stepPMF code machine).map (Control.observing saved)

def stopped : Control State → Bool
  | Control.producing state => boundary state
  | Control.observing _ _ => true

/-- The transfer changes only control registers, never tape cells or heads. -/
theorem transfer_tapes (state : State) :
    ((publicMachine state).resumeAt 0).inputTape = (publicMachine state).inputTape ∧
    ((publicMachine state).resumeAt 0).outputTape = (publicMachine state).outputTape := ⟨rfl, rfl⟩

/-- The native component cannot inspect its retained producer state. -/
theorem observing_eval (saved : State) (machine : Configuration) (fuel : Nat) :
    eval (step sourceStep boundary publicMachine code) fuel (Control.observing saved machine) =
      (eval (stepPMF code) fuel machine).map (Control.observing saved) := by
  symm
  exact eval_map _ _ (Control.observing saved) (fun _ => rfl) fuel machine

variable {start : State}
    (C : Completion sourceStep start (fun state => boundary state = true))
    (hAbsorb : ∀ state, boundary state = true → sourceStep state = PMF.pure state)
    {Input : Type v} {Output : Type w} (Q : Machine.Procedure Input Output)
    (view : State → Input)
    (hEntry : ∀ state, Q.execution.entry (view state) = (publicMachine state).resumeAt 0)

noncomputable def producer : TimedExecution.Procedure (step sourceStep boundary publicMachine Q.code) Unit State :=
  C.execution.liftBoundary boundary
    (fun _ state h => by cases ‹Unit›; rw [C.exit]; exact C.stopped state h)
    hAbsorb (fun _ state => state) (fun _ state => by cases ‹Unit›; exact C.exit state)
    (step sourceStep boundary publicMachine Q.code) (stopped boundary) Control.producing
    (fun _ => rfl) (fun state h => by simp [step, h])

/-- Total contract: non-boundary inputs already start in the native phase.
Only boundary inputs are supplied by the certified producer, where exactly
one transition is charged. This fallback performs no producer transition. -/
noncomputable def transfer : TimedExecution.Procedure (step sourceStep boundary publicMachine Q.code) State Unit :=
  TimedExecution.Procedure.ofFixed _
    (fun state => if boundary state then Control.producing state
      else Control.observing state ((publicMachine state).resumeAt 0))
    (fun state _ => Control.observing state ((publicMachine state).resumeAt 0))
    (fun _ => PMF.pure ()) (fun state => if boundary state then 1 else 0)
    (fun state => by by_cases h : boundary state = true <;> simp [h, eval, step, PMF.pure_map])

noncomputable def native : TimedExecution.Procedure (step sourceStep boundary publicMachine Q.code) State Output :=
  ((Q.execution.frame State).transport (step sourceStep boundary publicMachine Q.code)
    (fun frame => Control.observing frame.2 frame.1)
    (fun frame => by simp only [step, framedStep, PMF.map_comp, Function.comp_def]))
    |>.reindex (fun state => (view state, state))

private noncomputable def prepared :=
  (producer sourceStep boundary publicMachine C hAbsorb Q).seq
    (transfer sourceStep boundary publicMachine Q)
    (fun argument state h => by
      cases argument
      change (if boundary state then _ else _) = Control.producing (C.execution.exit () state)
      rw [C.exit, C.stopped state h]
      rfl)
    (fun _ => 1) (fun _ state _ => by change (if boundary state then 1 else 0) ≤ 1; split <;> omega)

/-- Actual producer, one charged transfer, then arbitrary native code.
The cap bounds native execution uniformly over supported producer results. -/
noncomputable def whole (cap : Nat)
    (hCap : ∀ state ∈ (C.execution.semantics ()).support, Q.execution.budget (view state) ≤ cap) :=
  (prepared sourceStep boundary publicMachine C hAbsorb Q).seq
    ((native sourceStep boundary publicMachine Q view).reindex Prod.fst)
    (fun _ result _ => by change Control.observing result.1 (Q.execution.entry (view result.1)) = _; rw [hEntry]; rfl)
    (fun _ => cap) (fun argument result h => by
      cases argument
      change result ∈ ((C.execution.semantics ()).bind (fun state => (PMF.pure ()).map (fun value => (state, value)))).support at h
      rw [PMF.mem_support_bind_iff] at h
      obtain ⟨state, hs, hr⟩ := h
      simp only [PMF.pure_map, PMF.mem_support_pure_iff] at hr
      subst result
      exact hCap state hs)

theorem whole_budget (cap : Nat)
    (hCap : ∀ state ∈ (C.execution.semantics ()).support, Q.execution.budget (view state) ≤ cap) :
    (whole sourceStep boundary publicMachine C hAbsorb Q view hEntry cap hCap).budget () =
      C.execution.budget () + 1 + cap := rfl

theorem whole_semantics (cap : Nat)
    (hCap : ∀ state ∈ (C.execution.semantics ()).support, Q.execution.budget (view state) ≤ cap) :
    (whole sourceStep boundary publicMachine C hAbsorb Q view hEntry cap hCap).semantics () =
      (C.execution.semantics ()).bind (fun state =>
        (Q.execution.semantics (view state)).map (fun output => ((state, ()), output))) := by
  simp only [whole, prepared, TimedExecution.Procedure.seq, producer, TimedExecution.Procedure.liftBoundary,
    transfer, TimedExecution.Procedure.ofFixed, native, TimedExecution.Procedure.frame, TimedExecution.Procedure.transport, TimedExecution.Procedure.reindex,
    PMF.bind_bind, PMF.pure_map, PMF.pure_bind, Function.comp_def]

/-- Preserve producer/result-time correlations and charge the single
handoff in addition to the native observer's own cost distribution. -/
theorem whole_costed (cap : Nat)
    (hCap : ∀ state ∈ (C.execution.semantics ()).support, Q.execution.budget (view state) ≤ cap) :
    (whole sourceStep boundary publicMachine C hAbsorb Q view hEntry cap hCap).costed () =
      ((producer sourceStep boundary publicMachine C hAbsorb Q).costed ()).bind
        (fun first => (Q.execution.costed (view first.1)).map
          (fun second => (((first.1, ()), second.1), first.2 + 1 + second.2))) := by
  simp only [whole, prepared, TimedExecution.Procedure.seq, transfer,
    TimedExecution.Procedure.ofFixed, native, TimedExecution.Procedure.frame,
    TimedExecution.Procedure.transport, TimedExecution.Procedure.reindex,
    PMF.bind_bind, PMF.pure_map, PMF.pure_bind, Function.comp_def]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext first hf
  have hs := (producer sourceStep boundary publicMachine C hAbsorb Q).result_support () first hf
  change first.1 ∈ (C.execution.semantics ()).support at hs
  rw [C.stopped first.1 hs]
  rfl

theorem whole_exit (cap : Nat)
    (hCap : ∀ state ∈ (C.execution.semantics ()).support, Q.execution.budget (view state) ≤ cap)
    (result : (State × Unit) × Output) :
    (whole sourceStep boundary publicMachine C hAbsorb Q view hEntry cap hCap).exit () result =
      Control.observing result.1.1 (Q.execution.exit (view result.1.1) result.2) := rfl

include hAbsorb hEntry in
/-- Finite evaluation of the composed runtime, including its private saved
state and the native program's complete physical exit. -/
theorem run (hHalt : ∀ input output, output ∈ (Q.execution.semantics input).support →
      (Q.execution.exit input output).halted = true)
    (cap : Nat)
    (hCap : ∀ state ∈ (C.execution.semantics ()).support, Q.execution.budget (view state) ≤ cap)
    (horizon : Nat) (hTime : C.execution.budget () + 1 + cap ≤ horizon) :
    eval (step sourceStep boundary publicMachine Q.code) horizon (Control.producing start) =
      (C.execution.semantics ()).bind (fun state =>
        (Q.execution.semantics (view state)).map
          (fun output => Control.observing state (Q.execution.exit (view state) output))) := by
  have h := (whole sourceStep boundary publicMachine C hAbsorb Q view hEntry cap hCap).final_run ()
    (by
      intro result hr
      rw [whole_semantics, PMF.mem_support_bind_iff] at hr
      obtain ⟨state, _, hr⟩ := hr
      rw [PMF.mem_support_map_iff] at hr
      obtain ⟨output, ho, rfl⟩ := hr
      change (stepPMF Q.code (Q.execution.exit (view state) output)).map (Control.observing state) = _
      simp only [whole_exit]
      simp [stepPMF, next, hHalt _ _ ho, PMF.pure_map]) horizon hTime
  change eval (step sourceStep boundary publicMachine Q.code) horizon (Control.producing (C.execution.entry ())) = _ at h
  rw [C.entry, whole_semantics, PMF.map_bind] at h
  simpa only [PMF.map_comp, Function.comp_def, whole_exit] using h

end Machine.NativeContinuation
