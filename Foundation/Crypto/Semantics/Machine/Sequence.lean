import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.ProcedureBoundary
import Foundation.Crypto.Semantics.Invariant

/-! A finite sequence of native programs with charged physical handoffs.
The controller resets only the program counter and halt bit. Tape preparation
and copying must be performed by programs in the sequence, not host functions.
Contracts retain actual stopping costs so subsequent code may start early. -/
namespace Machine.Sequence
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false

inductive Control where
  | running (remaining : List Program) (machine : Configuration)
  | returned (machine : Configuration)
  deriving DecidableEq

def restart (machine : Configuration) : Configuration := { machine with pc := 0, halted := false }

noncomputable def step : Control → PMF Control
  | .running [] machine => PMF.pure (.returned machine)
  | .running (code :: rest) machine =>
      if machine.halted then PMF.pure (.running rest (restart machine))
      else (stepPMF code machine).map (Control.running (code :: rest))
  | .returned machine => PMF.pure (.returned machine)

def boundary : Control → Bool
  | .running _ machine => machine.halted
  | .returned _ => true

def remaining : Control → List Program
  | .running codes _ => codes
  | .returned _ => []

/-- Runtime control can only consume the supplied finite code list. It
cannot manufacture a new program from a logical output or proof reader. -/
theorem step_remaining_suffix (start final : Control) (h : final ∈ (step start).support) :
    (remaining final).IsSuffix (remaining start) := by
  cases start with
  | returned machine =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst final
      exact ⟨[], rfl⟩
  | running codes machine =>
      cases codes with
      | nil =>
          simp only [step, PMF.mem_support_pure_iff] at h
          subst final
          exact ⟨[], rfl⟩
      | cons code rest =>
          by_cases hh : machine.halted = true
          · simp only [step, hh, ↓reduceIte, PMF.mem_support_pure_iff] at h
            subst final
            exact ⟨[code], rfl⟩
          · simp only [step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
            obtain ⟨next, _, he⟩ := h
            subst final
            exact ⟨[], rfl⟩

theorem eval_remaining_suffix (fuel : Nat) (start final : Control)
    (h : final ∈ (eval step fuel start).support) :
    (remaining final).IsSuffix (remaining start) := by
  exact eval_preserves step (fun state => (remaining state).IsSuffix (remaining start))
    (fun state hState next hNext => (step_remaining_suffix state next hNext).trans hState)
    fuel start final ⟨[], rfl⟩ h

@[simp] theorem restart_input (machine : Configuration) : (restart machine).inputTape = machine.inputTape := rfl
@[simp] theorem restart_output (machine : Configuration) : (restart machine).outputTape = machine.outputTape := rfl

variable {Input : Type u} {Output : Type v}

noncomputable def body (P : Machine.Procedure Input Output) (rest : List Program)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output) :
    TimedExecution.Procedure step Input Output :=
  P.execution.liftBoundary Configuration.halted (fun input output _ => hHalt input output)
    (fun machine h => by simp [stepPMF, next, h]) read hRead
    step boundary (Control.running (P.code :: rest)) (fun _ => rfl)
    (fun machine h => by simp [step, h])

/-- One controller transition resumes the next code with the same tapes. -/
noncomputable def handoff (P : Machine.Procedure Input Output) (rest : List Program)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true) :
    TimedExecution.Procedure step (Input × Output) Unit :=
  TimedExecution.Procedure.ofFixed step
    (fun input => .running (P.code :: rest) (P.execution.exit input.1 input.2))
    (fun input _ => .running rest (restart (P.execution.exit input.1 input.2)))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun input => by simp [eval, step, hHalt, PMF.pure_map])

/-- Native execution and handoff compose without freezing an early exit. -/
noncomputable def stage (P : Machine.Procedure Input Output) (rest : List Program)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output) :
    TimedExecution.Procedure step Input ((Input × Output) × Unit) :=
  (body P rest hHalt read hRead).remember.seq (handoff P rest hHalt)
    (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

@[simp] theorem stage_budget (P : Machine.Procedure Input Output) (rest : List Program)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output) (input : Input) :
    (stage P rest hHalt read hRead).budget input = P.execution.budget input + 1 := rfl

theorem stage_semantics (P : Machine.Procedure Input Output) (rest : List Program)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output) (input : Input) :
    (stage P rest hHalt read hRead).semantics input =
      (P.execution.semantics input).map (fun output => ((input, output), ())) := by
  change (((P.execution.semantics input).map (fun output => (input, output))).bind
    (fun middle => (PMF.pure ()).map (fun token => (middle, token)))) = _
  simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

noncomputable def finish : TimedExecution.Procedure step Configuration Unit :=
  TimedExecution.Procedure.ofFixed step (Control.running []) (fun machine _ => .returned machine)
    (fun _ => PMF.pure ()) (fun _ => 1) (fun machine => by simp [eval, step, PMF.pure_map])

/-- Compose two distinct finite programs. A logical input view does not
prepare the second program's tapes: their physical equality is required. -/
noncomputable def chain {NextInput : Type w} {NextOutput : Type x}
    (P : Machine.Procedure Input Output) (Q : Machine.Procedure NextInput NextOutput)
    (rest : List Program)
    (hP : ∀ input output, (P.execution.exit input output).halted = true)
    (hQ : ∀ input output, (Q.execution.exit input output).halted = true)
    (readP : Input → Configuration → Output)
    (readQ : NextInput → Configuration → NextOutput)
    (hReadP : ∀ input output, readP input (P.execution.exit input output) = output)
    (hReadQ : ∀ input output, readQ input (Q.execution.exit input output) = output)
    (view : Input × Output → NextInput)
    (hHandoff : ∀ input output,
      Q.execution.entry (view (input, output)) = restart (P.execution.exit input output))
    (cap : Input → Nat)
    (hCap : ∀ input result, result ∈ ((stage P (Q.code :: rest) hP readP hReadP).semantics input).support →
      Q.execution.budget (view result.1) + 1 ≤ cap input) :
    TimedExecution.Procedure step Input
      (((Input × Output) × Unit) × ((NextInput × NextOutput) × Unit)) :=
  (stage P (Q.code :: rest) hP readP hReadP).seq
    ((stage Q rest hQ readQ hReadQ).reindex (fun result => view result.1))
    (fun input result hResult => by
      rw [stage_semantics, PMF.mem_support_map_iff] at hResult
      obtain ⟨output, _, he⟩ := hResult
      subst result
      change Control.running (Q.code :: rest) (Q.execution.entry (view (input, output))) =
        Control.running (Q.code :: rest) (restart (P.execution.exit input output))
      rw [hHandoff])
    cap hCap

end Machine.Sequence
