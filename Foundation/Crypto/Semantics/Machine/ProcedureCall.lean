import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.ProcedureBoundary
import Foundation.Crypto.Semantics.Framing

/-! A fixed finite caller for arbitrary native procedure code. Every native
instruction is executed, and ownership transfer after native halt costs one
additional controller transition. Typed readers are proof observations only. -/
namespace Machine.ProcedureCall
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

inductive Control where
  | running : Configuration → Control
  | returned : Configuration → Control
  deriving DecidableEq

noncomputable def step (code : Program) : Control → PMF Control
  | .running machine =>
      if machine.halted then PMF.pure (.returned machine)
      else (stepPMF code machine).map Control.running
  | .returned machine => PMF.pure (.returned machine)

def boundary : Control → Bool
  | .running machine => machine.halted
  | .returned _ => true

variable {Input : Type u} {Output : Type v}

noncomputable def beginProcedure (P : Machine.Procedure Input Output)
    (hHalt : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).halted = true)
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output) :
    TimedExecution.Procedure (step P.code) Input Output :=
  P.execution.liftBoundary Configuration.halted hHalt
    (fun machine h => by simp [stepPMF, next, h]) read hRead
    (step P.code) boundary Control.running (fun _ => rfl)
    (fun machine h => by simp [step, h])

theorem returned_eval (code : Program) (machine : Configuration) (fuel : Nat) :
    eval (step code) fuel (.returned machine) = PMF.pure (.returned machine) :=
  Block.eval_of_absorbing (step := step code) (.returned machine) rfl fuel

theorem running_halted_eval (code : Program) (machine : Configuration) (hHalt : machine.halted = true)
    (fuel : Nat) (hFuel : 1 ≤ fuel) :
    eval (step code) fuel (.running machine) = PMF.pure (.returned machine) := by
  cases fuel with
  | zero => omega
  | succ fuel => simp [eval, step, hHalt, returned_eval]

/-- Completion includes the charged transition that transfers ownership. -/
theorem run (P : Machine.Procedure Input Output)
    (hHalt : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).halted = true)
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (input : Input) (horizon : Nat) (hBudget : P.execution.budget input + 1 ≤ horizon) :
    eval (step P.code) horizon (.running (P.execution.entry input)) =
      (P.execution.semantics input).map (fun output => .returned (P.execution.exit input output)) := by
  let L := beginProcedure P hHalt read hRead
  have h := L.law input horizon (by change P.execution.budget input ≤ horizon; omega)
  change eval (step P.code) horizon (.running (P.execution.entry input)) = _ at h
  rw [h]
  have hEach (result : Output × Nat) (hResult : result ∈ (L.costed input).support) :
      eval (step P.code) (horizon - result.2) (L.exit input result.1) =
        PMF.pure (.returned (P.execution.exit input result.1)) := by
    have ht := L.bounded input result hResult
    change result.2 ≤ P.execution.budget input at ht
    apply running_halted_eval
    · exact hHalt input result.1 (L.result_support input result hResult)
    · omega
  calc
    _ = (L.costed input).bind (fun result => PMF.pure (.returned (P.execution.exit input result.1))) := by
      rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext result hResult
      exact hEach result hResult
    _ = _ := by
      have hMap := congrArg (fun p => p.map (fun output => Control.returned (P.execution.exit input output))) (L.correct input)
      change ((L.costed input).map Prod.fst).map (fun output => Control.returned (P.execution.exit input output)) =
        (P.execution.semantics input).map (fun output => Control.returned (P.execution.exit input output)) at hMap
      simpa only [PMF.map_comp, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def] using hMap

/-- Native code plus the fixed caller produces a reusable whole procedure. -/
noncomputable def wholeProcedure (P : Machine.Procedure Input Output)
    (hHalt : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).halted = true)
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output) :
    TimedExecution.Procedure (step P.code) Input Output :=
  TimedExecution.Procedure.ofFixed (step P.code)
    (fun input => .running (P.execution.entry input))
    (fun input output => .returned (P.execution.exit input output))
    P.execution.semantics (fun input => P.execution.budget input + 1)
    (fun input => run P hHalt read hRead input _ (Nat.le_refl _))

/-- Keep an already retained caller frame isolated while running native code.
The native instructions and charged return are exactly the ordinary caller's.
Input preparation and copies into or out of the saved frame remain separate. -/
noncomputable def savedProcedure (Saved : Type w) (P : Machine.Procedure Input Output)
    (hHalt : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).halted = true)
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output) :
    TimedExecution.Procedure (framedStep (Saved := Saved) (step P.code)) (Input × Saved) Output :=
  (wholeProcedure P hHalt read hRead).frame Saved

theorem saved_run {Saved : Type w} (P : Machine.Procedure Input Output)
    (hHalt : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).halted = true)
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (input : Input) (saved : Saved) (horizon : Nat)
    (hBudget : P.execution.budget input + 1 ≤ horizon) :
    eval (framedStep (step P.code)) horizon (.running (P.execution.entry input), saved) =
      (P.execution.semantics input).map (fun output => (.returned (P.execution.exit input output), saved)) := by
  rw [framed_eval, run P hHalt read hRead input horizon hBudget, PMF.map_comp]
  rfl

end Machine.ProcedureCall
