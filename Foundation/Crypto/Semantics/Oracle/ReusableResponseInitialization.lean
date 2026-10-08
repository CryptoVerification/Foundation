import Foundation.Crypto.Semantics.Machine.PrivateInitialization
import Foundation.Crypto.Semantics.Oracle.ReusableResponseSource
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! Native private initialization followed by the reusable source runtime.
Two charged head moves prepare the actual retained-key layout; no tape reset
or key materialization is hidden in the transfer. The caller is preserved. -/
namespace CryptoOracle.Interactive.ReusableResponseInitialization
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false

inductive Control (Component : Type v) (State : Type u) where
  | initializing (component : Machine.PrivateInitialization.Control)
  | aligning (tape : Machine.Tape)
  | active (source : ReusableResponseSource.Control Component State Machine.Tape)

variable {Component : Type v} {State : Type u}
    (componentStep : Component → PMF Component)
    (begin : Machine.Tape → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Machine.Tape))
    (generator native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (caller : Configuration State)

noncomputable def step : Control Component State → PMF (Control Component State)
  | .initializing (.ready key) => PMF.pure (.aligning key.moveLeft)
  | .aligning key => PMF.pure (.active (.source key.moveRight caller))
  | .initializing component => (Machine.PrivateInitialization.step generator component).map .initializing
  | .active source => (ReusableResponseSource.step componentStep begin ready native code oracle source).map .active

def readyBoundary : Machine.PrivateInitialization.Control → Bool
  | .ready _ => true
  | _ => false

def boundary : Control Component State → Bool
  | .initializing component => readyBoundary component
  | .aligning _ => true
  | .active _ => true

theorem active_eval (fuel : Nat) (source : ReusableResponseSource.Control Component State Machine.Tape) :
    TimedExecution.eval (step componentStep begin ready generator native code oracle caller) fuel (.active source) =
      (TimedExecution.eval (ReusableResponseSource.step componentStep begin ready native code oracle) fuel source).map Control.active := by
  symm
  exact eval_map _ _ Control.active (fun _ => rfl) fuel source

section Contract
variable {Input : Type w} {Output : Type x}
    (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = Machine.ResponseExport.endTape (encode output))
    (read : Input → Machine.Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input)
    (decode : Machine.Tape → Output)
    (hDecode : ∀ output, decode (Machine.ResponseExport.fromCells ((encode output).map some ++ [none])) = output)

noncomputable def sampling :=
  (Machine.PrivateInitialization.sample P encode hHalt hTape read hRead cap hCap).liftBoundary
    readyBoundary (fun _ _ _ => rfl)
    (fun component h => by cases component <;> simp_all [readyBoundary, Machine.PrivateInitialization.step])
    (fun _ component => match component with
      | .ready tape => decode tape
      | _ => decode {})
    (fun _ _ => by simp only [Machine.PrivateInitialization.sample, Procedure.ofFixed, hDecode])
    (step componentStep begin ready P.code native code oracle caller) boundary Control.initializing (fun _ => rfl)
    (fun component h => by cases component <;> simp_all [readyBoundary, step])

noncomputable def transfer : Procedure (step componentStep begin ready P.code native code oracle caller)
    Output Unit :=
  Procedure.ofFixed _
    (fun input => .initializing (.ready
      (Machine.ResponseExport.fromCells ((encode input).map some ++ [none]))))
    (fun input _ => .active (.source
      (Machine.ResponseExport.fromCells ((encode input).map some ++ [none])).moveLeft.moveRight caller))
    (fun _ => PMF.pure ()) (fun _ => 2)
    (fun _ => by simp [TimedExecution.eval, step, PMF.pure_map])

noncomputable def initialization :=
  (sampling componentStep begin ready native code oracle caller P encode hHalt hTape read hRead cap hCap decode hDecode).seq
    (transfer componentStep begin ready native code oracle caller P encode) (fun _ _ _ => rfl)
    (fun _ => 2) (fun _ _ _ => Nat.le_refl _)

theorem budget (input : Input) :
    (initialization componentStep begin ready native code oracle caller P encode hHalt hTape read hRead cap hCap decode hDecode).budget input =
      P.execution.budget input + cap input + 4 := by
  change (P.execution.budget input + cap input + 2) + 2 = _
  omega

theorem semantics (input : Input) :
    (initialization componentStep begin ready native code oracle caller P encode hHalt hTape read hRead cap hCap decode hDecode).semantics input =
      (P.execution.semantics input).map (fun output => (output, ())) := by
  simp only [initialization, sampling, Procedure.seq, Procedure.liftBoundary]
  simp only [Machine.PrivateInitialization.sample, Procedure.ofFixed]
  simp [transfer, Procedure.ofFixed, PMF.map, Function.comp_def]

theorem distribution (input : Input) :
    ((initialization componentStep begin ready native code oracle caller P encode hHalt hTape read hRead cap hCap decode hDecode).costed input).map
      (fun result => (initialization componentStep begin ready native code oracle caller P encode hHalt hTape read hRead cap hCap decode hDecode).exit input result.1) =
      (P.execution.semantics input).map (fun output => Control.active (ReusableResponseSource.Control.source
        (Machine.ResponseExport.fromCells ((encode output).map some ++ [none])).moveLeft.moveRight caller)) := by
  have h := congrArg (fun distribution => distribution.map
    ((initialization componentStep begin ready native code oracle caller P encode hHalt hTape read hRead cap hCap decode hDecode).exit input))
    ((initialization componentStep begin ready native code oracle caller P encode hHalt hTape read hRead cap hCap decode hDecode).correct input)
  rw [semantics] at h
  simp only [PMF.map_comp, Function.comp_def] at h
  exact h
/-- Initialization does not freeze the attacker at the transfer boundary. -/
theorem resume_law (input : Input) (horizon : Nat)
    (hBudget : P.execution.budget input + cap input + 4 ≤ horizon) :
    TimedExecution.eval (step componentStep begin ready P.code native code oracle caller) horizon
      (.initializing (.generating (P.execution.entry input))) =
      ((initialization componentStep begin ready native code oracle caller P encode hHalt hTape read hRead cap hCap decode hDecode).costed input).bind
        (fun result =>
          (TimedExecution.eval (ReusableResponseSource.step componentStep begin ready native code oracle) (horizon - result.2)
            (.source (Machine.ResponseExport.fromCells ((encode result.1.1).map some ++ [none])).moveLeft.moveRight caller)).map Control.active) := by
  have h := (initialization componentStep begin ready native code oracle caller P encode hHalt hTape read hRead cap hCap decode hDecode).law
    input horizon (by rw [budget]; exact hBudget)
  change TimedExecution.eval _ _ ((initialization componentStep begin ready native code oracle caller P encode hHalt hTape read hRead cap hCap decode hDecode).entry input) = _
  rw [h]
  congr 1
  funext result
  change TimedExecution.eval (step componentStep begin ready P.code native code oracle caller) (horizon - result.2)
    (.active (.source (Machine.ResponseExport.fromCells ((encode result.1.1).map some ++ [none])).moveLeft.moveRight caller)) = _
  exact active_eval componentStep begin ready P.code native code oracle caller _ _
end Contract
end CryptoOracle.Interactive.ReusableResponseInitialization
