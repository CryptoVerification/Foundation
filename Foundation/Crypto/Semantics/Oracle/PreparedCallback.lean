import Foundation.Crypto.Semantics.Oracle.NativeCallback
import Foundation.Crypto.Semantics.Machine.PairPreparation
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! Real operand preparation and a native response callback share one
continuing controller. The restored source tapes remain private throughout.
The actual prepared buffer, rather than a semantic encoder, enters the code. -/
namespace CryptoOracle.Interactive.PreparedCallback
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

inductive Control (State : Type u) where
  | preparing (preparation : Machine.PairPreparation.Control)
  | calling (first second : Machine.Tape) (callback : NativeCallback.Control State)

variable {State : Type u}

noncomputable def step (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) : Control State → PMF (Control State)
  | .preparing (.ready first second buffer) =>
      PMF.pure (.calling first second (.responding (.running { inputTape := buffer })))
  | .preparing preparation => (Machine.PairPreparation.step preparation).map .preparing
  | .calling first second callback =>
      (NativeCallback.step native code oracle machine state trace request callback).map (.calling first second)

def boundary : Machine.PairPreparation.Control → Bool
  | .ready _ _ _ | .rejected _ _ _ => true
  | _ => false

def targetBoundary : Control State → Bool
  | .preparing preparation => boundary preparation
  | .calling _ _ _ => true

variable (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

noncomputable def preparation : Procedure (step native code oracle machine state trace request)
    Machine.PairPreparation.Input Unit :=
  Machine.PairPreparation.procedure.liftBoundary boundary (fun _ _ _ => rfl)
    (fun preparation h => by cases preparation <;> simp_all [boundary, Machine.PairPreparation.step])
    (fun _ _ => ()) (fun _ _ => rfl)
    (step native code oracle machine state trace request) targetBoundary Control.preparing (fun _ => rfl)
    (fun preparation h => by cases preparation <;> simp_all [boundary, step])

noncomputable def handoff : Procedure (step native code oracle machine state trace request)
    (Machine.PairPreparation.Input × Unit) Unit :=
  Procedure.ofFixed (step native code oracle machine state trace request)
    (fun input => .preparing (Machine.PairPreparation.procedure.exit input.1 input.2))
    (fun input _ => .calling
      (Machine.PairPreparation.operand [] input.1.first input.1.firstTail)
      (Machine.PairPreparation.operand [] input.1.second input.1.secondTail)
      (.responding (.running { inputTape := Machine.PairPreparation.fromCells ((Machine.PairPreparation.interleave input.1.first input.1.second).map some ++ [none]) })))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun input => by simp [TimedExecution.eval, step, Machine.PairPreparation.procedure, Procedure.ofFixed, PMF.pure_map])

noncomputable def preparingPrefix :=
  (preparation native code oracle machine state trace request).remember.seq
    (handoff native code oracle machine state trace request)
    (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem prefix_semantics (input : Machine.PairPreparation.Input) :
    (preparingPrefix native code oracle machine state trace request).semantics input = PMF.pure ((input, ()), ()) := by
  simp [preparingPrefix, preparation, handoff, Procedure.seq, Procedure.remember, Procedure.liftBoundary,
    Machine.PairPreparation.procedure, Procedure.ofFixed, PMF.pure_map]

def embed (frame : NativeCallback.Control State × (Machine.Tape × Machine.Tape)) : Control State :=
  .calling frame.2.1 frame.2.2 frame.1

theorem calling_eval (first second : Machine.Tape) (callback : NativeCallback.Control State) (fuel : Nat) :
    TimedExecution.eval (step native code oracle machine state trace request) fuel (.calling first second callback) =
      (TimedExecution.eval (NativeCallback.step native code oracle machine state trace request) fuel callback).map
        (.calling first second) := by
  symm
  exact eval_map _ _ (Control.calling first second) (fun _ => rfl) fuel callback

/-- The local code and resumed source have no access to the saved operands. -/
theorem calling_frames (first second : Machine.Tape) (callback : NativeCallback.Control State) (fuel : Nat)
    (endpoint : Control State)
    (hEndpoint : endpoint ∈ (TimedExecution.eval (step native code oracle machine state trace request) fuel
      (.calling first second callback)).support) :
    ∃ next, endpoint = .calling first second next := by
  rw [calling_eval, PMF.mem_support_map_iff] at hEndpoint
  obtain ⟨next, _, he⟩ := hEndpoint
  exact ⟨next, he.symm⟩

variable {Input : Type v} {Output : Type w}

noncomputable def whole (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = Machine.ResponseExport.endTape (encode output))
    (read : Input → Machine.Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input)
    (view : Machine.PairPreparation.Input → Input)
    (hEntry : ∀ input, P.execution.entry (view input) =
      { inputTape := Machine.PairPreparation.fromCells ((Machine.PairPreparation.interleave input.first input.second).map some ++ [none]) }) :=
  (preparingPrefix P.code code oracle machine state trace request).seq
    ((((NativeCallback.callback P encode hHalt hTape read hRead cap hCap code oracle machine state trace request).frame
      (Machine.Tape × Machine.Tape)).transport (step P.code code oracle machine state trace request) embed (fun frame => by simp [step, embed, framedStep, PMF.map_comp, Function.comp_def])).reindex
      (fun result => (view result.1.1,
        (Machine.PairPreparation.operand [] result.1.1.first result.1.1.firstTail,
         Machine.PairPreparation.operand [] result.1.1.second result.1.1.secondTail))))
    (fun input result hResult => by
      rw [prefix_semantics, PMF.mem_support_pure_iff] at hResult
      subst result
      change Control.calling _ _ (.responding (.running (P.execution.entry (view input)))) = _
      rw [hEntry]
      rfl)
    (fun input => P.execution.budget (view input) + (6 * cap (view input) + 7))
    (fun input result hResult => by
      rw [prefix_semantics, PMF.mem_support_pure_iff] at hResult
      subst result
      exact le_of_eq (NativeCallback.callback_budget P encode hHalt hTape read hRead cap hCap
        code oracle machine state trace request (view input)))

section Laws
variable (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = Machine.ResponseExport.endTape (encode output))
    (read : Input → Machine.Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input)
    (view : Machine.PairPreparation.Input → Input)
    (hEntry : ∀ input, P.execution.entry (view input) =
      { inputTape := Machine.PairPreparation.fromCells ((Machine.PairPreparation.interleave input.first input.second).map some ++ [none]) })

@[simp] theorem whole_budget (input : Machine.PairPreparation.Input) :
    (whole code oracle machine state trace request P encode hHalt hTape read hRead cap hCap view hEntry).budget input =
      12 * input.first.length + P.execution.budget (view input) + 6 * cap (view input) + 11 := by
  change (12 * input.first.length + 3 + 1) +
    (P.execution.budget (view input) + (6 * cap (view input) + 7)) = _
  omega

end Laws
end CryptoOracle.Interactive.PreparedCallback
