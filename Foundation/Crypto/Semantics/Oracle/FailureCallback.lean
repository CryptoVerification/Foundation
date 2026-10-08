import Foundation.Crypto.Semantics.Machine.PreparationCheck
import Foundation.Crypto.Semantics.Oracle.NativeCallback
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! A rejected physical preparation exports its actual response tape and
resumes the suspended source. Runtime never evaluates a response encoder.
This handler contract does not itself enforce a one-use policy. -/
namespace CryptoOracle.Interactive.FailureCallback
open Foundation.Probability TimedExecution
universe u

inductive Control (State : Type u) where
  | preparing (preparation : Machine.PreparationCheck.Control)
  | calling (first second : Machine.Tape) (callback : NativeCallback.Control State)

variable {State : Type u}

noncomputable def step (code : Code) (oracle : BitOracle State)
    (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) : Control State → PMF (Control State)
  | .preparing (.failure (.returned first second response)) =>
      PMF.pure (.calling first second (.responding (.running { outputTape := response, halted := true })))
  | .preparing preparation => (Machine.PreparationCheck.step preparation).map .preparing
  | .calling first second callback =>
      (NativeCallback.step [] code oracle machine state trace request callback).map (.calling first second)

def boundary : Machine.PreparationCheck.Control → Bool
  | .failure (.returned _ _ _) => true
  | .preparing (.ready _ _ _) => true
  | _ => false

def targetBoundary : Control State → Bool
  | .preparing preparation => boundary preparation
  | .calling _ _ _ => true

def packetMachine : Machine.Configuration :=
  { outputTape := Machine.ResponseExport.endTape [false], halted := true }

/-- Zero native steps: the entry is the already-written physical response.
The export and return operations are charged by the callback contract. -/
noncomputable def packetReady : Machine.Procedure Unit Unit :=
  Machine.Procedure.ofFixed [] (fun _ => packetMachine) (fun _ _ => packetMachine)
    (fun _ => PMF.pure ()) (fun _ => 0) (fun _ => by simp [Machine.evalConfigWithin, PMF.pure_map])

def embed (frame : NativeCallback.Control State × (Machine.Tape × Machine.Tape)) : Control State :=
  .calling frame.2.1 frame.2.2 frame.1

variable (code : Code) (oracle : BitOracle State) (machine : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool)) (request : List Bool)

noncomputable def delivery (first second : Machine.Tape) :=
  ((((NativeCallback.callback packetReady (fun _ => [false])
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => ()) (fun _ _ => rfl)
    (fun _ => 1) (fun _ _ _ => Nat.le_refl _)
    code oracle machine state trace request).frame (Machine.Tape × Machine.Tape)).transport
      (step code oracle machine state trace request) embed
      (fun frame => by
        rcases frame with ⟨callback, first, second⟩
        cases callback <;> simp [embed, step, framedStep, NativeCallback.step, PMF.map_comp, Function.comp_def, packetReady, Machine.Procedure.ofFixed]))).reindex
    (fun _ : Unit => ((), (first, second)))

noncomputable def preparation (input : Machine.PreparationCheck.FailureInput) :=
  (TimedExecution.Procedure.ofFixed Machine.PreparationCheck.step
    (fun _ : Unit => .preparing (.reading
      (Machine.PairPreparation.operand [] input.first input.firstTail)
      (Machine.PairPreparation.operand [] input.second input.secondTail) {}))
    (fun _ _ => Machine.PreparationCheck.final input) (fun _ => PMF.pure ())
    (fun _ => 12 * Machine.PreparationCheck.consumed input + 10)
    (fun _ => by simpa only [PMF.pure_map] using Machine.PreparationCheck.run input)).liftBoundary
    boundary (fun _ _ _ => rfl)
    (fun preparation h => by
      cases preparation with
      | preparing preparation => cases preparation <;> simp_all [boundary, Machine.PreparationCheck.step, Machine.PairPreparation.step, PMF.pure_map]
      | failure recovery => cases recovery <;> simp_all [boundary, Machine.PreparationCheck.step, Machine.PreparationFailure.step, PMF.pure_map])
    (fun _ _ => ()) (fun _ _ => rfl)
    (step code oracle machine state trace request) targetBoundary Control.preparing (fun _ => rfl)
    (fun preparation h => by
      cases preparation with
      | preparing preparation => rfl
      | failure recovery => cases recovery <;> simp_all [boundary, step])

noncomputable def handoff (input : Machine.PreparationCheck.FailureInput) :
    Procedure (step code oracle machine state trace request) Unit Unit :=
  Procedure.ofFixed (step code oracle machine state trace request)
    (fun _ => .preparing (Machine.PreparationCheck.final input))
    (fun _ _ => .calling (Machine.PairPreparation.operand [] input.first input.firstTail)
      (Machine.PairPreparation.operand [] input.second input.secondTail) (.responding (.running packetMachine)))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by simp [TimedExecution.eval, step, Machine.PreparationCheck.final, packetMachine, PMF.pure_map])

noncomputable def whole (input : Machine.PreparationCheck.FailureInput) :=
  ((preparation code oracle machine state trace request input).seq
    (handoff code oracle machine state trace request input) (fun _ _ _ => rfl)
    (fun _ => 1) (fun _ _ _ => Nat.le_refl _)).seq
    ((delivery code oracle machine state trace request
      (Machine.PairPreparation.operand [] input.first input.firstTail)
      (Machine.PairPreparation.operand [] input.second input.secondTail)).reindex (fun _ => ()))
    (fun _ _ _ => rfl) (fun _ => 13) (fun _ _ _ => Nat.le_refl _)

theorem budget (input : Machine.PreparationCheck.FailureInput) :
    (whole code oracle machine state trace request input).budget () =
      12 * Machine.PreparationCheck.consumed input + 24 := by
  simp [whole, preparation, Procedure.seq, Procedure.liftBoundary, Procedure.ofFixed]

theorem whole_semantics (input : Machine.PreparationCheck.FailureInput) :
    (whole code oracle machine state trace request input).semantics () =
      PMF.pure (((), ()), ([false], ())) := by
  simp [whole, preparation, handoff, delivery, NativeCallback.callback,
    NativeCallback.exported, NativeCallback.transfer, packetReady, Machine.Procedure.ofFixed,
    Procedure.seq, Procedure.reindex, Procedure.ofFixed, Procedure.liftBoundary,
    Procedure.transport, Procedure.frame, PMF.pure_map]

def resumed (input : Machine.PreparationCheck.FailureInput) : Control State :=
  .calling (Machine.PairPreparation.operand [] input.first input.firstTail)
    (Machine.PairPreparation.operand [] input.second input.secondTail)
    (.source (NativeCallback.resumed machine state trace request [false]))

theorem return_distribution (input : Machine.PreparationCheck.FailureInput) :
    ((whole code oracle machine state trace request input).costed ()).map
      (fun result => (whole code oracle machine state trace request input).exit () result.1) =
      PMF.pure (resumed machine state trace request input) := by
  have h := congrArg (fun distribution => distribution.map
    ((whole code oracle machine state trace request input).exit ()))
    ((whole code oracle machine state trace request input).correct ())
  rw [whole_semantics, PMF.pure_map] at h
  have he : (whole code oracle machine state trace request input).exit () (((), ()), ([false], ())) =
      resumed machine state trace request input := by rfl
  rw [he] at h
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- Actual return costs are retained. Remaining fuel runs the resumed source,
so the return boundary is not made absorbing in the surrounding machine. -/
theorem resume_law (input : Machine.PreparationCheck.FailureInput) (horizon : Nat)
    (hBudget : 12 * Machine.PreparationCheck.consumed input + 24 ≤ horizon) :
    TimedExecution.eval (step code oracle machine state trace request) horizon
      (.preparing (.preparing (.reading
        (Machine.PairPreparation.operand [] input.first input.firstTail)
        (Machine.PairPreparation.operand [] input.second input.secondTail) {}))) =
      ((whole code oracle machine state trace request input).costed ()).bind
        (fun result => TimedExecution.eval (step code oracle machine state trace request)
          (horizon - result.2) (resumed machine state trace request input)) := by
  have h := (whole code oracle machine state trace request input).law () horizon
    (by rw [budget]; exact hBudget)
  change TimedExecution.eval _ _ ((whole code oracle machine state trace request input).entry ()) = _
  rw [h]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  have hs := (whole code oracle machine state trace request input).result_support () result hResult
  rw [whole_semantics, PMF.mem_support_pure_iff] at hs
  rw [hs]
  rfl

end CryptoOracle.Interactive.FailureCallback
