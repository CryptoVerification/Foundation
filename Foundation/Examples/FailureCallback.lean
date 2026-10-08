import Foundation.Crypto.Semantics.Oracle.FailureCallback

/-! An arbitrary malformed-length request is rejected and the resumed
source executes its actual halt instruction. Key generation and source-call
capture precede the entry of this handler example and are not included. -/
namespace Foundation.FailureCallbackExamples
open Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u

def code : Code := [.native .halt]

def saved (sourceInput : Machine.Tape) (input : Machine.PreparationCheck.FailureInput) :
    Machine.Configuration :=
  { inputTape := sourceInput,
    outputTape := Machine.PairPreparation.operand [] input.second input.secondTail }

variable {State : Type u} (oracle : BitOracle State) (sourceInput : Machine.Tape) (state : State)
    (trace : List (List Bool × List Bool))

def final (input : Machine.PreparationCheck.FailureInput) : FailureCallback.Control State :=
  .calling (Machine.PairPreparation.operand [] input.first input.firstTail)
    (Machine.PairPreparation.operand [] input.second input.secondTail)
    (.source ⟨state, .running { (saved sourceInput input) with
      outputTape := ResponseLoading.loaded [false], halted := true }, (input.second, [false]) :: trace⟩)

noncomputable def stop (input : Machine.PreparationCheck.FailureInput) :
    Procedure (FailureCallback.step code oracle (saved sourceInput input) state trace input.second) Unit Unit :=
  Procedure.ofFixed _
    (fun _ => FailureCallback.resumed (saved sourceInput input) state trace input.second input)
    (fun _ _ => final sourceInput state trace input)
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by
      simp [TimedExecution.eval, FailureCallback.step, FailureCallback.resumed, NativeCallback.step,
        NativeCallback.resumed, saved, code, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, Machine.Instruction.next, final, PMF.pure_map])

noncomputable def complete (input : Machine.PreparationCheck.FailureInput) :=
  (FailureCallback.whole code oracle (saved sourceInput input) state trace input.second input).seq
    ((stop oracle sourceInput state trace input).reindex (fun _ => ()))
    (fun _ result hResult => by
      rw [FailureCallback.whole_semantics, PMF.mem_support_pure_iff] at hResult
      subst result
      rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem budget (input : Machine.PreparationCheck.FailureInput) :
    (complete oracle sourceInput state trace input).budget () =
      12 * Machine.PreparationCheck.consumed input + 25 := by
  change (FailureCallback.whole code oracle (saved sourceInput input) state trace input.second input).budget () + 1 = _
  rw [FailureCallback.budget]

theorem run (input : Machine.PreparationCheck.FailureInput) :
    TimedExecution.eval (FailureCallback.step code oracle (saved sourceInput input) state trace input.second)
      (12 * Machine.PreparationCheck.consumed input + 25)
      (.preparing (.preparing (.reading
        (Machine.PairPreparation.operand [] input.first input.firstTail)
        (Machine.PairPreparation.operand [] input.second input.secondTail) {}))) =
      PMF.pure (final sourceInput state trace input) := by
  have h := (complete oracle sourceInput state trace input).final_run ()
    (fun _ _ => by
      simp [complete, stop, Procedure.seq, Procedure.reindex, Procedure.ofFixed,
        FailureCallback.step, NativeCallback.step, Reification.timedStep, Reification.terminal,
        final, PMF.pure_map])
    (12 * Machine.PreparationCheck.consumed input + 25) (by rw [budget])
  simp only [complete, Procedure.seq] at h
  rw [FailureCallback.whole_semantics] at h
  simpa [stop, Procedure.reindex, Procedure.ofFixed, PMF.pure_map,
    FailureCallback.whole, FailureCallback.preparation, Procedure.seq, Procedure.liftBoundary] using h

def terminal : FailureCallback.Control State → Bool
  | .calling _ _ (.source frame) => Reification.terminal frame.control
  | _ => false

theorem source_stops (input : Machine.PreparationCheck.FailureInput) :
    ∀ result ∈ (TimedExecution.eval
      (FailureCallback.step code oracle (saved sourceInput input) state trace input.second)
      (12 * Machine.PreparationCheck.consumed input + 25)
      (.preparing (.preparing (.reading
        (Machine.PairPreparation.operand [] input.first input.firstTail)
        (Machine.PairPreparation.operand [] input.second input.secondTail) {})))).support,
      terminal result = true := by
  rw [run]
  intro result hResult
  rw [PMF.mem_support_pure_iff] at hResult
  subst result
  rfl

end Foundation.FailureCallbackExamples
