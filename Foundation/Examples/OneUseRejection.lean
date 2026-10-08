import Foundation.Crypto.Semantics.Oracle.OneUseRejection

/-! An arbitrary malformed-length request is rejected and the resumed
source executes its actual halt instruction. Key generation and source-call
capture precede the entry of this handler example and are not included. -/
namespace Foundation.OneUseRejectionExamples
open Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false

def code : Code := [.native .halt]

def saved (sourceInput : Machine.Tape) (input : Machine.PreparationCheck.FailureInput) :
    Machine.Configuration :=
  { inputTape := sourceInput,
    outputTape := Machine.PairPreparation.operand [] input.second input.secondTail }

variable {State : Type u} (native : Machine.Program) (oracle : BitOracle State) (sourceInput : Machine.Tape) (state : State)
    (trace : List (List Bool × List Bool))

def final (input : Machine.PreparationCheck.FailureInput) : OneUseSource.Control State :=
  .source false (Machine.PairPreparation.operand [] input.first input.firstTail)
    ⟨state, .running { (saved sourceInput input) with
      outputTape := ResponseLoading.loaded [false], halted := true }, (input.second, [false]) :: trace⟩

noncomputable def stop (input : Machine.PreparationCheck.FailureInput) :
    Procedure (OneUseSource.step native code oracle) Unit Unit :=
  Procedure.ofFixed _
    (fun _ => OneUseRejection.resumed (saved sourceInput input) state trace input.second input)
    (fun _ _ => final sourceInput state trace input)
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by
      simp [TimedExecution.eval, OneUseSource.step, OneUseRejection.resumed,
        NativeCallback.resumed, saved, code, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, Machine.Instruction.next, final, PMF.pure_map])

noncomputable def complete (input : Machine.PreparationCheck.FailureInput) :=
  (OneUseRejection.whole native code oracle (saved sourceInput input) state trace input.second input).seq
    ((stop native oracle sourceInput state trace input).reindex (fun _ => ()))
    (fun _ result hResult => by
      rw [OneUseRejection.whole_semantics, PMF.mem_support_pure_iff] at hResult
      subst result
      rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem budget (input : Machine.PreparationCheck.FailureInput) :
    (complete native oracle sourceInput state trace input).budget () =
      12 * Machine.PreparationCheck.consumed input + 26 := by
  change (OneUseRejection.whole native code oracle (saved sourceInput input) state trace input.second input).budget () + 1 = _
  rw [OneUseRejection.budget]

theorem run (input : Machine.PreparationCheck.FailureInput) :
    TimedExecution.eval (OneUseSource.step native code oracle)
      (12 * Machine.PreparationCheck.consumed input + 26)
      (.handling false (saved sourceInput input) state trace input.second (.preparing (.preparing (.reading
        (Machine.PairPreparation.operand [] input.first input.firstTail)
        (Machine.PairPreparation.operand [] input.second input.secondTail) {})))) =
      PMF.pure (final sourceInput state trace input) := by
  have h := (complete native oracle sourceInput state trace input).final_run ()
    (fun _ _ => by
      simp [complete, stop, Procedure.seq, Procedure.reindex, Procedure.ofFixed,
        OneUseSource.step, Reification.timedStep, Reification.terminal,
        final, PMF.pure_map])
    (12 * Machine.PreparationCheck.consumed input + 26) (by rw [budget])
  simp only [complete, Procedure.seq] at h
  rw [OneUseRejection.whole_semantics] at h
  simpa [stop, Procedure.reindex, Procedure.ofFixed, PMF.pure_map,
    OneUseRejection.whole, OneUseRejection.preparation, OneUseRejection.embedFailure, Procedure.seq, Procedure.liftBoundary] using h

def terminal : OneUseSource.Control State → Bool
  | .source _ _ frame => Reification.terminal frame.control
  | _ => false

theorem source_stops (input : Machine.PreparationCheck.FailureInput) :
    ∀ result ∈ (TimedExecution.eval
      (OneUseSource.step native code oracle)
      (12 * Machine.PreparationCheck.consumed input + 26)
      (.handling false (saved sourceInput input) state trace input.second (.preparing (.preparing (.reading
        (Machine.PairPreparation.operand [] input.first input.firstTail)
        (Machine.PairPreparation.operand [] input.second input.secondTail) {}))))).support,
      terminal result = true := by
  rw [run]
  intro result hResult
  rw [PMF.mem_support_pure_iff] at hResult
  subst result
  rfl

theorem unused_after_stop (input : Machine.PreparationCheck.FailureInput) :
    ∀ result ∈ (TimedExecution.eval (OneUseSource.step native code oracle)
      (12 * Machine.PreparationCheck.consumed input + 26)
      (.handling false (saved sourceInput input) state trace input.second (.preparing (.preparing (.reading
        (Machine.PairPreparation.operand [] input.first input.firstTail)
        (Machine.PairPreparation.operand [] input.second input.secondTail) {}))))).support,
      OneUseSource.used result = false := by
  rw [run]
  intro result hResult
  rw [PMF.mem_support_pure_iff] at hResult
  subst result
  rfl

end Foundation.OneUseRejectionExamples
