import Foundation.Crypto.Semantics.Oracle.SourceCallback
import Foundation.Examples.SourceEntry

/-! Full execution in the outer source controller: real call, physical
operand preparation, native XOR, response, resumption and native halt.
This is a one-call operational example; key generation/use policy is separate. -/
namespace Foundation.SourceCallbackExamples
open Foundation.Probability TimedExecution
open CryptoOracle.Interactive
open Machine.OneTimePad.Prepared
universe u
set_option backward.isDefEq.respectTransparency false

variable {State : Type u} (oracle : BitOracle State) (sourceInput : Machine.Tape) (state : State)
    (trace : List (List Bool × List Bool))

def sourceMachine (input : Machine.PairPreparation.Input) :=
  SourceEntryExamples.machine sourceInput input.second input.secondTail

noncomputable def call (input : Machine.PairPreparation.Input) :=
  SourceEntry.invoke SourceEntryExamples.code oracle (sourceMachine sourceInput input).advance state trace input.second
    listProcedure id (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ machine => machine.outputBits) (fun _ output => finish_output _ output [])
    (fun input => input.first.length)
    (fun input output h => by
      change output ∈ (PMF.pure (Machine.OneTimePad.xorList input.first input.second)).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      exact le_of_eq (xorList_length input.first input.second input.sameLength)) id (fun _ => rfl)
    (sourceMachine sourceInput input) (Machine.PairPreparation.operand [] input.first input.firstTail)
    input rfl rfl rfl rfl rfl rfl

theorem call_semantics (input : Machine.PairPreparation.Input) :
    (call oracle sourceInput state trace input).semantics () =
      PMF.pure ((), ((((input, ()), ()), Machine.OneTimePad.xorList input.first input.second), ())) := by
  simp [call, SourceEntry.invoke, SourceEntry.handler, SourceEntry.body, SourceEntry.preparationPrefix,
    SourceEntry.preparationBody, SourceEntry.preparationHandoff, SourceEntry.exportBody, SourceEntry.reply,
    NativeCallback.exported, listProcedure, Machine.Procedure.ofFixed, Procedure.seq, Procedure.reindex,
    Procedure.remember, Procedure.liftBoundary, Procedure.frame, Machine.PairPreparation.procedure,
    Procedure.ofFixed, PMF.pure_map]

def final (input : Machine.PairPreparation.Input) (packet : List Bool) : SourceEntry.Control State :=
  .source (Machine.PairPreparation.operand [] input.first input.firstTail)
    ⟨state, .running { (sourceMachine sourceInput input).advance with
      outputTape := ResponseLoading.loaded packet, halted := true }, (input.second, packet) :: trace⟩

noncomputable def stop : Procedure (SourceEntry.step listProcedure.code SourceEntryExamples.code oracle)
    (Machine.PairPreparation.Input × List Bool) Unit :=
  Procedure.ofFixed _
    (fun input => .source (Machine.PairPreparation.operand [] input.1.first input.1.firstTail)
      (NativeCallback.resumed (sourceMachine sourceInput input.1).advance state trace input.1.second input.2))
    (fun input _ => final sourceInput state trace input.1 input.2) (fun _ => PMF.pure ()) (fun _ => 1)
    (fun input => by
      simp [TimedExecution.eval, SourceEntry.step, NativeCallback.resumed, sourceMachine,
        SourceEntryExamples.machine, SourceEntryExamples.code, Reification.timedStep,
        Reification.terminal, Reification.perform, Reification.action, transition,
        Machine.Configuration.advance, Machine.Instruction.next, final, PMF.pure_map])

noncomputable def complete (input : Machine.PairPreparation.Input) :=
  (call oracle sourceInput state trace input).seq
    ((stop oracle sourceInput state trace).reindex (fun result => (result.2.1.1.1.1, result.2.1.2)))
    (fun _ result hResult => by
      rw [call_semantics, PMF.mem_support_pure_iff] at hResult
      subst result
      rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem budget (input : Machine.PairPreparation.Input) :
    (complete oracle sourceInput state trace input).budget () = 28 * input.first.length + 19 := by
  change (2 * input.second.length + 4) +
    ((12 * input.first.length + 3 + 1) + (8 * input.first.length + 2 + (3 * input.first.length + 4)) +
      (3 * input.first.length + 4)) + 1 = _
  have h := input.sameLength
  omega

theorem run (input : Machine.PairPreparation.Input) :
    TimedExecution.eval (SourceEntry.step listProcedure.code SourceEntryExamples.code oracle)
      (28 * input.first.length + 19)
      (.source (Machine.PairPreparation.operand [] input.first input.firstTail)
        ⟨state, .running (sourceMachine sourceInput input), trace⟩) =
      PMF.pure (final sourceInput state trace input (Machine.OneTimePad.xorList input.first input.second)) := by
  have h := (complete oracle sourceInput state trace input).final_run ()
    (fun _ _ => by
      simp [complete, stop, final, Procedure.seq, Procedure.reindex, Procedure.ofFixed,
        SourceEntry.step, Reification.timedStep, Reification.terminal, PMF.pure_map])
    (28 * input.first.length + 19) (by rw [budget])
  simp only [complete, Procedure.seq] at h
  rw [call_semantics] at h
  simpa [call, SourceEntry.invoke, stop, final, Procedure.seq, Procedure.reindex, Procedure.ofFixed, PMF.pure_map] using h

theorem pad_run (width : Nat) (key message : Foundation.Symmetric.Bits width)
    (keyTail messageTail : List (Option Bool)) :
    TimedExecution.eval (SourceEntry.step listProcedure.code SourceEntryExamples.code oracle) (28 * width + 19)
      (.source (Machine.PairPreparation.operand [] key.toList keyTail)
        ⟨state, .running (SourceEntryExamples.machine sourceInput message.toList messageTail), trace⟩) =
      PMF.pure (final sourceInput state trace (PreparedCallbackExamples.operands key message keyTail messageTail)
        (Foundation.Symmetric.OneTimePad.encrypt key message).toList) := by
  simpa only [PreparedCallbackExamples.operands, Foundation.Symmetric.Bits.length_toList, sourceMachine,
    Foundation.Symmetric.OneTimePad.encrypt, Machine.OneTimePad.toList_xor] using
    SourceCallbackExamples.run oracle sourceInput state trace (PreparedCallbackExamples.operands key message keyTail messageTail)

def terminal : SourceEntry.Control State → Bool
  | .source _ frame => Reification.terminal frame.control
  | _ => false

theorem source_stops (input : Machine.PairPreparation.Input) (endpoint : SourceEntry.Control State)
    (hEndpoint : endpoint ∈ (TimedExecution.eval (SourceEntry.step listProcedure.code SourceEntryExamples.code oracle)
      (28 * input.first.length + 19) (.source (Machine.PairPreparation.operand [] input.first input.firstTail)
        ⟨state, .running (sourceMachine sourceInput input), trace⟩)).support) : terminal endpoint = true := by
  rw [run, PMF.mem_support_pure_iff] at hEndpoint
  subst endpoint
  rfl

end Foundation.SourceCallbackExamples
