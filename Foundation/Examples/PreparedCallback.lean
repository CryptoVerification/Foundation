import Foundation.Crypto.Semantics.Oracle.PreparedCallback
import Foundation.Crypto.Semantics.Machine.PreparedXor
import Foundation.Examples.NativeCallback

/-! Separate operand tapes become a real native input, then a returned
ciphertext and a resumed source. Restored operands remain physically saved. -/
namespace Foundation.PreparedCallbackExamples
open Foundation.Probability TimedExecution
open CryptoOracle.Interactive
open Machine.OneTimePad.Prepared
universe u
set_option backward.isDefEq.respectTransparency false

variable {State : Type u} (oracle : BitOracle State) (sourceInput : Machine.Tape) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

noncomputable def respond :=
  PreparedCallback.whole (code := NativeCallbackExamples.code) (oracle := oracle)
    (machine := NativeCallbackExamples.caller sourceInput) (state := state) (trace := trace) (request := request)
    listProcedure id (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ machine => machine.outputBits) (fun _ output => finish_output _ output [])
    (fun input => input.first.length)
    (fun input output h => by
      change output ∈ (PMF.pure (Machine.OneTimePad.xorList input.first input.second)).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      exact le_of_eq (xorList_length input.first input.second input.sameLength))
    id (fun _ => rfl)

def stopped (input : Machine.PairPreparation.Input) (packet : List Bool) : PreparedCallback.Control State :=
  .calling (Machine.PairPreparation.operand [] input.first input.firstTail)
    (Machine.PairPreparation.operand [] input.second input.secondTail)
    (NativeCallbackExamples.final sourceInput state trace request packet)

noncomputable def stop : Procedure (PreparedCallback.step listProcedure.code NativeCallbackExamples.code oracle
    (NativeCallbackExamples.caller sourceInput) state trace request)
    (Machine.PairPreparation.Input × List Bool) Unit :=
  Procedure.ofFixed _
    (fun input => .calling (Machine.PairPreparation.operand [] input.1.first input.1.firstTail)
      (Machine.PairPreparation.operand [] input.1.second input.1.secondTail)
      (.source (NativeCallback.resumed (NativeCallbackExamples.caller sourceInput) state trace request input.2)))
    (fun input _ => stopped sourceInput state trace request input.1 input.2)
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun input => by
      have h := eval_map
        (NativeCallback.step listProcedure.code NativeCallbackExamples.code oracle
          (NativeCallbackExamples.caller sourceInput) state trace request)
        (PreparedCallback.step listProcedure.code NativeCallbackExamples.code oracle
          (NativeCallbackExamples.caller sourceInput) state trace request)
        (PreparedCallback.Control.calling (Machine.PairPreparation.operand [] input.1.first input.1.firstTail)
          (Machine.PairPreparation.operand [] input.1.second input.1.secondTail))
        (fun _ => rfl) 1
        (.source (NativeCallback.resumed (NativeCallbackExamples.caller sourceInput) state trace request input.2))
      rw [NativeCallbackExamples.source_halts _ oracle sourceInput state trace request input.2 1 (by omega), PMF.pure_map] at h
      simpa only [stopped, PMF.pure_map] using h.symm)

noncomputable def complete :=
  (respond oracle sourceInput state trace request).seq
    ((stop oracle sourceInput state trace request).reindex (fun result => (result.1.1.1, result.2.1)))
    (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem budget (input : Machine.PairPreparation.Input) :
    (complete oracle sourceInput state trace request).budget input = 26 * input.first.length + 14 := by
  change (12 * input.first.length + 3 + 1) + (8 * input.first.length + 2 +
    (6 * input.first.length + 7)) + 1 = _
  omega

theorem run (input : Machine.PairPreparation.Input) :
    TimedExecution.eval (PreparedCallback.step listProcedure.code NativeCallbackExamples.code oracle
      (NativeCallbackExamples.caller sourceInput) state trace request) (26 * input.first.length + 14)
      (.preparing (Machine.PairPreparation.procedure.entry input)) =
      PMF.pure (stopped sourceInput state trace request input (Machine.OneTimePad.xorList input.first input.second)) := by
  have h := (complete oracle sourceInput state trace request).final_run input
    (fun output _ => by
      simp [complete, stop, stopped, Procedure.seq, Procedure.reindex, Procedure.ofFixed,
        PreparedCallback.step, NativeCallback.step, NativeCallbackExamples.final,
        Reification.timedStep, Reification.terminal, PMF.pure_map])
    (26 * input.first.length + 14) (by rw [budget])
  simpa [complete, respond, stop, stopped, PreparedCallback.whole, PreparedCallback.preparingPrefix,
    PreparedCallback.preparation, PreparedCallback.handoff, PreparedCallback.embed,
    NativeCallback.callback, NativeCallback.exported, NativeCallback.transfer,
    Machine.PairPreparation.procedure, listProcedure, Machine.Procedure.ofFixed,
    Procedure.seq, Procedure.reindex, Procedure.remember, Procedure.liftBoundary,
    Procedure.transport, Procedure.frame, Procedure.ofFixed, PMF.map, PMF.bind_bind,
    Function.comp_def] using h

def operands {width : Nat} (key message : Foundation.Symmetric.Bits width)
    (keyTail messageTail : List (Option Bool)) : Machine.PairPreparation.Input :=
  ⟨key.toList, message.toList, keyTail, messageTail, by simp⟩

theorem pad_run (width : Nat) (key message : Foundation.Symmetric.Bits width)
    (keyTail messageTail : List (Option Bool)) :
    TimedExecution.eval (PreparedCallback.step listProcedure.code NativeCallbackExamples.code oracle
      (NativeCallbackExamples.caller sourceInput) state trace message.toList) (26 * width + 14)
      (.preparing (.reading (Machine.PairPreparation.operand [] key.toList keyTail)
        (Machine.PairPreparation.operand [] message.toList messageTail) {})) =
      PMF.pure (stopped sourceInput state trace message.toList (operands key message keyTail messageTail)
        (Foundation.Symmetric.OneTimePad.encrypt key message).toList) := by
  simpa only [operands, Foundation.Symmetric.Bits.length_toList, Machine.PairPreparation.procedure,
    Procedure.ofFixed, Foundation.Symmetric.OneTimePad.encrypt, Machine.OneTimePad.toList_xor] using
    PreparedCallbackExamples.run oracle sourceInput state trace message.toList (operands key message keyTail messageTail)

def terminal : PreparedCallback.Control State → Bool
  | .calling _ _ (.source frame) => Reification.terminal frame.control
  | _ => false

theorem source_stops (input : Machine.PairPreparation.Input) (endpoint : PreparedCallback.Control State)
    (hEndpoint : endpoint ∈ (TimedExecution.eval (PreparedCallback.step listProcedure.code NativeCallbackExamples.code oracle
      (NativeCallbackExamples.caller sourceInput) state trace request) (26 * input.first.length + 14)
      (.preparing (Machine.PairPreparation.procedure.entry input))).support) : terminal endpoint = true := by
  rw [run, PMF.mem_support_pure_iff] at hEndpoint
  subst endpoint
  rfl

end Foundation.PreparedCallbackExamples
