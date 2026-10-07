import Foundation.Crypto.Semantics.Oracle.CheckedResponse
import Foundation.Crypto.Semantics.Machine.PreparedXor

/-! Arbitrary-width XOR in the checked response controller, including the
physical success tag and the resumed source's actual halt instruction.
Operand preparation precedes this component entry. -/
namespace Foundation.CheckedResponseExamples
open Foundation.Probability TimedExecution CryptoOracle.Interactive
open Machine.OneTimePad.Prepared
universe u
set_option backward.isDefEq.respectTransparency false

def code : Code := [.native .halt]

variable {State : Type u} (oracle : BitOracle State) (saved : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool)) (request : List Bool)

def first (input : Machine.PairPreparation.Input) := Machine.PairPreparation.operand [] input.first input.firstTail
def second (input : Machine.PairPreparation.Input) := Machine.PairPreparation.operand [] input.second input.secondTail

theorem xor_halt (input : Machine.PairPreparation.Input) (output : List Bool) :
    (listProcedure.execution.exit input output).halted = true := rfl

theorem xor_tape (input : Machine.PairPreparation.Input) (output : List Bool) :
    (listProcedure.execution.exit input output).outputTape = Machine.ResponseExport.endTape output := rfl

noncomputable def component (input : Machine.PairPreparation.Input) :=
  (CheckedCallback.nativeResponse code oracle saved state trace request listProcedure id
    xor_halt xor_tape
    (fun _ machine => machine.outputBits) (fun _ output => finish_output _ output [])
    (fun input => input.first.length)
    (fun input output h => by
      change output ∈ (PMF.pure (Machine.OneTimePad.xorList input.first input.second)).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      exact le_of_eq (xorList_length input.first input.second input.sameLength))
    (first input) (second input)).reindex (fun _ : Unit => input)

theorem component_semantics (input : Machine.PairPreparation.Input) :
    (component oracle saved state trace request input).semantics () =
      PMF.pure (CheckedCallback.nativeResult input (Machine.OneTimePad.xorList input.first input.second)) := by
  simp only [component, Procedure.reindex, Function.comp_def]
  rw [CheckedCallback.nativeResponse_semantics]
  simp [listProcedure, Machine.Procedure.ofFixed, Procedure.ofFixed, PMF.pure_map]

def final (input : Machine.PairPreparation.Input) : CheckedCallback.Control State :=
  .calling (first input) (second input) (.source
    ⟨state, .running { saved with outputTape := ResponseLoading.loaded (true :: Machine.OneTimePad.xorList input.first input.second), halted := true },
      (request, true :: Machine.OneTimePad.xorList input.first input.second) :: trace⟩)

noncomputable def stop (input : Machine.PairPreparation.Input) (hPC : saved.pc = 0) (hActive : saved.halted = false) :
    Procedure (CheckedCallback.step listProcedure.code code oracle saved state trace request) Unit Unit :=
  Procedure.ofFixed _
    (fun _ => .calling (first input) (second input) (.source
      (NativeCallback.resumed saved state trace request (true :: Machine.OneTimePad.xorList input.first input.second))))
    (fun _ _ => final saved state trace request input) (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by
      simp [TimedExecution.eval, CheckedCallback.step, NativeCallback.step, NativeCallback.resumed,
        code, hPC, hActive, Reification.timedStep, Reification.terminal, Reification.perform,
        Reification.action, transition, Machine.Instruction.next, final, PMF.pure_map])

noncomputable def complete (input : Machine.PairPreparation.Input) (hPC : saved.pc = 0) (hActive : saved.halted = false) :=
  (component oracle saved state trace request input).seq
    ((stop oracle saved state trace request input hPC hActive).reindex (fun _ => ()))
    (fun start result hResult => by
      cases start
      rw [component_semantics, PMF.mem_support_pure_iff] at hResult
      subst result
      rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem budget (input : Machine.PairPreparation.Input) (hPC : saved.pc = 0) (hActive : saved.halted = false) :
    (complete oracle saved state trace request input hPC hActive).budget () = 19 * input.first.length + 25 := by
  change (component oracle saved state trace request input).budget () + 1 = _
  simp only [component, Procedure.reindex, Function.comp_def]
  rw [CheckedCallback.nativeResponse_budget]
  change (8 * input.first.length + 2 + 11 * input.first.length + 22) + 1 = _
  omega

theorem run (input : Machine.PairPreparation.Input) (hPC : saved.pc = 0) (hActive : saved.halted = false) :
    TimedExecution.eval (CheckedCallback.step listProcedure.code code oracle saved state trace request)
      (19 * input.first.length + 25)
      (.computing (first input) (second input) (.running (listProcedure.execution.entry input))) =
      PMF.pure (final saved state trace request input) := by
  have h := (complete oracle saved state trace request input hPC hActive).final_run ()
    (fun _ _ => by
      simp [complete, stop, Procedure.seq, Procedure.reindex, Procedure.ofFixed,
        CheckedCallback.step, NativeCallback.step, Reification.timedStep, Reification.terminal,
        final, PMF.pure_map])
    (19 * input.first.length + 25) (by rw [budget])
  simp only [complete, Procedure.seq] at h
  rw [component_semantics] at h
  simpa [component, stop, Procedure.reindex, Procedure.ofFixed, PMF.pure_map,
    CheckedCallback.nativeResponse, CheckedCallback.rawBody, Procedure.seq,
    Procedure.remember, Procedure.liftBoundary, Procedure.frame, NativeCallback.exported,
    CheckedCallback.embedRaw] using h

def terminal : CheckedCallback.Control State → Bool
  | .calling _ _ (.source frame) => Reification.terminal frame.control
  | _ => false

theorem source_stops (input : Machine.PairPreparation.Input) (hPC : saved.pc = 0) (hActive : saved.halted = false) :
    ∀ result ∈ (TimedExecution.eval (CheckedCallback.step listProcedure.code code oracle saved state trace request)
      (19 * input.first.length + 25)
      (.computing (first input) (second input) (.running (listProcedure.execution.entry input)))).support,
      terminal result = true := by
  rw [run oracle saved state trace request input hPC hActive]
  intro result hResult
  rw [PMF.mem_support_pure_iff] at hResult
  subst result
  rfl

end Foundation.CheckedResponseExamples
