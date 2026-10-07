import Foundation.Crypto.Semantics.Machine.Sequence
import Foundation.Examples.ProcedureCall

/-! Two different native programs share a physical output tape. The second
reads the sampled bit in place and flips it. No host-side preparation occurs
between programs; both controller handoffs and final completion are charged. -/
namespace Foundation.NativeSequenceExamples
open Foundation.Probability TimedExecution
open Foundation.Symmetric.EncryptThenMAC
open PrimitiveContracts
open Machine

def flipCode : Program :=
  [.branch .output 5 1 3, .write .output true, .halt,
   .write .output false, .halt, .halt]

def flipFinish (input : List Bool × Bool) (output : Bool) : Configuration :=
  { IntegrityEncryption.keyFinish input.1 output with pc := if input.2 then 4 else 2 }

noncomputable def flip : Machine.Procedure (List Bool × Bool) Bool :=
  Machine.Procedure.ofFixed flipCode
    (fun input => Sequence.restart (IntegrityEncryption.keyFinish input.1 input.2))
    flipFinish (fun input => PMF.pure (!input.2)) (fun _ => 3)
    (fun input => by
      rcases input with ⟨raw, bit⟩
      cases bit <;>
        simp [evalConfigWithin, stepPMF, next, flipCode, Sequence.restart,
          IntegrityEncryption.keyFinish, flipFinish, Instruction.next, Configuration.tape,
          Configuration.updateTape, Configuration.advance, Tape.write, PMF.pure_map])

def flipRead (_ : List Bool × Bool) (machine : Configuration) : Bool :=
  machine.outputTape.current.getD false

theorem flipRead_exit (input : List Bool × Bool) (output : Bool) :
    flipRead input (flip.execution.exit input output) = output := by
  cases output <;> rfl

noncomputable def twoStages := Sequence.chain oneBitKeygen flip []
  (fun _ _ => rfl) (fun _ _ => rfl)
  ProcedureCallExamples.bitRead flipRead
  (fun _ bit => by cases bit <;> rfl) flipRead_exit id
  (fun _ _ => rfl) (fun _ => 4) (fun _ _ _ => Nat.le_refl _)

theorem twoStages_budget (raw : List Bool) : twoStages.budget raw = 7 := rfl

noncomputable def whole := twoStages.seq
  (Sequence.finish.reindex (fun result =>
    Sequence.restart (flip.execution.exit result.2.1.1 result.2.1.2)))
  (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem whole_budget (raw : List Bool) : whole.budget raw = 8 := rfl

theorem whole_run (raw : List Bool) :
    eval Sequence.step 8 (.running [oneBitKeygen.code, flipCode] (Configuration.initial raw)) =
      sampleBit.map (fun bit => Sequence.Control.returned
        (Sequence.restart (flipFinish (raw, bit) (!bit)))) := by
  have h := whole.final_run raw (fun _ _ => rfl) 8 (Nat.le_refl _)
  simpa [whole, twoStages, Sequence.chain, Sequence.stage, Sequence.body, Sequence.handoff,
    Sequence.finish, TimedExecution.Procedure.seq, TimedExecution.Procedure.remember,
    TimedExecution.Procedure.reindex, TimedExecution.Procedure.ofFixed,
    TimedExecution.Procedure.liftBoundary, flip, oneBitKeygen, Machine.Procedure.ofFixed,
    PMF.map, PMF.bind_bind, Function.comp_def] using h

end Foundation.NativeSequenceExamples
