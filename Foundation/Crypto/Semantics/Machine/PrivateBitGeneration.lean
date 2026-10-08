import Foundation.Crypto.Semantics.Machine.PrivateInitialization
import Foundation.Crypto.Semantics.Machine.OneTimePad

/-! A fixed native bit sampler instantiates private initialization at any width.
The width is marker input data and does not change the finite code. -/
namespace Machine.PrivateBitGeneration
open Foundation.Probability Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false

noncomputable def native (width : Nat) : Machine.Procedure Unit (Bits width) :=
  Machine.Procedure.ofFixed OneTimePad.keygen
    (fun _ => Configuration.initial (List.replicate width true))
    (fun _ key => OneTimePad.finish 5 (List.replicate width true) key.toList)
    (fun _ => uniform (Bits width)) (fun _ => 5 * width + 2)
    (fun _ => by
      simpa [OneTimePad.state_initial] using OneTimePad.keygen_typed_run width [] [])

theorem halted (width : Nat) (input : Unit) (key : Bits width) :
    ((native width).execution.exit input key).halted = true := rfl

theorem tape (width : Nat) (input : Unit) (key : Bits width) :
    ((native width).execution.exit input key).outputTape = ResponseExport.endTape key.toList := rfl

def read (width : Nat) (_ : Unit) (machine : Configuration) : Bits width :=
  fun index => machine.outputBits[index.val]?.getD false

theorem read_exit (width : Nat) (input : Unit) (key : Bits width) :
    read width input ((native width).execution.exit input key) = key := by
  funext index
  simp [read, native, Machine.Procedure.ofFixed, TimedExecution.Procedure.ofFixed, OneTimePad.finish_output,
    Bits.toList]

noncomputable def procedure (width : Nat) :=
  PrivateInitialization.procedure (native width) Bits.toList (halted width) (tape width)
    (read width) (read_exit width) (fun _ => width) (fun _ key _ => by simp)

theorem budget (width : Nat) : (procedure width).budget () = 6 * width + 4 := by
  unfold procedure
  rw [PrivateInitialization.budget]
  change (5 * width + 2) + width + 2 = _
  omega

theorem distribution (width : Nat) :
    ((procedure width).costed ()).map (fun result => (procedure width).exit () result.1) =
      (uniform (Bits width)).map (fun key => PrivateInitialization.Control.ready
        (ResponseExport.fromCells (key.toList.map some ++ [none]))) := by
  unfold procedure
  rw [PrivateInitialization.distribution]
  rfl
def decode (width : Nat) (tape : Tape) : Bits width := fun index => tape.bits[index.val]?.getD false

theorem decode_store (width : Nat) (key : Bits width) :
    decode width (ResponseExport.fromCells (key.toList.map some ++ [none])) = key := by
  have hBits : (ResponseExport.fromCells (key.toList.map some ++ [none])).bits = key.toList := by
    cases h : key.toList with
    | nil => simp [ResponseExport.fromCells, Tape.bits]
    | cons bit rest => simp [ResponseExport.fromCells, Tape.bits]
  funext index
  unfold decode
  rw [hBits]
  simp [Bits.toList]

end Machine.PrivateBitGeneration
