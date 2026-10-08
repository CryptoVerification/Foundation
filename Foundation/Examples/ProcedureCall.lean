import Foundation.Crypto.Semantics.Machine.ProcedureCall
import Foundation.Crypto.Semantics.VectorEncoding
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrimitiveContracts

/-! Two existing finite native programs instantiate the same charged caller.
Readers are observations of the full machine frame, never runtime operations.
Arbitrary retained prefixes and the zero-width case are covered. -/
namespace Foundation.ProcedureCallExamples
open Foundation.Probability TimedExecution
open Foundation.Symmetric Foundation.Symmetric.EncryptThenMAC
open PrimitiveContracts

def bitRead (_ : List Bool) (machine : Machine.Configuration) : Bool :=
  machine.outputTape.current.getD false

noncomputable def bitCall := Machine.ProcedureCall.wholeProcedure oneBitKeygen
  (fun _ _ _ => rfl) bitRead (fun _ bit => by cases bit <;> rfl)

theorem bitCall_budget (raw : List Bool) : bitCall.budget raw = 3 := rfl

theorem bitCall_run (raw : List Bool) :
    eval (Machine.ProcedureCall.step oneBitKeygen.code) 3 (bitCall.entry raw) =
      sampleBit.map (fun bit => Machine.ProcedureCall.Control.returned
        (IntegrityEncryption.keyFinish raw bit)) := by
  apply bitCall.final_run raw _ 3 (Nat.le_refl _)
  intro bit _
  rfl

def vectorRead (width : Nat) (retained : Prefixes) (machine : Machine.Configuration) : Bits width :=
  (Encoding.vector Bool width).observe (fun _ => false)
    (machine.outputBits.drop retained.output.length)

theorem vectorRead_finish (width : Nat) (retained : Prefixes) (key : Bits width) :
    vectorRead width retained
      ((bitstringKeygen width).execution.exit retained key) = key := by
  change (Encoding.vector Bool width).observe (fun _ => false)
    ((Machine.OneTimePad.finish 5 _ (retained.output ++ key.toList)).outputBits.drop retained.output.length) = key
  rw [Machine.OneTimePad.finish_output, List.drop_left]
  exact (Encoding.vector Bool width).observe_encode _ key

noncomputable def vectorCall (width : Nat) :=
  Machine.ProcedureCall.wholeProcedure (bitstringKeygen width)
    (fun _ _ _ => rfl) (vectorRead width) (vectorRead_finish width)

theorem vectorCall_budget (width : Nat) (retained : Prefixes) :
    (vectorCall width).budget retained = 5 * width + 3 := by
  change 5 * width + 2 + 1 = _
  omega

theorem vectorCall_run (width : Nat) (retained : Prefixes) :
    eval (Machine.ProcedureCall.step (bitstringKeygen width).code) (5 * width + 3)
      ((vectorCall width).entry retained) =
    (uniform (Bits width)).map (fun key => Machine.ProcedureCall.Control.returned
      ((bitstringKeygen width).execution.exit retained key)) := by
  apply (vectorCall width).final_run retained _ _ (by rw [vectorCall_budget])
  intro key _
  rfl

end Foundation.ProcedureCallExamples
