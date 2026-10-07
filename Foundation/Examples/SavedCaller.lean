import Foundation.Examples.ProcedureCall
import Foundation.Crypto.Semantics.Framing
import Foundation.Examples.NativeSequence

/-! A real native sampler executes with a full caller configuration retained.
All tape cells and head positions of the caller remain unchanged. Its data is
not passed to the native instruction function as a branching input. -/
namespace Foundation.SavedCallerExamples
open Foundation.Probability TimedExecution
open Foundation.Symmetric.EncryptThenMAC
open PrimitiveContracts
open Machine

noncomputable def sampler := ProcedureCall.savedProcedure Configuration oneBitKeygen
  (fun _ _ _ => rfl) ProcedureCallExamples.bitRead (fun _ bit => by cases bit <;> rfl)

theorem budget (raw : List Bool) (caller : Configuration) : sampler.budget (raw, caller) = 3 := rfl

theorem run (raw : List Bool) (caller : Configuration) :
    eval (framedStep (ProcedureCall.step oneBitKeygen.code)) 3
      (.running (Configuration.initial raw), caller) =
    sampleBit.map (fun bit => (ProcedureCall.Control.returned (IntegrityEncryption.keyFinish raw bit), caller)) :=
  ProcedureCall.saved_run oneBitKeygen (fun _ _ _ => rfl) ProcedureCallExamples.bitRead
    (fun _ bit => by cases bit <;> rfl) raw caller 3 (Nat.le_refl _)

theorem caller_retained (raw : List Bool) (caller : Configuration) (fuel : Nat)
    (final : ProcedureCall.Control × Configuration)
    (hFinal : final ∈ (eval (framedStep (ProcedureCall.step oneBitKeygen.code)) fuel
      (.running (Configuration.initial raw), caller)).support) : final.2 = caller :=
  framed_saved _ fuel _ caller final hFinal

noncomputable def sequence := NativeSequenceExamples.whole.frame Configuration

theorem sequence_budget (raw : List Bool) (caller : Configuration) :
    sequence.budget (raw, caller) = 8 := rfl

theorem sequence_run (raw : List Bool) (caller : Configuration) :
    eval (framedStep Sequence.step) 8
      (.running [oneBitKeygen.code, NativeSequenceExamples.flipCode] (Configuration.initial raw), caller) =
    sampleBit.map (fun bit => (Sequence.Control.returned
      (Sequence.restart (NativeSequenceExamples.flipFinish (raw, bit) (!bit))), caller)) := by
  rw [framed_eval, NativeSequenceExamples.whole_run, PMF.map_comp]
  rfl

end Foundation.SavedCallerExamples
