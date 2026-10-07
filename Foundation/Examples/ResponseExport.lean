import Foundation.Crypto.Semantics.Machine.ResponseExport
import Foundation.Crypto.Semantics.VectorEncoding
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrimitiveContracts

/-! Random sampling and arbitrary-width pad encryption use the same physical
response exporter. The caller and private store can be retained jointly.
Encryption input layout is still an explicit entry precondition. -/
namespace Foundation.ResponseExportExamples
open Foundation.Probability TimedExecution
open Foundation.Symmetric Foundation.Symmetric.EncryptThenMAC
open PrimitiveContracts Machine

def readVector (width : Nat) (_ : Input) (machine : Configuration) : Bits width :=
  (Encoding.vector Bool width).observe (fun _ => false) machine.outputBits

noncomputable def sampler (width : Nat) : Machine.Procedure (List Bool) (Bits width) :=
  ⟨(bitstringKeygen width).code,
    (bitstringKeygen width).execution.reindex (fun retained => ⟨retained, []⟩)⟩

theorem sampler_read (width : Nat) (retained : List Bool) (key : Bits width) :
    readVector width retained ((sampler width).execution.exit retained key) = key := by
  change (Encoding.vector Bool width).observe (fun _ => false)
    (OneTimePad.finish 5 _ ([] ++ key.toList)).outputBits = key
  rw [OneTimePad.finish_output]
  exact (Encoding.vector Bool width).observe_encode _ key

theorem sampler_run (width : Nat) (retained : List Bool) :
    eval (ResponseExport.step (sampler width).code) (8 * width + 6)
      (.running ((sampler width).execution.entry retained)) =
      (uniform (Bits width)).map (fun key => ResponseExport.Control.returned key.toList) := by
  apply ResponseExport.whole_run (sampler width) Bits.toList
    (fun _ _ => rfl) (fun _ _ => rfl) (readVector width) (sampler_read width)
    (fun _ => width) (fun _ _ _ => by simp) retained
  change 5 * width + 2 + (3 * width + 4) ≤ 8 * width + 6
  omega

structure PadInput (width : Nat) where
  key : Bits width
  message : Bits width
  retainedInput : List Bool

noncomputable def encryptor (width : Nat) : Machine.Procedure (PadInput width) (Bits width) :=
  ⟨(padEncrypt width).code,
    (padEncrypt width).execution.reindex
      (fun input => ⟨input.key, input.message, ⟨input.retainedInput, []⟩⟩)⟩

theorem encryptor_read (width : Nat) (input : PadInput width) (ciphertext : Bits width) :
    readVector width input ((encryptor width).execution.exit input ciphertext) = ciphertext := by
  change (Encoding.vector Bool width).observe (fun _ => false)
    (Machine.OneTimePad.finish 16 _ ([] ++ ciphertext.toList)).outputBits = ciphertext
  rw [Machine.OneTimePad.finish_output]
  exact (Encoding.vector Bool width).observe_encode _ ciphertext

theorem encryptor_run (width : Nat) (input : PadInput width) :
    eval (ResponseExport.step (encryptor width).code) (11 * width + 6)
      (.running ((encryptor width).execution.entry input)) =
      PMF.pure (ResponseExport.Control.returned (OneTimePad.encrypt input.key input.message).toList) := by
  have h := ResponseExport.whole_run (encryptor width) Bits.toList
    (fun _ _ => rfl) (fun _ _ => rfl) (readVector width) (encryptor_read width)
    (fun _ => width) (fun _ _ _ => by simp) input (11 * width + 6)
    (by change 8 * width + 2 + (3 * width + 4) ≤ 11 * width + 6; omega)
  simpa only [encryptor, padEncrypt, Machine.Procedure.ofFixed,
    TimedExecution.Procedure.ofFixed, TimedExecution.Procedure.reindex, Function.comp_def, PMF.pure_map] using h

/-- The component and exporter cannot inspect the saved caller or key store. -/
theorem encryptor_saved_run (width : Nat) (input : PadInput width)
    (caller : Configuration) (privateStore : Tape) :
    eval (framedStep (ResponseExport.step (encryptor width).code)) (11 * width + 6)
      (.running ((encryptor width).execution.entry input), (caller, privateStore)) =
      PMF.pure (ResponseExport.Control.returned (OneTimePad.encrypt input.key input.message).toList,
        (caller, privateStore)) := by
  rw [framed_eval, encryptor_run, PMF.pure_map]

end Foundation.ResponseExportExamples
