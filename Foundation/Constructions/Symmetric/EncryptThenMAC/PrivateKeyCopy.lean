import Foundation.Crypto.Semantics.Machine.RetainedCopy
import Foundation.Crypto.Semantics.Machine.RetainedCopyComponent

/-! Compatibility names for the shared native copy implementation. Secret
keys must still be copied into a private destination. The finite instructions,
physical layouts and existing public theorem names are preserved. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivateKeyCopy
open Machine Foundation.Probability

def code : Program :=
  [.branch .input 8 1 3,
   .write .output false, .jump 5,
   .write .output true, .jump 5,
   .moveRight .input, .moveRight .output, .jump 0,
   .moveLeft .input, .branch .input 10 8 8,
   .moveRight .input, .halt]

def copying (before remaining : List Bool) (outputBefore : List (Option Bool)) : Configuration :=
  { inputTape := { Tape.ofBits remaining with left := before.reverse.map some },
    outputTape := { left := outputBefore } }

def rewinding (left : List Bool) (current : Option Bool) (right : List (Option Bool))
    (output : Tape) : Configuration :=
  { pc := 8, inputTape := ⟨left.map some, current, right⟩, outputTape := output }

def restored (cells : List (Option Bool)) : Tape :=
  ⟨[none], cells.headD none, cells.tail⟩

theorem code_eq_shared : code = Machine.RetainedCopy.code := rfl

noncomputable def component : Machine.NativeComponent (List Bool × List (Option Bool)) Machine.Configuration :=
  Machine.RetainedCopy.Component.component

theorem component_code : component.procedure.code = code := rfl

def finish (key : List Bool) (outputBefore : List (Option Bool)) : Configuration :=
  { pc := 11, halted := true, inputTape := restored (key.map some ++ [none]),
    outputTape := { left := key.reverse.map some ++ outputBefore } }

theorem copy_cell (bit : Bool) (before remaining : List Bool)
    (outputBefore : List (Option Bool)) :
    evalConfigWithin code (copying before (bit :: remaining) outputBefore) 6 =
      PMF.pure (copying (before ++ [bit]) remaining (some bit :: outputBefore)) := by
  exact Machine.RetainedCopy.copy_cell bit before remaining outputBefore

theorem copy_loop (before remaining : List Bool) (outputBefore : List (Option Bool)) :
    evalConfigWithin code (copying before remaining outputBefore) (6 * remaining.length + 1) =
      PMF.pure (rewinding (before ++ remaining).reverse none []
        { left := remaining.reverse.map some ++ outputBefore }) := by
  exact Machine.RetainedCopy.copy_loop before remaining outputBefore

theorem rewind_cell (bit : Bool) (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    evalConfigWithin code (rewinding (bit :: left) current right output) 2 =
      PMF.pure (rewinding left (some bit) (current :: right) output) := by
  exact Machine.RetainedCopy.rewind_cell bit left current right output

theorem rewind_loop (left : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    evalConfigWithin code (rewinding left current right output) (2 * left.length + 4) =
      PMF.pure ({ pc := 11, inputTape := restored (left.reverse.map some ++ current :: right), outputTape := output, halted := true } : Configuration) := by
  exact Machine.RetainedCopy.rewind_loop left current right output

theorem run (key : List Bool) (outputBefore : List (Option Bool)) :
    evalConfigWithin code (copying [] key outputBefore) (8 * key.length + 5) =
      PMF.pure (finish key outputBefore) := by
  exact Machine.RetainedCopy.run key outputBefore

theorem key_restored (key : List Bool) (outputBefore : List (Option Bool)) :
    (finish key outputBefore).inputTape.Equivalent (Tape.ofBits key) := by
  exact Machine.RetainedCopy.key_restored key outputBefore

theorem output_bits (key header : List Bool) :
    (finish key (header.reverse.map some)).outputBits = header ++ key := by
  exact Machine.RetainedCopy.output_bits key header

theorem key_bits (key : List Bool) (outputBefore : List (Option Bool)) :
    (finish key outputBefore).inputTape.bits = key := by
  exact Machine.RetainedCopy.key_bits key outputBefore

theorem halts (key : List Bool) : HaltsWithin code key (8 * key.length + 5) := by
  exact Machine.RetainedCopy.halts key

theorem joint_run (key header : List Bool) :
    (evalConfigWithin code (copying [] key (header.reverse.map some)) (8 * key.length + 5)).map
      (fun final => (final.halted, final.inputTape.bits, final.outputBits)) =
        PMF.pure (true, key, header ++ key) := by
  exact Machine.RetainedCopy.joint_run key header

theorem reusable_run (key header : List Bool) (store : Tape)
    (hStore : store.Equivalent (Tape.ofBits key)) :
    (evalConfigWithin code
      { inputTape := store, outputTape := { left := header.reverse.map some } }
      (8 * key.length + 5)).map
        (fun final => (final.halted, final.inputTape.bits, final.outputBits)) =
          PMF.pure (true, key, header ++ key) := by
  exact Machine.RetainedCopy.reusable_run key header store hStore

end Foundation.Symmetric.EncryptThenMAC.PrivateKeyCopy
