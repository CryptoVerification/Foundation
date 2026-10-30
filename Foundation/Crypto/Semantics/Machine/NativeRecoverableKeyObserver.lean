import Foundation.Crypto.Semantics.Machine.NativeRecoverableKeySampler
import Foundation.Crypto.Semantics.Machine.NativeKeyPairObserver

/-! A native recovery caller rewinds the three retained key cells, reads the
new key, and writes its parent/source bit. No host predicate is an instruction. -/
namespace Machine.NativeRecoverableKeyObserver
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def accepts (bits : Fin 3 → Bool) : Bool :=
  match NativeEightBitCipher.decodeKey bits with
  | none => false
  | some key => Recoverable.parent key

theorem accepts_encoded (key : Fin 5) : accepts (NativeEightBitCipher.encodeKey key) = Recoverable.parent key := by
  simp [accepts, NativeEightBitCipher.decode_encodeKey]

def decoder : Program := compile 3 (fun bits => NativeKeyPairObserver.leaf (accepts bits))
abbrev rewind := NativeKeyPairObserver.rewind
def code : Program := rewind.followedBy decoder

theorem decoder_stops : StopsEverywhere decoder 12 :=
  NativeBitDecoderTotal.compile_stops_everywhere 3 _ 3 (fun bits => NativeKeyPairObserver.leaf_stops (accepts bits))

theorem stops : StopsEverywhere code 23 :=
  NativeUniformSequence.stops rewind decoder 10 12 NativeKeyPairObserver.rewind_stops decoder_stops

theorem run (key : Fin 3 → Bool) (inputSuffix output : Tape) :
    evalConfigWithin code (NativeBitChoice.start (NativeKeyPairObserver.keyed key inputSuffix) output) 23 =
      PMF.pure {pc := rewind.length + decoder.length + 2, inputTape := NativeKeyPairObserver.keyed key inputSuffix, outputTape := (output.write (some (accepts key))).moveRight, halted := true} := by
  unfold code
  rw [NativeUniformSequence.run rewind decoder 10 12 NativeKeyPairObserver.rewind_stops decoder_stops]
  have hr := NativePrivateHistoryErasure.run [.left,.left,.left] (NativeKeyPairObserver.keyed key inputSuffix) output
  rw [NativeKeyPairObserver.rewind_tape] at hr
  change evalConfigWithin rewind (NativeBitChoice.start (NativeKeyPairObserver.keyed key inputSuffix) output) 10 = _ at hr
  rw [hr, PMF.pure_bind]
  change (evalConfigWithin (compile 3 (fun bits => NativeKeyPairObserver.leaf (accepts bits)))
    (NativeBitChoice.start (preload (List.ofFn key) inputSuffix) output) 12).map _ = _
  rw [compile_run 3 _ 3 (fun bits input output => NativeKeyPairObserver.leaf_stops _ input output),
    NativeKeyPairObserver.leaf_run, NativeKeyPairObserver.after_read_key, PMF.pure_map, PMF.pure_map]
  rfl

theorem code_length : code.length ≤ 85 := by
  have hd := compile_length_bound 3 (fun bits => NativeKeyPairObserver.leaf (accepts bits)) 3 (fun _ => by rfl)
  change decoder.length + 6 ≤ 9 * 2 ^ 3 at hd
  have hr : rewind.length = 16 := NativePrivateHistoryErasure.code_length [.left,.left,.left]
  unfold code
  rw [NativeUniformSequence.code_length, hr]
  omega

end Machine.NativeRecoverableKeyObserver
