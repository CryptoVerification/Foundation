import Foundation.Crypto.Semantics.Machine.NativeEightBitKeyWitness
import Foundation.Crypto.Semantics.Machine.NativePrivateHistoryErasure

/-! An actual finite caller reads the retained three-bit key, tests the two
labels 0 and 2, and writes its decision to the current reserved output cell.
Both tape heads' movements, output placement and stopping are charged. -/
namespace Machine.NativeKeyPairObserver
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def accepts (bits : Fin 3 → Bool) : Bool :=
  match NativeEightBitCipher.decodeKey bits with
  | none => false
  | some key => decide (key = 0 ∨ key = 2)

theorem accepts_encoded (key : Fin 5) (ciphertext : Bool) :
    accepts (NativeEightBitCipher.encodeKey key) = keyPairTest (key, ciphertext) := by
  simp [accepts, NativeEightBitCipher.decode_encodeKey, keyPairTest]

def leaf (decision : Bool) : Program := [.write .output decision, .moveRight .output, .halt]

def leafFinish (decision : Bool) (input output : Tape) : Configuration :=
  {pc := 2, inputTape := input, outputTape := (output.write (some decision)).moveRight, halted := true}

theorem leaf_run (decision : Bool) (input output : Tape) :
    evalConfigWithin (leaf decision) (NativeBitChoice.start input output) 3 =
      PMF.pure (leafFinish decision input output) := by
  simp [leaf, leafFinish, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
    Instruction.next, Configuration.updateTape, Configuration.advance]

theorem leaf_stops (decision : Bool) : StopsEverywhere (leaf decision) 3 := by
  intro input output finish trace
  have h := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  rw [leaf_run, PMF.mem_support_pure_iff] at h
  subst finish
  rfl

def decoder : Program := compile 3 (fun bits => leaf (accepts bits))

def rewind : Program := NativePrivateHistoryErasure.code [.left, .left, .left]

def code : Program := rewind.followedBy decoder

theorem decoder_stops : StopsEverywhere decoder 12 :=
  NativeBitDecoderTotal.compile_stops_everywhere 3 _ 3 (fun bits => leaf_stops (accepts bits))

theorem rewind_stops : StopsEverywhere rewind 10 :=
  NativePrivateHistoryErasure.stops [.left, .left, .left]

theorem stops : StopsEverywhere code 23 :=
  NativeUniformSequence.stops rewind decoder 10 12 rewind_stops decoder_stops

def keyed (key : Fin 3 → Bool) (suffix : Tape) : Tape :=
  {suffix with left := some (key 2) :: some (key 1) :: some (key 0) :: suffix.left}

theorem rewind_tape (key : Fin 3 → Bool) (suffix : Tape) :
    NativePrivateHistoryErasure.applyActions [.left, .left, .left] (keyed key suffix) =
      preload (List.ofFn key) suffix := by
  change ({left := suffix.left, current := some (key 0), right := some (key 1) :: some (key 2) :: suffix.current :: suffix.right} : Tape) = _
  rw [show List.ofFn key = [key 0, key 1, key 2] from rfl]
  rfl

theorem after_read_key (key : Fin 3 → Bool) (suffix : Tape) :
    afterRead (List.ofFn key) suffix = keyed key suffix := by
  rw [show List.ofFn key = [key 0, key 1, key 2] from rfl]
  rfl

theorem run (key : Fin 3 → Bool) (inputSuffix output : Tape) :
    evalConfigWithin code (NativeBitChoice.start (keyed key inputSuffix) output) 23 =
      PMF.pure {pc := rewind.length + decoder.length + 2, inputTape := keyed key inputSuffix, outputTape := (output.write (some (accepts key))).moveRight, halted := true} := by
  unfold code
  rw [NativeUniformSequence.run rewind decoder 10 12 rewind_stops decoder_stops]
  have hr := NativePrivateHistoryErasure.run [.left, .left, .left] (keyed key inputSuffix) output
  rw [rewind_tape] at hr
  change evalConfigWithin rewind (NativeBitChoice.start (keyed key inputSuffix) output) 10 = _ at hr
  rw [hr, PMF.pure_bind]
  change (evalConfigWithin (compile 3 (fun bits => leaf (accepts bits)))
    (NativeBitChoice.start (preload (List.ofFn key) inputSuffix) output) 12).map _ = _
  rw [compile_run 3 _ 3 (fun bits input output => leaf_stops _ input output),
    leaf_run, after_read_key, PMF.pure_map, PMF.pure_map]
  rfl

theorem run_reserved (key : Fin 3 → Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin code
      (NativeBitChoice.start (keyed key inputSuffix) (NativePrivateBitResult.outputBuffer outputSuffix)) 23 =
      PMF.pure {pc := rewind.length + decoder.length + 2, inputTape := keyed key inputSuffix, outputTape := {outputSuffix with left := some (accepts key) :: outputSuffix.left}, halted := true} := by
  rw [run, NativePrivateBitResult.writeOutput_buffer]

theorem code_length_bound : code.length ≤ 85 := by
  have hd := compile_length_bound 3 (fun bits => leaf (accepts bits)) 3 (fun bits => by rfl)
  change decoder.length + 6 ≤ (3 + 6) * 2 ^ 3 at hd
  have hr : rewind.length = 16 := NativePrivateHistoryErasure.code_length [.left, .left, .left]
  unfold code
  rw [NativeUniformSequence.code_length, hr]
  omega

end Machine.NativeKeyPairObserver
