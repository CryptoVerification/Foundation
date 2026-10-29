import Foundation.Crypto.Semantics.Machine.NativeControlledCipherInitial
import Foundation.Crypto.Semantics.Machine.NativePrivateHistoryErasure

/-! A continuing native execution erases consumed request and coin history.
The complete formatted-entry result law factors through the key/ciphertext pair.
The retained key remains private; this is not a key-hidden security theorem. -/
namespace Machine.NativeCleanEightBitCipher
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

abbrev source := NativeControlledEightBitCipher.code

attribute [local irreducible] NativeControlledEightBitCipher.code

def code : Program := source.followedBy NativePrivateHistoryErasure.cleanup

def finish (pc : ℕ) (result : Fin 5 × Bool) (inputSuffix outputSuffix : Tape) : Configuration :=
  let key := NativeEightBitCipher.encodeKey result.1
  {pc := pc,
   inputTape := {inputSuffix with left := some (key 2) :: some (key 1) :: some (key 0) ::
     (List.replicate 27 none ++ inputSuffix.left)},
   outputTape := {outputSuffix with left := some result.2 :: outputSuffix.left}, halted := true}

theorem finish_resume (pc : ℕ) (result : Fin 5 × Bool) (inputSuffix outputSuffix : Tape) :
    (finish pc result inputSuffix outputSuffix).resumeAt 0 =
      (finish 0 result inputSuffix outputSuffix).resumeAt 0 := rfl

def sourceFinish (v : OrderedGridVertex 32) (message : Bool) (bits : Fin 8 → Bool)
    (inputSuffix outputSuffix : Tape) : Configuration :=
  finishControl 19 NativeControlledEightBitCipher.leaves
    (NativeRandomPrivateResult.finish 8 (NativeEightBitCipher.payload v message) bits
      (afterRead (List.ofFn (EightBitCipherControl.request v message)) inputSuffix) outputSuffix)

theorem source_run (v : OrderedGridVertex 32) (message : Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin source (NativeControlledEightBitCipher.entry v message inputSuffix outputSuffix) 148 =
      (uniform (Fin 8 → Bool)).map (fun bits => sourceFinish v message bits inputSuffix outputSuffix) := by
  unfold source
  rw [NativeControlledEightBitCipher.code_def]
  unfold NativeControlledEightBitCipher.entry
  rw [compile_run 19 _ 91 (fun word input output => NativeControlledEightBitCipher.leaves_stops word input output),
    NativeControlledEightBitCipher.leaves_request, NativeBitGenerator.afterRead_blankBlock,
    NativePrivateBitResult.afterRead_keyBuffer]
  change (evalConfigWithin (NativeRandomPrivateResult.code 8 (NativeEightBitCipher.payload v message))
    (NativeBitChoice.start
      (NativeBitGenerator.blankBlock 8 (NativePrivateBitResult.keyBuffer
        (afterRead (List.ofFn (EightBitCipherControl.request v message)) inputSuffix)))
      (NativePrivateBitResult.outputBuffer outputSuffix)) 91).map _ = _
  rw [NativeRandomPrivateResult.run, PMF.map_comp]
  rfl

theorem cleanup_run (pc : ℕ) (v : OrderedGridVertex 32) (message : Bool) (bits : Fin 8 → Bool)
    (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin NativePrivateHistoryErasure.cleanup
      ((sourceFinish v message bits inputSuffix outputSuffix).resumeAt 0) 262).map
        (fun d => {d with pc := pc, halted := true}) =
      PMF.pure (finish pc (tableEightBitResult v message bits) inputSuffix outputSuffix) := by
  let key := NativeEightBitCipher.encodeKey (tableEightBitResult v message bits).1
  let history := (List.ofFn bits).reverse.map some ++
    (List.ofFn (EightBitCipherControl.request v message)).reverse.map some
  have history_length : history.length = 27 := by simp [history]
  have hc := NativePrivateHistoryErasure.protected_cells
    [some (key 2), some (key 1), some (key 0)] history inputSuffix.left inputSuffix.current inputSuffix.right
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, history_length] at hc
  change (evalConfigWithin (NativePrivateHistoryErasure.code
      (NativePrivateHistoryErasure.protectedActions 3 27))
    (NativeBitChoice.start
      {inputSuffix with left := [some (key 2), some (key 1), some (key 0)] ++ history ++ inputSuffix.left}
      {outputSuffix with left := some (tableEightBitResult v message bits).2 :: outputSuffix.left})
    (3 * (NativePrivateHistoryErasure.protectedActions 3 27).length + 1)).map _ = _
  rw [NativePrivateHistoryErasure.run, PMF.pure_map, hc]
  rfl

theorem run (v : OrderedGridVertex 32) (message : Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin code (NativeControlledEightBitCipher.entry v message inputSuffix outputSuffix) 411 =
      (tableEightBitLaw v message).map (fun result => finish (source.length + NativePrivateHistoryErasure.cleanup.length + 2) result inputSuffix outputSuffix) := by
  unfold code NativeControlledEightBitCipher.entry
  rw [show 411 = 148 + 262 + 1 from rfl,
    NativeUniformSequence.run _ _ _ _ NativeControlledEightBitCipher.code_stops
      NativePrivateHistoryErasure.cleanup_stops]
  change (evalConfigWithin source (NativeControlledEightBitCipher.entry v message inputSuffix outputSuffix) 148).bind _ = _
  rw [source_run, PMF.bind_map]
  simp only [Function.comp_def]
  simp only [cleanup_run]
  unfold tableEightBitLaw
  rw [PMF.map_comp]
  rfl

theorem stops : StopsEverywhere code 411 :=
  NativeUniformSequence.stops source NativePrivateHistoryErasure.cleanup 148 262
    NativeControlledEightBitCipher.code_stops NativePrivateHistoryErasure.cleanup_stops

theorem observe_finish (pc : ℕ) (result : Fin 5 × Bool) (inputSuffix outputSuffix : Tape) :
    NativeEightBitCipher.observe (finish pc result inputSuffix outputSuffix) = some result := by
  change NativeEightBitCipher.decodeResult
    (some (NativeEightBitCipher.encodeKey result.1, result.2)) = _
  simp [NativeEightBitCipher.decodeResult, NativeEightBitCipher.decode_encodeKey]

theorem observed_run (v : OrderedGridVertex 32) (message : Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin code (NativeControlledEightBitCipher.entry v message inputSuffix outputSuffix) 411).map
      NativeEightBitCipher.observe = (tableEightBitLaw v message).map some := by
  rw [run, PMF.map_comp]
  congr 1
  funext result
  exact observe_finish _ result inputSuffix outputSuffix

theorem initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin code
      (Configuration.initial (List.ofFn (EightBitCipherControl.request v message))) 411).map
      NativeEightBitCipher.observe = (tableEightBitLaw v message).map some := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativeControlledCipherInitial.entry_equivalent v message).symm 411 _
    NativeControlledCipherInitial.observe_equivalent]
  exact observed_run v message {} {}

theorem haltsWithin (input : List Bool) : HaltsWithin code input 411 :=
  stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 411
  polynomial := PolynomiallyBounded.const 411
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

end Machine.NativeCleanEightBitCipher
