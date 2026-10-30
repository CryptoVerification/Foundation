import Foundation.Crypto.Semantics.Machine.NativeFairRecoverySampler
import Foundation.Crypto.Semantics.Machine.NativePrivateHistoryErasure
import Foundation.Crypto.Semantics.Machine.NativePreparedState

/-! Physically erase all four request and twelve random cells after either
fair recovery sampler. The complete clean exit, including control and both
tapes, depends only on the sampled key, ciphertext and inherited frames. -/
namespace Machine.NativeCleanFairRecovery
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence

def cleanup : Program := NativePrivateHistoryErasure.code (NativePrivateHistoryErasure.protectedActions 3 16)

theorem cleanup_stops : StopsEverywhere cleanup 163 := by
  have h := NativePrivateHistoryErasure.stops (NativePrivateHistoryErasure.protectedActions 3 16)
  rw [NativePrivateHistoryErasure.protected_length] at h
  exact h

theorem cleanup_length : cleanup.length = 271 := by
  unfold cleanup
  rw [NativePrivateHistoryErasure.code_length, NativePrivateHistoryErasure.protected_length]

def code (backward : Bool) : Program := (NativeFairRecoverySampler.code backward).followedBy cleanup

def finish (pc : Nat) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) : Configuration :=
  let encoded := NativeEightBitCipher.encodeKey key
  {pc := pc,
   inputTape := {inputSuffix with left := some (encoded 2) :: some (encoded 1) :: some (encoded 0) ::
     (List.replicate 16 none ++ inputSuffix.left)},
   outputTape := {outputSuffix with left := some ciphertext :: outputSuffix.left}, halted := true}

theorem cleanup_run (pc : Nat) (backward : Bool) (key : Fin 5) (ciphertext : Bool)
    (inputSuffix outputSuffix : Tape) (coins : Fin 12 → Bool) :
    (evalConfigWithin cleanup
      ((NativeFairRecoverySampler.finish backward key ciphertext inputSuffix outputSuffix coins).resumeAt 0) 163).map
        (fun c => {c with pc := pc, halted := true}) =
      PMF.pure (finish pc (NativeFairRecoverySampler.sample backward key coins) ciphertext inputSuffix outputSuffix) := by
  let encoded := NativeEightBitCipher.encodeKey (NativeFairRecoverySampler.sample backward key coins)
  let history := (List.ofFn coins).reverse.map some ++ (NativeFairRecoverySampler.rawInput key ciphertext).reverse.map some
  have history_length : history.length = 16 := by
    simp [history,NativeFairRecoverySampler.rawInput]
  have hc := NativePrivateHistoryErasure.protected_cells
    [some (encoded 2),some (encoded 1),some (encoded 0)] history
    inputSuffix.left inputSuffix.current inputSuffix.right
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd,history_length] at hc
  have handoff : (NativeFairRecoverySampler.finish backward key ciphertext inputSuffix outputSuffix coins).resumeAt 0 =
      NativeBitChoice.start
        {inputSuffix with left := some (encoded 2) :: some (encoded 1) :: some (encoded 0) :: (history ++ inputSuffix.left)}
        {outputSuffix with left := some ciphertext :: outputSuffix.left} := by
    rw [NativeFairRecoverySampler.finish, NativeRecoverableKeySampler.finishControl_resume]
    simp only [NativeRandomPrivateResult.finish, NativePrivateBitResult.bufferedFinish, Configuration.resumeAt, NativeBitChoice.start]
    simp only [afterRead, NativeFairRecoverySampler.payload, encoded, history, List.append_assoc]
  rw [handoff, show 163 = 3 * (NativePrivateHistoryErasure.protectedActions 3 16).length + 1 by
    rw [NativePrivateHistoryErasure.protected_length]]
  unfold cleanup
  rw [NativePrivateHistoryErasure.run,PMF.pure_map]
  simp only [List.cons_append,List.nil_append] at hc
  rw [hc]
  rfl

theorem full_run (backward : Bool) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (code backward) (NativeFairRecoverySampler.entry key ciphertext inputSuffix outputSuffix) 307 =
      (NativeFairRecoverySampler.kernel backward key).map (fun result =>
        finish ((NativeFairRecoverySampler.code backward).length + cleanup.length + 2) result ciphertext inputSuffix outputSuffix) := by
  unfold code NativeFairRecoverySampler.entry
  rw [show 307 = 143 + 163 + 1 from rfl,
    NativeUniformSequence.run _ _ 143 163 (NativeFairRecoverySampler.stops backward) cleanup_stops]
  change (evalConfigWithin (NativeFairRecoverySampler.code backward)
    (NativeFairRecoverySampler.entry key ciphertext inputSuffix outputSuffix) 143).bind _ = _
  rw [NativeFairRecoverySampler.full_run,PMF.bind_map]
  simp only [Function.comp_def,cleanup_run]
  rw [← NativeFairRecoverySampler.sample_law backward key,PMF.map_comp]
  rfl

theorem observe_finish (pc : Nat) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    NativeEightBitCipher.observe (finish pc key ciphertext inputSuffix outputSuffix) = some (key,ciphertext) := by
  have encoded : ![NativeEightBitCipher.encodeKey key 0,NativeEightBitCipher.encodeKey key 1,
      NativeEightBitCipher.encodeKey key 2] = NativeEightBitCipher.encodeKey key := by
    funext i
    fin_cases i <;> rfl
  change NativeEightBitCipher.decodeResult
    (some (![NativeEightBitCipher.encodeKey key 0,NativeEightBitCipher.encodeKey key 1,
      NativeEightBitCipher.encodeKey key 2],ciphertext)) = _
  rw [encoded]
  simp [NativeEightBitCipher.decodeResult,NativeEightBitCipher.decode_encodeKey]

theorem framed_law (backward : Bool) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin (code backward) (NativeFairRecoverySampler.entry key ciphertext inputSuffix outputSuffix) 307).map
      NativeEightBitCipher.observe = (NativeFairRecoverySampler.kernel backward key).map (fun result => some (result,ciphertext)) := by
  rw [full_run,PMF.map_comp]
  congr 1
  funext result
  exact observe_finish _ result ciphertext inputSuffix outputSuffix

theorem initial_state_law (backward : Bool) (key : Fin 5) (ciphertext : Bool) :
    (evalConfigWithin (code backward) (Configuration.initial (NativeFairRecoverySampler.rawInput key ciphertext)) 307).map
      NativePreparedState.state = (NativeFairRecoverySampler.kernel backward key).map (fun result => NativePreparedState.state
        (finish ((NativeFairRecoverySampler.code backward).length + cleanup.length + 2) result ciphertext {} {})) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativeFairRecoverySampler.entry_equivalent key ciphertext).symm
    307 _ NativePreparedState.state_equivalent,full_run,PMF.map_comp]
  rfl

theorem cleanup_coin_independent (backward : Bool) (key : Fin 5) (ciphertext : Bool)
    (inputSuffix outputSuffix : Tape) (coins other : Fin 12 → Bool)
    (same : NativeFairRecoverySampler.sample backward key coins = NativeFairRecoverySampler.sample backward key other) :
    evalConfigWithin cleanup ((NativeFairRecoverySampler.finish backward key ciphertext inputSuffix outputSuffix coins).resumeAt 0) 163 =
      evalConfigWithin cleanup ((NativeFairRecoverySampler.finish backward key ciphertext inputSuffix outputSuffix other).resumeAt 0) 163 := by
  have left := cleanup_run (cleanup.length - 1) backward key ciphertext inputSuffix outputSuffix coins
  have right := cleanup_run (cleanup.length - 1) backward key ciphertext inputSuffix outputSuffix other
  have fixed (c : Configuration) :
      (evalConfigWithin cleanup (c.resumeAt 0) 163).map (fun d => {d with pc := cleanup.length - 1,halted := true}) =
        evalConfigWithin cleanup (c.resumeAt 0) 163 := by
    change (evalConfigWithin (NativePrivateHistoryErasure.code (NativePrivateHistoryErasure.protectedActions 3 16))
      (NativeBitChoice.start c.inputTape c.outputTape) (3 * (NativePrivateHistoryErasure.protectedActions 3 16).length + 1)).map _ = _
    change _ = evalConfigWithin (NativePrivateHistoryErasure.code (NativePrivateHistoryErasure.protectedActions 3 16))
      (NativeBitChoice.start c.inputTape c.outputTape) (3 * (NativePrivateHistoryErasure.protectedActions 3 16).length + 1)
    rw [NativePrivateHistoryErasure.run,PMF.pure_map]
    simp only [cleanup]
  rw [fixed] at left right
  exact left.trans ((congrArg PMF.pure (congrArg (fun result =>
    finish (cleanup.length - 1) result ciphertext inputSuffix outputSuffix) same)).trans right.symm)

theorem stops (backward : Bool) : StopsEverywhere (code backward) 307 :=
  NativeUniformSequence.stops _ _ 143 163 (NativeFairRecoverySampler.stops backward) cleanup_stops

theorem code_length (backward : Bool) : (code backward).length ≤ 985484 := by
  have h := NativeFairRecoverySampler.code_length backward
  rw [code,NativeUniformSequence.code_length,cleanup_length]
  omega

theorem haltsWithin (backward : Bool) (input : List Bool) : HaltsWithin (code backward) input 307 :=
  stops backward (Tape.ofBits input) {}

def bounded (backward : Bool) : CryptoLogic.BoundedProgram where
  program := code backward
  budget := fun _ => 307
  polynomial := PolynomiallyBounded.const 307
  halts := haltsWithin backward

theorem polynomial_time (backward : Bool) : PolynomialTime (code backward) := (bounded backward).polynomialTime

end Machine.NativeCleanFairRecovery
