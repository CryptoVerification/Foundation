import Foundation.Crypto.Semantics.Machine.NativeFiveStateSampler
import Foundation.Crypto.Semantics.Machine.NativeCleanFairRecovery
import Foundation.Crypto.Semantics.Machine.NativePrivateHistoryErasure
import Foundation.Crypto.Semantics.Machine.NativePreparedState

/-! Uniform physical erasure for a five-state sampler with twelve fresh bits.
The clean exit retains all inherited tape frames, the sampled key, ciphertext,
and actual control. No label-preservation assumption is needed for erasure. -/
namespace Machine.NativeCleanFiveStateSampler
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence

abbrev cleanup := NativeCleanFairRecovery.cleanup

theorem cleanup_stops : StopsEverywhere cleanup 163 := NativeCleanFairRecovery.cleanup_stops

theorem cleanup_length : cleanup.length = 271 := NativeCleanFairRecovery.cleanup_length

def code (draw : NativeFiveStateSampler.Sampler) : Program := (NativeFiveStateSampler.code draw).followedBy cleanup

abbrev finish := NativeCleanFairRecovery.finish

theorem cleanup_run (pc : Nat) (draw : NativeFiveStateSampler.Sampler) (key : Fin 5) (ciphertext : Bool)
    (inputSuffix outputSuffix : Tape) (coins : Fin 12 → Bool) :
    (evalConfigWithin cleanup
      ((NativeFiveStateSampler.finish draw key ciphertext inputSuffix outputSuffix coins).resumeAt 0) 163).map
        (fun c => {c with pc := pc, halted := true}) =
      PMF.pure (finish pc (draw key coins) ciphertext inputSuffix outputSuffix) := by
  let encoded := NativeEightBitCipher.encodeKey (draw key coins)
  let history := (List.ofFn coins).reverse.map some ++ (NativeFiveStateSampler.rawInput key ciphertext).reverse.map some
  have history_length : history.length = 16 := by
    simp [history,NativeFiveStateSampler.rawInput]
  have hc := NativePrivateHistoryErasure.protected_cells
    [some (encoded 2),some (encoded 1),some (encoded 0)] history
    inputSuffix.left inputSuffix.current inputSuffix.right
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd,history_length] at hc
  have handoff : (NativeFiveStateSampler.finish draw key ciphertext inputSuffix outputSuffix coins).resumeAt 0 =
      NativeBitChoice.start
        {inputSuffix with left := some (encoded 2) :: some (encoded 1) :: some (encoded 0) :: (history ++ inputSuffix.left)}
        {outputSuffix with left := some ciphertext :: outputSuffix.left} := by
    rw [NativeFiveStateSampler.finish, NativeRecoverableKeySampler.finishControl_resume]
    simp only [NativeRandomPrivateResult.finish, NativePrivateBitResult.bufferedFinish, Configuration.resumeAt, NativeBitChoice.start]
    simp only [afterRead, NativeFiveStateSampler.payload, encoded, history, List.append_assoc]
  rw [handoff, show 163 = 3 * (NativePrivateHistoryErasure.protectedActions 3 16).length + 1 by
    rw [NativePrivateHistoryErasure.protected_length]]
  unfold cleanup NativeCleanFairRecovery.cleanup
  rw [NativePrivateHistoryErasure.run,PMF.pure_map]
  simp only [List.cons_append,List.nil_append] at hc
  rw [hc]
  rfl

theorem full_run (draw : NativeFiveStateSampler.Sampler) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (code draw) (NativeFiveStateSampler.entry key ciphertext inputSuffix outputSuffix) 307 =
      (NativeFiveStateSampler.kernel draw key).map (fun result =>
        finish ((NativeFiveStateSampler.code draw).length + cleanup.length + 2) result ciphertext inputSuffix outputSuffix) := by
  unfold code NativeFiveStateSampler.entry
  rw [show 307 = 143 + 163 + 1 from rfl,
    NativeUniformSequence.run _ _ 143 163 (NativeFiveStateSampler.stops draw) cleanup_stops]
  change (evalConfigWithin (NativeFiveStateSampler.code draw)
    (NativeFiveStateSampler.entry key ciphertext inputSuffix outputSuffix) 143).bind _ = _
  rw [NativeFiveStateSampler.full_run,PMF.bind_map]
  simp only [Function.comp_def,cleanup_run]
  rw [← NativeFiveStateSampler.sample_law draw key,PMF.map_comp]
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

theorem framed_law (draw : NativeFiveStateSampler.Sampler) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin (code draw) (NativeFiveStateSampler.entry key ciphertext inputSuffix outputSuffix) 307).map
      NativeEightBitCipher.observe = (NativeFiveStateSampler.kernel draw key).map (fun result => some (result,ciphertext)) := by
  rw [full_run,PMF.map_comp]
  congr 1
  funext result
  exact observe_finish _ result ciphertext inputSuffix outputSuffix

theorem initial_state_law (draw : NativeFiveStateSampler.Sampler) (key : Fin 5) (ciphertext : Bool) :
    (evalConfigWithin (code draw) (Configuration.initial (NativeFiveStateSampler.rawInput key ciphertext)) 307).map
      NativePreparedState.state = (NativeFiveStateSampler.kernel draw key).map (fun result => NativePreparedState.state
        (finish ((NativeFiveStateSampler.code draw).length + cleanup.length + 2) result ciphertext {} {})) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativeFiveStateSampler.entry_equivalent key ciphertext).symm
    307 _ NativePreparedState.state_equivalent,full_run,PMF.map_comp]
  rfl

theorem cleanup_coin_independent (draw : NativeFiveStateSampler.Sampler) (key : Fin 5) (ciphertext : Bool)
    (inputSuffix outputSuffix : Tape) (coins other : Fin 12 → Bool)
    (same : draw key coins = draw key other) :
    evalConfigWithin cleanup ((NativeFiveStateSampler.finish draw key ciphertext inputSuffix outputSuffix coins).resumeAt 0) 163 =
      evalConfigWithin cleanup ((NativeFiveStateSampler.finish draw key ciphertext inputSuffix outputSuffix other).resumeAt 0) 163 := by
  have left := cleanup_run (cleanup.length - 1) draw key ciphertext inputSuffix outputSuffix coins
  have right := cleanup_run (cleanup.length - 1) draw key ciphertext inputSuffix outputSuffix other
  have fixed (c : Configuration) :
      (evalConfigWithin cleanup (c.resumeAt 0) 163).map (fun d => {d with pc := cleanup.length - 1,halted := true}) =
        evalConfigWithin cleanup (c.resumeAt 0) 163 := by
    change (evalConfigWithin (NativePrivateHistoryErasure.code (NativePrivateHistoryErasure.protectedActions 3 16))
      (NativeBitChoice.start c.inputTape c.outputTape) (3 * (NativePrivateHistoryErasure.protectedActions 3 16).length + 1)).map _ = _
    change _ = evalConfigWithin (NativePrivateHistoryErasure.code (NativePrivateHistoryErasure.protectedActions 3 16))
      (NativeBitChoice.start c.inputTape c.outputTape) (3 * (NativePrivateHistoryErasure.protectedActions 3 16).length + 1)
    rw [NativePrivateHistoryErasure.run,PMF.pure_map]
    simp only [cleanup, NativeCleanFairRecovery.cleanup]
  rw [fixed] at left right
  exact left.trans ((congrArg PMF.pure (congrArg (fun result =>
    finish (cleanup.length - 1) result ciphertext inputSuffix outputSuffix) same)).trans right.symm)

theorem stops (draw : NativeFiveStateSampler.Sampler) : StopsEverywhere (code draw) 307 :=
  NativeUniformSequence.stops _ _ 143 163 (NativeFiveStateSampler.stops draw) cleanup_stops

theorem code_length (draw : NativeFiveStateSampler.Sampler) : (code draw).length ≤ 985484 := by
  have h := NativeFiveStateSampler.code_length draw
  rw [code,NativeUniformSequence.code_length,cleanup_length]
  omega

theorem haltsWithin (draw : NativeFiveStateSampler.Sampler) (input : List Bool) : HaltsWithin (code draw) input 307 :=
  stops draw (Tape.ofBits input) {}

def bounded (draw : NativeFiveStateSampler.Sampler) : CryptoLogic.BoundedProgram where
  program := code draw
  budget := fun _ => 307
  polynomial := PolynomiallyBounded.const 307
  halts := haltsWithin draw

theorem polynomial_time (draw : NativeFiveStateSampler.Sampler) : PolynomialTime (code draw) := (bounded draw).polynomialTime

end Machine.NativeCleanFiveStateSampler
