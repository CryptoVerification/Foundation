import Foundation.Crypto.Semantics.Machine.NativeRecoverableCouplingExecution
import Foundation.Crypto.Semantics.Machine.NativePrivateHistoryErasure
import Foundation.Crypto.Semantics.Machine.NativePreparedState

/-! Charged physical erasure of the two request and seven coin cells after
the repaired coupling sampler and recovery caller. Every final cell depends
only on the sampled key, request values and original tape frames. This is a
clean exit for this program, not a canonical reference-cipher exit adapter. -/
namespace Machine.NativeCleanRecoverableCoupling
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def cleanup : Program := NativePrivateHistoryErasure.code
  (NativePrivateHistoryErasure.protectedActions 3 9)

theorem cleanup_stops : StopsEverywhere cleanup 100 := by
  have h := NativePrivateHistoryErasure.stops (NativePrivateHistoryErasure.protectedActions 3 9)
  rw [NativePrivateHistoryErasure.protected_length] at h
  exact h

theorem cleanup_length : cleanup.length = 166 := by
  unfold cleanup
  rw [NativePrivateHistoryErasure.code_length, NativePrivateHistoryErasure.protected_length]

def code : Program := NativeRecoverableCouplingExecution.code.followedBy cleanup

def finish (pc : ℕ) (bit ciphertext : Bool) (key : Fin 5)
    (inputSuffix outputSuffix : Tape) : Configuration :=
  let encoded := NativeEightBitCipher.encodeKey key
  {pc := pc,
   inputTape := {inputSuffix with left := some (encoded 2) :: some (encoded 1) :: some (encoded 0) ::
     (List.replicate 9 none ++ inputSuffix.left)},
   outputTape := ({outputSuffix with left := some ciphertext :: outputSuffix.left}.write (some bit)).moveRight,
   halted := true}

theorem cleanup_run (pc : ℕ) (bit ciphertext : Bool) (coins : Fin 7 → Bool)
    (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin cleanup
      ((NativeRecoverableCouplingExecution.finish bit ciphertext inputSuffix outputSuffix coins).resumeAt 0) 100).map
        (fun c => {c with pc := pc, halted := true}) =
      PMF.pure (finish pc bit ciphertext (RecoverableSampler.sample bit coins) inputSuffix outputSuffix) := by
  let encoded := NativeEightBitCipher.encodeKey (RecoverableSampler.sample bit coins)
  let history := (List.ofFn coins).reverse.map some ++
    (NativeRecoverableKeySampler.rawInput bit ciphertext).reverse.map some
  have history_length : history.length = 9 := by
    simp [history, NativeRecoverableKeySampler.rawInput]
  have hc := NativePrivateHistoryErasure.protected_cells
    [some (encoded 2), some (encoded 1), some (encoded 0)] history
    inputSuffix.left inputSuffix.current inputSuffix.right
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, history_length] at hc
  have hi := congrArg Configuration.inputTape
    (NativeRecoverableCouplingExecution.sampler_resume bit ciphertext inputSuffix outputSuffix coins)
  have ho := congrArg Configuration.outputTape
    (NativeRecoverableCouplingExecution.sampler_resume bit ciphertext inputSuffix outputSuffix coins)
  simp only [Configuration.resumeAt, NativeBitChoice.start] at hi ho
  have handoff : (NativeRecoverableCouplingExecution.finish bit ciphertext inputSuffix outputSuffix coins).resumeAt 0 =
      NativeBitChoice.start
        {inputSuffix with left := some (encoded 2) :: some (encoded 1) :: some (encoded 0) ::
          (history ++ inputSuffix.left)}
        (({outputSuffix with left := some ciphertext :: outputSuffix.left}.write (some bit)).moveRight) := by
    simp only [NativeRecoverableCouplingExecution.finish, Configuration.resumeAt, NativeBitChoice.start]
    rw [hi, ho]
    simp only [NativeKeyPairObserver.keyed, NativeRecoverableCouplingExecution.history,
      afterRead, encoded, history, List.append_assoc]
  rw [handoff, show 100 = 3 * (NativePrivateHistoryErasure.protectedActions 3 9).length + 1 by
    rw [NativePrivateHistoryErasure.protected_length]]
  unfold cleanup
  rw [NativePrivateHistoryErasure.run, PMF.pure_map]
  simp only [List.cons_append, List.nil_append] at hc
  rw [hc]
  rfl

theorem full_run (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin code (NativeRecoverableKeySampler.entry bit ciphertext inputSuffix outputSuffix) 212 =
      (Recoverable.forward bit).map (fun key =>
        finish (NativeRecoverableCouplingExecution.code.length + cleanup.length + 2)
          bit ciphertext key inputSuffix outputSuffix) := by
  unfold code NativeRecoverableKeySampler.entry
  rw [show 212 = 111 + 100 + 1 from rfl,
    NativeUniformSequence.run _ _ 111 100 NativeRecoverableCouplingExecution.stops cleanup_stops]
  change (evalConfigWithin NativeRecoverableCouplingExecution.code
    (NativeRecoverableKeySampler.entry bit ciphertext inputSuffix outputSuffix) 111).bind _ = _
  rw [NativeRecoverableCouplingExecution.full_run, PMF.bind_map]
  simp only [Function.comp_def, cleanup_run]
  rw [← RecoverableSampler.sample_law bit, PMF.map_comp]
  rfl

theorem observe_finish (pc : ℕ) (bit ciphertext : Bool) (key : Fin 5) (inputSuffix outputSuffix : Tape) :
    NativeRecoverableCouplingExecution.observe (finish pc bit ciphertext key inputSuffix outputSuffix) =
      (some (key,ciphertext),some bit) := by
  apply Prod.ext
  · change NativeEightBitCipher.observe (NativePreparedInternalResult.withoutDecision
      (finish pc bit ciphertext key inputSuffix outputSuffix)) = some (key,ciphertext)
    unfold NativeEightBitCipher.observe NativePreparedInternalResult.withoutDecision finish NativeRandomPrivateResult.observe
    rw [NativeRecoverableCouplingExecution.written_left]
    change NativeEightBitCipher.decodeResult
      (some (![NativeEightBitCipher.encodeKey key 0, NativeEightBitCipher.encodeKey key 1,
        NativeEightBitCipher.encodeKey key 2],ciphertext)) = _
    have encoded : ![NativeEightBitCipher.encodeKey key 0, NativeEightBitCipher.encodeKey key 1,
        NativeEightBitCipher.encodeKey key 2] = NativeEightBitCipher.encodeKey key := by
      funext i
      fin_cases i <;> rfl
    rw [encoded]
    simp [NativeEightBitCipher.decodeResult, NativeEightBitCipher.decode_encodeKey]
  · change NativeRecoverableCouplingExecution.read _ = _
    simp only [NativeRecoverableCouplingExecution.read, finish,
      NativeRecoverableCouplingExecution.written_left, List.getD_cons_zero]

theorem framed_law (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin code (NativeRecoverableKeySampler.entry bit ciphertext inputSuffix outputSuffix) 212).map
      NativeRecoverableCouplingExecution.observe =
      (Recoverable.forward bit).map (fun key => (some (key,ciphertext),some bit)) := by
  rw [full_run, PMF.map_comp]
  congr 1
  funext key
  exact observe_finish _ bit ciphertext key inputSuffix outputSuffix

theorem initial_law (bit ciphertext : Bool) :
    (evalConfigWithin code (Configuration.initial (NativeRecoverableKeySampler.rawInput bit ciphertext)) 212).map
      NativeRecoverableCouplingExecution.observe =
      (Recoverable.forward bit).map (fun key => (some (key,ciphertext),some bit)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativeRecoverableKeySampler.entry_equivalent bit ciphertext).symm 212 _
      NativeRecoverableCouplingExecution.observe_equivalent]
  exact framed_law bit ciphertext {} {}

theorem initial_state_law (bit ciphertext : Bool) :
    (evalConfigWithin code (Configuration.initial (NativeRecoverableKeySampler.rawInput bit ciphertext)) 212).map
      NativePreparedState.state =
      (Recoverable.forward bit).map (fun key => NativePreparedState.state
        (finish (NativeRecoverableCouplingExecution.code.length + cleanup.length + 2) bit ciphertext key {} {})) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativeRecoverableKeySampler.entry_equivalent bit ciphertext).symm 212 _ NativePreparedState.state_equivalent,
    full_run, PMF.map_comp]
  rfl

theorem cleanup_coin_independent (bit ciphertext : Bool)
    (inputSuffix outputSuffix : Tape) (coins other : Fin 7 → Bool)
    (same_key : RecoverableSampler.sample bit coins = RecoverableSampler.sample bit other) :
    evalConfigWithin cleanup
      ((NativeRecoverableCouplingExecution.finish bit ciphertext inputSuffix outputSuffix coins).resumeAt 0) 100 =
    evalConfigWithin cleanup
      ((NativeRecoverableCouplingExecution.finish bit ciphertext inputSuffix outputSuffix other).resumeAt 0) 100 := by
  -- The cleanup itself has a fixed terminal control position, so the equality
  -- includes every cell and the real control fields, not just an observation.
  have left := cleanup_run (cleanup.length - 1) bit ciphertext coins inputSuffix outputSuffix
  have right := cleanup_run (cleanup.length - 1) bit ciphertext other inputSuffix outputSuffix
  have run_fixed (c : Configuration) :
      (evalConfigWithin cleanup (c.resumeAt 0) 100).map
        (fun d => {d with pc := cleanup.length - 1, halted := true}) =
      evalConfigWithin cleanup (c.resumeAt 0) 100 := by
    change (evalConfigWithin (NativePrivateHistoryErasure.code
      (NativePrivateHistoryErasure.protectedActions 3 9))
      (NativeBitChoice.start c.inputTape c.outputTape)
      (3 * (NativePrivateHistoryErasure.protectedActions 3 9).length + 1)).map _ = _
    change _ = evalConfigWithin (NativePrivateHistoryErasure.code
      (NativePrivateHistoryErasure.protectedActions 3 9))
      (NativeBitChoice.start c.inputTape c.outputTape)
      (3 * (NativePrivateHistoryErasure.protectedActions 3 9).length + 1)
    rw [NativePrivateHistoryErasure.run, PMF.pure_map]
    simp only [cleanup]
  rw [run_fixed] at left right
  exact left.trans ((congrArg PMF.pure (congrArg (fun key =>
    finish (cleanup.length - 1) bit ciphertext key inputSuffix outputSuffix) same_key)).trans right.symm)

theorem stops : StopsEverywhere code 212 :=
  NativeUniformSequence.stops NativeRecoverableCouplingExecution.code cleanup 111 100
    NativeRecoverableCouplingExecution.stops cleanup_stops

theorem haltsWithin (input : List Bool) : HaltsWithin code input 212 := stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 212
  polynomial := PolynomiallyBounded.const 212
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

theorem code_length : code.length ≤ 8255 := by
  have h := NativeRecoverableCouplingExecution.code_length
  rw [code, NativeUniformSequence.code_length, cleanup_length]
  omega

end Machine.NativeCleanRecoverableCoupling
