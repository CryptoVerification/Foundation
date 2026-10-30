import Foundation.Crypto.Semantics.Machine.NativeCleanFiveStateSampler
import Foundation.Crypto.Semantics.Machine.NativeContinuingFairRecovery

/-! A uniform two-stage native execution for arbitrary five-state twelve-bit
samplers. The intermediate request adapter is charged and both histories are
erased. The final law uses the actual control position of the composed code. -/
namespace Machine.NativeContinuingFiveStateSampler
open Foundation.Probability NativeUniformSequence
open NativeAdaptedRecoverableCoupling (atControl atControl_equivalent)
open NativeFiveStateSampler (Sampler kernel)
set_option Elab.async false
noncomputable section

def nextCode (second : Sampler) : Program :=
  NativeFairRecoveryRequest.code.followedBy (NativeCleanFiveStateSampler.code second)

def code (first second : Sampler) : Program :=
  (NativeCleanFiveStateSampler.code first).followedBy (nextCode second)

theorem next_stops (second : Sampler) : StopsEverywhere (nextCode second) 355 :=
  NativeUniformSequence.stops _ _ 47 307 NativeFairRecoveryRequest.stops (NativeCleanFiveStateSampler.stops second)

theorem stops (first second : Sampler) : StopsEverywhere (code first second) 663 :=
  NativeUniformSequence.stops _ _ 307 355 (NativeCleanFiveStateSampler.stops first) (next_stops second)

theorem prepared_run (second : Sampler) (pc oldPc : Nat) (key : Fin 5) (ciphertext : Bool)
    (before beforeOut : List (Option Bool)) :
    (evalConfigWithin (NativeCleanFiveStateSampler.code second)
      ((NativeFairRecoveryRequest.prepared oldPc (NativeEightBitCipher.encodeKey key) ciphertext before beforeOut).resumeAt 0) 307).map
        (atControl pc) = (kernel second key).map (fun result => NativePreparedState.state
          (NativeCleanFiveStateSampler.finish pc result ciphertext {left := List.replicate 19 none ++ before} {left := none :: beforeOut})) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativeFairRecoveryRequest.prepared_equivalent oldPc key ciphertext before beforeOut) 307 _ (atControl_equivalent pc)]
  change (evalConfigWithin (NativeCleanFiveStateSampler.code second)
    (NativeFiveStateSampler.entry key ciphertext {left := List.replicate 19 none ++ before} {left := none :: beforeOut}) 307).map
      (atControl pc) = _
  rw [NativeCleanFiveStateSampler.full_run,PMF.map_comp]
  rfl

theorem next_run (second : Sampler) (pc oldPc : Nat) (key : Fin 5) (ciphertext : Bool)
    (before beforeOut : List (Option Bool)) :
    (evalConfigWithin (nextCode second)
      ((NativeCleanFiveStateSampler.finish oldPc key ciphertext {left := before} {left := beforeOut}).resumeAt 0) 355).map (atControl pc) =
      (kernel second key).map (fun result => NativePreparedState.state
        (NativeCleanFiveStateSampler.finish pc result ciphertext {left := List.replicate 19 none ++ before} {left := none :: beforeOut})) := by
  unfold nextCode
  change (evalConfigWithin (NativeFairRecoveryRequest.code.followedBy (NativeCleanFiveStateSampler.code second))
    (NativeBitChoice.start (NativeCleanFiveStateSampler.finish oldPc key ciphertext {left := before} {left := beforeOut}).inputTape
      (NativeCleanFiveStateSampler.finish oldPc key ciphertext {left := before} {left := beforeOut}).outputTape) (47 + 307 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 47 307 NativeFairRecoveryRequest.stops (NativeCleanFiveStateSampler.stops second)]
  change ((evalConfigWithin NativeFairRecoveryRequest.code
    ((NativeCleanFiveStateSampler.finish oldPc key ciphertext {left := before} {left := beforeOut}).resumeAt 0) 47).bind _).map _ = _
  rw [NativeFairRecoveryRequest.run,PMF.pure_bind,PMF.map_comp]
  exact prepared_run second pc _ key ciphertext before beforeOut

theorem run_at (first second : Sampler) (pc : Nat) (key : Fin 5) (ciphertext : Bool)
    (before beforeOut : List (Option Bool)) :
    (evalConfigWithin (code first second) (NativeFiveStateSampler.entry key ciphertext {left := before} {left := beforeOut}) 663).map (atControl pc) =
      ((kernel first key).bind (kernel second)).map (fun result => NativePreparedState.state
        (NativeCleanFiveStateSampler.finish pc result ciphertext {left := List.replicate 19 none ++ before} {left := none :: beforeOut})) := by
  unfold code NativeFiveStateSampler.entry
  rw [show 663 = 307 + 355 + 1 from rfl,
    NativeUniformSequence.run _ _ 307 355 (NativeCleanFiveStateSampler.stops first) (next_stops second)]
  change ((evalConfigWithin (NativeCleanFiveStateSampler.code first)
    (NativeFiveStateSampler.entry key ciphertext {left := before} {left := beforeOut}) 307).bind _).map _ = _
  rw [NativeCleanFiveStateSampler.full_run,PMF.bind_map,PMF.map_bind]
  simp only [Function.comp_def,PMF.map_comp]
  change (kernel first key).bind (fun intermediate =>
    (evalConfigWithin (nextCode second)
      ((NativeCleanFiveStateSampler.finish _ intermediate ciphertext {left := before} {left := beforeOut}).resumeAt 0) 355).map (atControl pc)) = _
  simp only [next_run]
  rw [PMF.map_bind]

theorem full_state_run (first second : Sampler) (key : Fin 5) (ciphertext : Bool)
    (before beforeOut : List (Option Bool)) :
    (evalConfigWithin (code first second) (NativeFiveStateSampler.entry key ciphertext {left := before} {left := beforeOut}) 663).map
      NativePreparedState.state = ((kernel first key).bind (kernel second)).map (fun result => NativePreparedState.state
        (NativeCleanFiveStateSampler.finish ((NativeCleanFiveStateSampler.code first).length + (nextCode second).length + 2)
          result ciphertext {left := List.replicate 19 none ++ before} {left := none :: beforeOut})) := by
  have fixed := NativeContinuingFairRecovery.sequence_normalized (NativeCleanFiveStateSampler.code first) (nextCode second) 307 355
    (NativeCleanFiveStateSampler.stops first) (next_stops second)
    (NativeFiveStateSampler.entry key ciphertext {left := before} {left := beforeOut}).inputTape
    (NativeFiveStateSampler.entry key ciphertext {left := before} {left := beforeOut}).outputTape
  have entryEta : NativeBitChoice.start
      (NativeFiveStateSampler.entry key ciphertext {left := before} {left := beforeOut}).inputTape
      (NativeFiveStateSampler.entry key ciphertext {left := before} {left := beforeOut}).outputTape =
      NativeFiveStateSampler.entry key ciphertext {left := before} {left := beforeOut} := rfl
  rw [entryEta] at fixed
  have run := run_at first second ((NativeCleanFiveStateSampler.code first).length + (nextCode second).length + 2)
    key ciphertext before beforeOut
  simp only [code] at run
  simp only [code]
  exact fixed.trans run

theorem initial_state_law (first second : Sampler) (key : Fin 5) (ciphertext : Bool) :
    (evalConfigWithin (code first second) (Configuration.initial (NativeFiveStateSampler.rawInput key ciphertext)) 663).map NativePreparedState.state =
      ((kernel first key).bind (kernel second)).map (fun result => NativePreparedState.state
        (NativeCleanFiveStateSampler.finish ((NativeCleanFiveStateSampler.code first).length + (nextCode second).length + 2)
          result ciphertext {left := List.replicate 19 none} {left := [none]})) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativeFiveStateSampler.entry_equivalent key ciphertext).symm
    663 _ NativePreparedState.state_equivalent]
  exact full_state_run first second key ciphertext [] []

theorem code_length (first second : Sampler) : (code first second).length ≤ 1971259 := by
  have f := NativeCleanFiveStateSampler.code_length first
  have r := NativeCleanFiveStateSampler.code_length second
  have a := NativeFairRecoveryRequest.code_length
  have inner : (nextCode second).length = NativeFairRecoveryRequest.code.length + (NativeCleanFiveStateSampler.code second).length + 3 := by
    exact NativeUniformSequence.code_length _ _
  have outer : (code first second).length = (NativeCleanFiveStateSampler.code first).length + (nextCode second).length + 3 := by
    exact NativeUniformSequence.code_length _ _
  calc
    (code first second).length = (NativeCleanFiveStateSampler.code first).length + (nextCode second).length + 3 := outer
    _ = (NativeCleanFiveStateSampler.code first).length +
        (NativeFairRecoveryRequest.code.length + (NativeCleanFiveStateSampler.code second).length + 3) + 3 :=
      congrArg (fun n => (NativeCleanFiveStateSampler.code first).length + n + 3) inner
    _ ≤ 1971259 := by omega

theorem haltsWithin (first second : Sampler) (input : List Bool) : HaltsWithin (code first second) input 663 :=
  stops first second (Tape.ofBits input) {}

def bounded (first second : Sampler) : CryptoLogic.BoundedProgram where
  program := code first second
  budget := fun _ => 663
  polynomial := PolynomiallyBounded.const 663
  halts := haltsWithin first second

theorem polynomial_time (first second : Sampler) : PolynomialTime (code first second) := (bounded first second).polynomialTime

end
end Machine.NativeContinuingFiveStateSampler
