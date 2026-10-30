import Foundation.Crypto.Semantics.Machine.NativeFairRecoveryRequest
import Foundation.Crypto.Semantics.Machine.NativeAdaptedRecoverableCoupling

/-! The new forward and reverse samplers run on one continuing machine.
Both sample histories are erased; the intermediate request is prepared by
real instructions. Control normalization below is used only to prove laws;
the final theorem uses the actual terminal control of the combined code. -/
namespace Machine.NativeContinuingFairRecovery
open Foundation.Probability NativeUniformSequence
open NativeAdaptedRecoverableCoupling (atControl atControl_equivalent)
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
set_option Elab.async false
noncomputable section

noncomputable def reverseCode : Program := NativeFairRecoveryRequest.code.followedBy (NativeCleanFairRecovery.code true)
noncomputable def code : Program := (NativeCleanFairRecovery.code false).followedBy reverseCode


theorem reverse_stops : StopsEverywhere reverseCode 355 :=
  NativeUniformSequence.stops _ _ 47 307 NativeFairRecoveryRequest.stops (NativeCleanFairRecovery.stops true)

theorem stops : StopsEverywhere code 663 :=
  NativeUniformSequence.stops _ _ 307 355 (NativeCleanFairRecovery.stops false) reverse_stops

theorem prepared_run (pc oldPc : Nat) (key : Fin 5) (ciphertext : Bool) (before beforeOut : List (Option Bool)) :
    (evalConfigWithin (NativeCleanFairRecovery.code true)
      ((NativeFairRecoveryRequest.prepared oldPc (NativeEightBitCipher.encodeKey key) ciphertext before beforeOut).resumeAt 0) 307).map
        (atControl pc) = (FairRecovery.reverse key).map (fun result => NativePreparedState.state
          (NativeCleanFairRecovery.finish pc result ciphertext {left := List.replicate 19 none ++ before} {left := none :: beforeOut})) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
    (NativeFairRecoveryRequest.prepared_equivalent oldPc key ciphertext before beforeOut) 307 _ (atControl_equivalent pc),
    NativeCleanFairRecovery.full_run,PMF.map_comp]
  rfl

theorem reverse_run (pc oldPc : Nat) (key : Fin 5) (ciphertext : Bool) (before beforeOut : List (Option Bool)) :
    (evalConfigWithin reverseCode
      ((NativeCleanFairRecovery.finish oldPc key ciphertext {left := before} {left := beforeOut}).resumeAt 0) 355).map (atControl pc) =
      (FairRecovery.reverse key).map (fun result => NativePreparedState.state
        (NativeCleanFairRecovery.finish pc result ciphertext {left := List.replicate 19 none ++ before} {left := none :: beforeOut})) := by
  unfold reverseCode
  change (evalConfigWithin (NativeFairRecoveryRequest.code.followedBy (NativeCleanFairRecovery.code true))
    (NativeBitChoice.start (NativeCleanFairRecovery.finish oldPc key ciphertext {left := before} {left := beforeOut}).inputTape
      (NativeCleanFairRecovery.finish oldPc key ciphertext {left := before} {left := beforeOut}).outputTape) (47 + 307 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 47 307 NativeFairRecoveryRequest.stops (NativeCleanFairRecovery.stops true)]
  change ((evalConfigWithin NativeFairRecoveryRequest.code
    ((NativeCleanFairRecovery.finish oldPc key ciphertext {left := before} {left := beforeOut}).resumeAt 0) 47).bind _).map _ = _
  rw [NativeFairRecoveryRequest.run,PMF.pure_bind,PMF.map_comp]
  exact prepared_run pc _ key ciphertext before beforeOut

theorem run_at (pc : Nat) (key : Fin 5) (ciphertext : Bool) (before beforeOut : List (Option Bool)) :
    (evalConfigWithin code (NativeFairRecoverySampler.entry key ciphertext {left := before} {left := beforeOut}) 663).map (atControl pc) =
      ((FairRecovery.forward key).bind FairRecovery.reverse).map (fun result => NativePreparedState.state
        (NativeCleanFairRecovery.finish pc result ciphertext {left := List.replicate 19 none ++ before} {left := none :: beforeOut})) := by
  unfold code NativeFairRecoverySampler.entry
  rw [show 663 = 307 + 355 + 1 from rfl,
    NativeUniformSequence.run _ _ 307 355 (NativeCleanFairRecovery.stops false) reverse_stops]
  change ((evalConfigWithin (NativeCleanFairRecovery.code false)
    (NativeFairRecoverySampler.entry key ciphertext {left := before} {left := beforeOut}) 307).bind _).map _ = _
  rw [NativeCleanFairRecovery.full_run,PMF.bind_map,PMF.map_bind]
  simp only [Function.comp_def,PMF.map_comp]
  change (FairRecovery.forward key).bind (fun intermediate =>
    (evalConfigWithin reverseCode
      ((NativeCleanFairRecovery.finish _ intermediate ciphertext {left := before} {left := beforeOut}).resumeAt 0) 355).map (atControl pc)) = _
  simp only [reverse_run]
  rw [PMF.map_bind]

theorem sequence_normalized (first second : Program) (n m : Nat)
    (hf : StopsEverywhere first n) (hs : StopsEverywhere second m) (input output : Tape) :
    (evalConfigWithin (first.followedBy second) (NativeBitChoice.start input output) (n + m + 1)).map NativePreparedState.state =
      (evalConfigWithin (first.followedBy second) (NativeBitChoice.start input output) (n + m + 1)).map
        (atControl (first.length + second.length + 2)) := by
  rw [NativeUniformSequence.run first second n m hf hs]
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def,atControl]

theorem full_state_run (key : Fin 5) (ciphertext : Bool) (before beforeOut : List (Option Bool)) :
    (evalConfigWithin code (NativeFairRecoverySampler.entry key ciphertext {left := before} {left := beforeOut}) 663).map
      NativePreparedState.state = ((FairRecovery.forward key).bind FairRecovery.reverse).map (fun result => NativePreparedState.state
        (NativeCleanFairRecovery.finish ((NativeCleanFairRecovery.code false).length + reverseCode.length + 2) result ciphertext {left := List.replicate 19 none ++ before} {left := none :: beforeOut})) := by
  have fixed := sequence_normalized (NativeCleanFairRecovery.code false) reverseCode 307 355
    (NativeCleanFairRecovery.stops false) reverse_stops
    (NativeFairRecoverySampler.entry key ciphertext {left := before} {left := beforeOut}).inputTape
    (NativeFairRecoverySampler.entry key ciphertext {left := before} {left := beforeOut}).outputTape
  have entryEta : NativeBitChoice.start
      (NativeFairRecoverySampler.entry key ciphertext {left := before} {left := beforeOut}).inputTape
      (NativeFairRecoverySampler.entry key ciphertext {left := before} {left := beforeOut}).outputTape =
      NativeFairRecoverySampler.entry key ciphertext {left := before} {left := beforeOut} := rfl
  rw [entryEta] at fixed
  have run := run_at ((NativeCleanFairRecovery.code false).length + reverseCode.length + 2)
    key ciphertext before beforeOut
  simp only [code] at run
  simp only [code]
  exact fixed.trans run

theorem initial_state_law (key : Fin 5) (ciphertext : Bool) :
    (evalConfigWithin code (Configuration.initial (NativeFairRecoverySampler.rawInput key ciphertext)) 663).map NativePreparedState.state =
      ((FairRecovery.forward key).bind FairRecovery.reverse).map (fun result => NativePreparedState.state
        (NativeCleanFairRecovery.finish ((NativeCleanFairRecovery.code false).length + reverseCode.length + 2) result ciphertext {left := List.replicate 19 none} {left := [none]})) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativeFairRecoverySampler.entry_equivalent key ciphertext).symm
    663 _ NativePreparedState.state_equivalent]
  exact full_state_run key ciphertext [] []

theorem code_length : code.length ≤ 1971259 := by
  have f := NativeCleanFairRecovery.code_length false
  have r := NativeCleanFairRecovery.code_length true
  have a := NativeFairRecoveryRequest.code_length
  have inner : reverseCode.length = NativeFairRecoveryRequest.code.length + (NativeCleanFairRecovery.code true).length + 3 := by
    change (NativeFairRecoveryRequest.code.followedBy (NativeCleanFairRecovery.code true)).length = _
    exact NativeUniformSequence.code_length _ _
  have outer : code.length = (NativeCleanFairRecovery.code false).length + reverseCode.length + 3 := by
    change ((NativeCleanFairRecovery.code false).followedBy reverseCode).length = _
    exact NativeUniformSequence.code_length _ _
  calc
    code.length = (NativeCleanFairRecovery.code false).length + reverseCode.length + 3 := outer
    _ = (NativeCleanFairRecovery.code false).length +
        (NativeFairRecoveryRequest.code.length + (NativeCleanFairRecovery.code true).length + 3) + 3 :=
      congrArg (fun n => (NativeCleanFairRecovery.code false).length + n + 3) inner
    _ ≤ 1971259 := by omega

theorem haltsWithin (input : List Bool) : HaltsWithin code input 663 := stops (Tape.ofBits input) {}

noncomputable def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 663
  polynomial := PolynomiallyBounded.const 663
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code :=
  ⟨fun _ => 663,PolynomiallyBounded.const _,haltsWithin⟩


end
end Machine.NativeContinuingFairRecovery
