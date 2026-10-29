import Foundation.Crypto.Semantics.Machine.NativeKeyPairDecisionExecution

/-! The charged decision program also has the standard physical output packet:
the complemented ciphertext followed by the decision bit. -/
namespace Machine.NativeKeyPairOutputPacket
open Foundation.Probability NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

attribute [local irreducible] NativeControlledEightBitCipher.code

theorem caller_packet (result : Fin 5 × Bool) :
    (evalConfigWithin NativeKeyPairDecisionExecution.caller
      ((NativeCleanEightBitCipher.finish 0 result {} {}).resumeAt 0) 30).map Configuration.outputBits =
      PMF.pure [!result.2, keyPairTest result] := by
  unfold NativeKeyPairDecisionExecution.caller
  change (evalConfigWithin (NativeCiphertextToggle.code.followedBy NativeKeyPairObserver.code)
    (NativeBitChoice.start
      (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1)
        {left := List.replicate 27 none})
      {left := some result.2 :: []}) (6 + 23 + 1)).map _ = _
  rw [NativeUniformSequence.run _ _ 6 23 NativeCiphertextToggle.stops NativeKeyPairObserver.stops,
    NativeCiphertextToggle.run _ {} result.2, PMF.pure_bind]
  change ((evalConfigWithin NativeKeyPairObserver.code
    (NativeBitChoice.start
      (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1)
        {left := List.replicate 27 none})
      {left := some (!result.2) :: []}) 23).map _).map _ = _
  rw [NativeKeyPairObserver.run, PMF.pure_map, PMF.pure_map,
    NativeKeyPairObserver.accepts_encoded result.1 result.2]
  rfl

theorem kernel_packet (result : Fin 5 × Bool) :
    (NativeCleanCipherContinuation.kernel NativeKeyPairDecisionExecution.caller 30 {} {} result).map
      Configuration.outputBits = PMF.pure [!result.2, keyPairTest result] := by
  unfold NativeCleanCipherContinuation.kernel
  rw [PMF.map_comp]
  change (evalConfigWithin NativeKeyPairDecisionExecution.caller
    ((NativeCleanEightBitCipher.finish 0 result {} {}).resumeAt 0) 30).map Configuration.outputBits = _
  exact caller_packet result

theorem framed_packet (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativeKeyPairDecisionExecution.code
      (NativeControlledEightBitCipher.entry v message {} {}) 442).map Configuration.outputBits =
      (tableEightBitLaw v message).map (fun result => [!result.2, keyPairTest result]) := by
  unfold NativeKeyPairDecisionExecution.code
  rw [NativeCleanCipherContinuation.run _ 30 NativeKeyPairDecisionExecution.caller_stops, PMF.map_bind]
  simp only [kernel_packet]
  rfl

theorem evalWithin_of_halts (p : Program) (input : List Bool) (T : ℕ)
    (h : HaltsWithin p input T) :
    evalWithin p input T =
      (evalConfigWithin p (Configuration.initial input) T).map (fun c => some c.outputBits) := by
  change ((evalConfigWithin p (Configuration.initial input) T).bind
    (fun c => PMF.pure (if c.halted then some c.outputBits else none))) = _
  apply bind_congr_of_support
  intro c hc
  have hhalt := h c ((mem_support_evalConfigWithin_iff p _ c T).mp hc)
  simp [hhalt]

end Machine.NativeKeyPairOutputPacket
