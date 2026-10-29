import Foundation.Crypto.Semantics.Machine.NativePreparedInternalResult

/-! The full cell state of the prepared native execution. Quotienting removes
only redundant finite blank padding, as in the existing operational relation.
The program counter, halt flag and every cell relative to both heads remain.
This is a semantic representation, not a machine normalization operation. -/
namespace Machine.NativePreparedState
open Foundation.Probability NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
attribute [local irreducible] NativeControlledEightBitCipher.code

abbrev Result := Fin 5 × Bool

def cellSetoid : Setoid Configuration where
  r := Configuration.Equivalent
  iseqv := ⟨Configuration.Equivalent.refl, fun h => h.symm, fun h k =>
    ⟨h.1.trans k.1, h.2.1.trans k.2.1, h.2.2.1.trans k.2.2.1, h.2.2.2.trans k.2.2.2⟩⟩

abbrev State := Quotient cellSetoid

def state (c : Configuration) : State := Quotient.mk cellSetoid c

theorem state_equivalent (c d : Configuration) (h : c.Equivalent d) : state c = state d :=
  Quotient.sound h

theorem state_eq_iff (c d : Configuration) : state c = state d ↔ c.Equivalent d :=
  ⟨fun h => Quotient.exact h, fun h => state_equivalent c d h⟩

def observe : State → Option Result :=
  Quotient.lift NativePreparedInternalResult.observe NativePreparedInternalResult.observe_equivalent

def finish (pc : ℕ) (result : Result) : Configuration :=
  {pc := pc, inputTape := (NativeCleanEightBitCipher.finish 0 result {} {}).inputTape,
   outputTape := {left := [some (keyPairTest result), some (!result.2)]}, halted := true}

theorem finish_with_control (oldPc newPc : ℕ) (result : Result) :
    ({finish oldPc result with pc := newPc, halted := true} : Configuration) = finish newPc result := rfl

noncomputable def encode (result : Result) : State := state (finish (NativePreparedKeyDecision.preparation.length + NativePreparedKeyDecision.source.length + 2) result)

theorem observe_finish (pc : ℕ) (result : Result) :
    NativePreparedInternalResult.observe (finish pc result) = some result := by
  change (NativeEightBitCipher.observe (NativeCleanEightBitCipher.finish pc (result.1, !result.2) {} {})).map
    NativePreparedInternalResult.undoToggle = _
  rw [NativeCleanEightBitCipher.observe_finish]
  simp [NativePreparedInternalResult.undoToggle]

theorem observe_encode (result : Result) : observe (encode result) = some result := observe_finish (NativePreparedKeyDecision.preparation.length + NativePreparedKeyDecision.source.length + 2) result

def decode (s : State) : Result := (observe s).getD (0,false)

theorem decode_encode (result : Result) : decode (encode result) = result := by
  simp only [decode, observe_encode, Option.getD_some]

theorem encode_injective : Function.Injective encode := Function.LeftInverse.injective decode_encode

theorem caller_run (result : Result) :
    evalConfigWithin NativeKeyPairDecisionExecution.caller
      ((NativeCleanEightBitCipher.finish 0 result {} {}).resumeAt 0) 30 =
      PMF.pure (finish (NativeCiphertextToggle.code.length + NativeKeyPairObserver.code.length + 2) result) := by
  unfold NativeKeyPairDecisionExecution.caller
  change evalConfigWithin (NativeCiphertextToggle.code.followedBy NativeKeyPairObserver.code)
    (NativeBitChoice.start
      (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 27 none})
      {left := some result.2 :: []}) (6 + 23 + 1) = _
  rw [NativeUniformSequence.run _ _ 6 23 NativeCiphertextToggle.stops NativeKeyPairObserver.stops,
    NativeCiphertextToggle.run _ {} result.2, PMF.pure_bind]
  change (evalConfigWithin NativeKeyPairObserver.code
    (NativeBitChoice.start
      (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 27 none})
      {left := some (!result.2) :: []}) 23).map _ = _
  rw [NativeKeyPairObserver.run, PMF.pure_map,
    NativeKeyPairObserver.accepts_encoded result.1 result.2]
  rfl

theorem pure_finish_state (oldPc newPc : ℕ) (result : Result) :
    (PMF.pure (finish oldPc result)).map (fun c => state {c with pc := newPc, halted := true}) =
      PMF.pure (state (finish newPc result)) := by
  rw [PMF.pure_map]
  rfl

theorem kernel_state (pc : ℕ) (result : Result) :
    (NativeCleanCipherContinuation.kernel NativeKeyPairDecisionExecution.caller 30 {} {} result).map
      (fun c => state {c with pc := pc, halted := true}) = PMF.pure (state (finish pc result)) := by
  unfold NativeCleanCipherContinuation.kernel
  rw [PMF.map_comp]
  change (evalConfigWithin NativeKeyPairDecisionExecution.caller
    ((NativeCleanEightBitCipher.finish 0 result {} {}).resumeAt 0) 30).map
      (fun c => state {c with pc := pc, halted := true}) = _
  exact (congrArg (fun law : PMF Configuration => law.map (fun c => state {c with pc := pc, halted := true}))
    (caller_run result)).trans (pure_finish_state _ pc result)

theorem source_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativePreparedKeyDecision.source
      ((NativePreparedKeyDecision.prepared v message).resumeAt 0) 442).map
        (fun c => state {c with pc := (NativePreparedKeyDecision.preparation.length + NativePreparedKeyDecision.source.length + 2), halted := true}) =
      (tableEightBitLaw v message).map encode := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativePreparedKeyDecision.handoff v message) 442 _ (by
    intro c d h
    exact state_equivalent _ _ ⟨rfl, rfl, h.2.2⟩)]
  change (evalConfigWithin (NativeCleanCipherContinuation.code NativeKeyPairDecisionExecution.caller)
    (NativeControlledEightBitCipher.entry v message {} {}) 442).map
      (fun c => state {c with pc := (NativePreparedKeyDecision.preparation.length + NativePreparedKeyDecision.source.length + 2), halted := true}) = _
  rw [NativeCleanCipherContinuation.run NativeKeyPairDecisionExecution.caller 30
    NativeKeyPairDecisionExecution.caller_stops, PMF.map_bind]
  simp only [kernel_state]
  rfl

theorem framed_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativePreparedKeyDecision.code (NativePreparedKeyDecision.entry v message) 930).map state =
      (tableEightBitLaw v message).map encode := by
  unfold NativePreparedKeyDecision.code NativePreparedKeyDecision.entry
  rw [show 930 = 487 + 442 + 1 from rfl,
    NativeUniformSequence.run _ _ _ _ NativePreparedKeyDecision.preparation_stops NativePreparedKeyDecision.source_stops]
  change ((evalConfigWithin NativePreparedKeyDecision.preparation (NativePreparedKeyDecision.entry v message) 487).bind _).map state = _
  rw [NativePreparedKeyDecision.preparation_run, PMF.pure_bind, PMF.map_comp]
  exact source_law v message

theorem initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin NativePreparedKeyDecision.code
      (Configuration.initial (NativePreparedKeyDecision.rawInput v message)) 930).map state =
      (tableEightBitLaw v message).map encode := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (NativePreparedKeyDecision.entry_equivalent v message).symm
    930 _ state_equivalent]
  exact framed_law v message

end Machine.NativePreparedState
