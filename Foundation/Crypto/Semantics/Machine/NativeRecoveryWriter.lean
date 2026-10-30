import Foundation.Crypto.Semantics.Machine.NativeCanonicalCouplingExecution

/-! Deterministically reconstruct the source private label and reference
public packet from a two-bit request, then physically erase that request. -/
namespace Machine.NativeRecoveryWriter
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def sourceKey (bit : Bool) : Fin 5 := if bit then 2 else 0
def result (bit ciphertext : Bool) : Fin 5 × Bool := (sourceKey bit,ciphertext)

theorem source_test (bit ciphertext : Bool) : keyPairTest (result bit ciphertext) = true := by
  cases bit <;> rfl

def leaf (bit ciphertext : Bool) : Program :=
  [.write .input (NativeEightBitCipher.encodeKey (sourceKey bit) 0), .moveRight .input,
   .write .input (NativeEightBitCipher.encodeKey (sourceKey bit) 1), .moveRight .input,
   .write .input (NativeEightBitCipher.encodeKey (sourceKey bit) 2), .moveRight .input, .write .output (!ciphertext), .moveRight .output,
   .write .output true, .moveRight .output, .halt]

def leafFinish (bit ciphertext : Bool) (input output : Tape) : Configuration :=
  {pc := 10, inputTape := NativePrivateBitResult.writeKey (NativeEightBitCipher.encodeKey (sourceKey bit)) input,
   outputTape := (((output.write (some (!ciphertext))).moveRight).write (some true)).moveRight, halted := true}

theorem leaf_run (bit ciphertext : Bool) (input output : Tape) :
    evalConfigWithin (leaf bit ciphertext) (NativeBitChoice.start input output) 11 =
      PMF.pure (leafFinish bit ciphertext input output) := by
  simp [leaf, leafFinish, NativePrivateBitResult.writeKey, evalConfigWithin, stepPMF, next,
    NativeBitChoice.start, Instruction.next, Configuration.updateTape, Configuration.advance]

theorem leaf_stops (bit ciphertext : Bool) : StopsEverywhere (leaf bit ciphertext) 11 := by
  intro input output finish trace
  have h := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  rw [leaf_run, PMF.mem_support_pure_iff] at h
  subst finish
  rfl

def leaves (word : Fin 2 → Bool) : Program := leaf (word 0) (word 1)
def decoder : Program := compile 2 leaves
def cleanup : Program := NativePrivateHistoryErasure.code (NativePrivateHistoryErasure.protectedActions 3 2)
def code : Program := decoder.followedBy cleanup

def entry (bit ciphertext : Bool) : Configuration := NativeBitChoice.start
  (preload (NativeRecoverableKeySampler.rawInput bit ciphertext) (NativePrivateBitResult.keyBuffer {}))
  (NativeBitGenerator.blankBlock 2 {})

def beforeCleanup (bit ciphertext : Bool) : Configuration :=
  {pc := decoder.length - 1,
   inputTape := NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey (sourceKey bit))
     (afterRead (NativeRecoverableKeySampler.rawInput bit ciphertext) {}),
   outputTape := {left := [some true,some (!ciphertext)]}, halted := true}

theorem decoder_run (bit ciphertext : Bool) :
    evalConfigWithin decoder (entry bit ciphertext) 17 = PMF.pure (beforeCleanup bit ciphertext) := by
  unfold decoder entry NativeRecoverableKeySampler.rawInput
  rw [compile_run 2 leaves 11 (fun word input output => leaf_stops _ _ input output),
    show leaves (NativeRecoverableKeySampler.request bit ciphertext) = leaf bit ciphertext from rfl,
    leaf_run, PMF.pure_map]
  unfold leafFinish
  rw [NativePrivateBitResult.afterRead_keyBuffer, NativePrivateBitResult.writeKey_buffer]
  rfl

theorem decoder_stops : StopsEverywhere decoder 17 :=
  NativeBitDecoderTotal.compile_stops_everywhere 2 leaves 11 (fun _word => leaf_stops _ _)

theorem cleanup_stops : StopsEverywhere cleanup 37 := by
  have h := NativePrivateHistoryErasure.stops (NativePrivateHistoryErasure.protectedActions 3 2)
  rw [NativePrivateHistoryErasure.protected_length] at h
  exact h

def finish (pc : ℕ) (bit ciphertext : Bool) : Configuration :=
  {pc := pc, inputTape := NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey (sourceKey bit))
      {left := List.replicate 2 none},
   outputTape := {left := [some true,some (!ciphertext)]}, halted := true}

theorem cleanup_run (pc : ℕ) (bit ciphertext : Bool) :
    (evalConfigWithin cleanup ((beforeCleanup bit ciphertext).resumeAt 0) 37).map
      (fun c => {c with pc := pc, halted := true}) = PMF.pure (finish pc bit ciphertext) := by
  have h := NativePrivateHistoryErasure.protected_cells
    [some (NativeEightBitCipher.encodeKey (sourceKey bit) 2),
      some (NativeEightBitCipher.encodeKey (sourceKey bit) 1),some (NativeEightBitCipher.encodeKey (sourceKey bit) 0)]
    ((NativeRecoverableKeySampler.rawInput bit ciphertext).reverse.map some) [] none []
  have len : ((NativeRecoverableKeySampler.rawInput bit ciphertext).reverse.map some).length = 2 := by
    simp [NativeRecoverableKeySampler.rawInput]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, len] at h
  change (evalConfigWithin (NativePrivateHistoryErasure.code (NativePrivateHistoryErasure.protectedActions 3 2))
    (NativeBitChoice.start
      {left := [some (NativeEightBitCipher.encodeKey (sourceKey bit) 2),
      some (NativeEightBitCipher.encodeKey (sourceKey bit) 1),some (NativeEightBitCipher.encodeKey (sourceKey bit) 0)] ++
        (NativeRecoverableKeySampler.rawInput bit ciphertext).reverse.map some ++ []}
      {left := [some true,some (!ciphertext)]})
    (3 * (NativePrivateHistoryErasure.protectedActions 3 2).length + 1)).map _ = _
  rw [NativePrivateHistoryErasure.run, PMF.pure_map, h]
  simp only [finish]
  rfl

theorem run (bit ciphertext : Bool) : evalConfigWithin code (entry bit ciphertext) 55 =
    PMF.pure (finish (decoder.length + cleanup.length + 2) bit ciphertext) := by
  unfold code entry
  rw [show 55 = 17 + 37 + 1 from rfl,
    NativeUniformSequence.run _ _ 17 37 decoder_stops cleanup_stops]
  change (evalConfigWithin decoder (entry bit ciphertext) 17).bind _ = _
  rw [decoder_run, PMF.pure_bind]
  exact cleanup_run _ bit ciphertext

theorem entry_equivalent (bit ciphertext : Bool) : (entry bit ciphertext).Equivalent
    (Configuration.initial (NativeRecoverableKeySampler.rawInput bit ciphertext)) := by
  refine ⟨rfl,rfl,?_,Tape.blank_padding_equivalent [] 2⟩
  exact (NativeControlledCipherInitial.preload_equivalent _ (Tape.blank_padding_equivalent [] 3)).trans
    (NativeControlledCipherInitial.preload_empty _)

theorem finish_equivalent (pc : ℕ) (bit ciphertext : Bool) :
    (finish pc bit ciphertext).Equivalent (NativePreparedState.finish pc (result bit ciphertext)) := by
  have h := (NativeAdaptedRecoverableCoupling.blank_left 2).trans (NativeAdaptedRecoverableCoupling.blank_left 27).symm
  refine ⟨rfl,rfl,⟨rfl,?_,fun _ => rfl⟩,?_⟩
  · intro i
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
        cases i with
        | zero => rfl
        | succ i => exact h.2.1 i
  · simp only [NativePreparedState.finish, source_test]
    exact Tape.Equivalent.refl _

theorem stops : StopsEverywhere code 55 :=
  NativeUniformSequence.stops decoder cleanup 17 37 decoder_stops cleanup_stops

theorem code_length : code.length ≤ 126 := by
  have hd := compile_length_bound 2 leaves 11 (fun word => by rfl)
  change decoder.length + 6 ≤ (11 + 6) * 2 ^ 2 at hd
  have hc : cleanup.length = 61 := by
    rw [cleanup, NativePrivateHistoryErasure.code_length, NativePrivateHistoryErasure.protected_length]
  rw [code, NativeUniformSequence.code_length, hc]
  omega

end Machine.NativeRecoveryWriter
