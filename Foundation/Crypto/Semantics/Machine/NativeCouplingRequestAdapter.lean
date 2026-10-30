import Foundation.Crypto.Semantics.Machine.NativeCleanRecoverableCoupling

/-! A real native adapter reads the retained key and ciphertext of the
reference exit. It erases the old three key cells and both output cells,
writes the two-bit conditional request, and rewinds to that request.
No host-side decoding operation is used as a machine instruction. -/
namespace Machine.NativeCouplingRequestAdapter
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def leaf (bit : Bool) : Program :=
  [.moveLeft .input, .erase .input, .moveLeft .input, .erase .input,
   .moveLeft .input, .erase .input, .moveRight .input, .moveRight .input, .moveRight .input,
   .moveLeft .output, .erase .output, .moveLeft .output,
   .write .input bit, .moveRight .input,
   .branch .output 15 15 17,
   .write .input true, .jump 18, .write .input false,
   .moveRight .input, .moveLeft .input, .moveLeft .input,
   .erase .output, .moveRight .output, .moveRight .output, .halt]

def prepared (pc : ℕ) (bit ciphertext : Bool) : Configuration :=
  {pc := pc,
   inputTape := preload (NativeRecoverableKeySampler.rawInput bit ciphertext) {left := List.replicate 30 none},
   outputTape := {left := [none,none]}, halted := true}

theorem leaf_run (bit ciphertext decision : Bool) (key : Fin 3 → Bool) :
    evalConfigWithin (leaf bit)
      (NativeBitChoice.start
        (NativeKeyPairObserver.keyed key {left := List.replicate 27 none})
        {left := [some decision,some (!ciphertext)]}) 25 =
      PMF.pure (prepared 24 bit ciphertext) := by
  cases ciphertext <;>
    simp [leaf, prepared, NativeRecoverableKeySampler.rawInput, NativeRecoverableKeySampler.request,
      NativeKeyPairObserver.keyed, preload, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
      Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.moveLeft, Tape.moveRight, Tape.write, List.replicate_succ]

theorem leaf_stops (bit : Bool) : StopsEverywhere (leaf bit) 25 := by
  intro input output finish trace
  have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  cases h : output.left with
  | nil =>
    simp [leaf, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
      Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.moveLeft, Tape.moveRight, Tape.write, h] at member
    subst finish
    rfl
  | cons a rest =>
    cases hr : rest with
    | nil =>
      simp [leaf, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
        Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
        Tape.moveLeft, Tape.moveRight, Tape.write, h, hr] at member
      subst finish
      rfl
    | cons b tail =>
      cases b with
      | none =>
        simp [leaf, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
          Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
          Tape.moveLeft, Tape.moveRight, Tape.write, h, hr] at member
        subst finish
        rfl
      | some value =>
        cases value <;>
          simp [leaf, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
            Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
            Tape.moveLeft, Tape.moveRight, Tape.write, h, hr] at member <;>
          subst finish <;> rfl

def decoder : Program := compile 3 (fun bits => leaf (NativeRecoverableKeyObserver.accepts bits))
def code : Program := NativeKeyPairObserver.rewind.followedBy decoder

theorem decoder_stops : StopsEverywhere decoder 34 :=
  NativeBitDecoderTotal.compile_stops_everywhere 3 _ 25 (fun _bits => leaf_stops _)

theorem stops : StopsEverywhere code 45 :=
  NativeUniformSequence.stops NativeKeyPairObserver.rewind decoder 10 34
    NativeKeyPairObserver.rewind_stops decoder_stops

theorem run (pc : ℕ) (result : Fin 5 × Bool) :
    evalConfigWithin code ((NativePreparedState.finish pc result).resumeAt 0) 45 =
      PMF.pure (prepared (NativeKeyPairObserver.rewind.length + decoder.length + 2)
        (Recoverable.parent result.1) result.2) := by
  unfold code
  change evalConfigWithin (NativeKeyPairObserver.rewind.followedBy decoder)
    (NativeBitChoice.start
      (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 27 none})
      {left := [some (keyPairTest result),some (!result.2)]}) 45 = _
  rw [NativeUniformSequence.run _ _ 10 34 NativeKeyPairObserver.rewind_stops decoder_stops]
  have hr := NativePrivateHistoryErasure.run [.left,.left,.left]
    (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 27 none})
    {left := [some (keyPairTest result),some (!result.2)]}
  rw [NativeKeyPairObserver.rewind_tape] at hr
  change evalConfigWithin NativeKeyPairObserver.rewind
    (NativeBitChoice.start
      (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 27 none})
      {left := [some (keyPairTest result),some (!result.2)]}) 10 = _ at hr
  rw [hr, PMF.pure_bind]
  change (evalConfigWithin (compile 3 (fun bits => leaf (NativeRecoverableKeyObserver.accepts bits)))
    (NativeBitChoice.start
      (preload (List.ofFn (NativeEightBitCipher.encodeKey result.1)) {left := List.replicate 27 none})
      {left := [some (keyPairTest result),some (!result.2)]}) 34).map _ = _
  rw [compile_run 3 _ 25 (fun bits input output => leaf_stops _ input output),
    NativeKeyPairObserver.after_read_key, leaf_run, PMF.pure_map, PMF.pure_map,
    NativeRecoverableKeyObserver.accepts_encoded]
  rfl

theorem code_length : code.length ≤ 261 := by
  have hd := compile_length_bound 3 (fun bits => leaf (NativeRecoverableKeyObserver.accepts bits))
    25 (fun bits => by rfl)
  change decoder.length + 6 ≤ (25 + 6) * 2 ^ 3 at hd
  have hr : NativeKeyPairObserver.rewind.length = 16 :=
    NativePrivateHistoryErasure.code_length [.left,.left,.left]
  rw [code, NativeUniformSequence.code_length, hr]
  omega

end Machine.NativeCouplingRequestAdapter
