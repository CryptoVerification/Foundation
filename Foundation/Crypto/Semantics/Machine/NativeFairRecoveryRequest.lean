import Foundation.Crypto.Semantics.Machine.NativeCleanFairRecovery
import Foundation.Crypto.Semantics.Machine.NativeKeyPairObserver

/-! A charged adapter between clean fair sampler exits and the next request.
The current/right tape cells are blank at this boundary. Older left frames
are retained. The old key and ciphertext are physically cleared and rewritten. -/
namespace Machine.NativeFairRecoveryRequest
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence

def leaf (key : Fin 3 → Bool) : Program :=
  [.moveLeft .input,.erase .input,.moveLeft .input,.erase .input,.moveLeft .input,.erase .input,
   .moveRight .input,.moveRight .input,.moveRight .input,.moveLeft .output,
   .write .input (key 0),.moveRight .input,.write .input (key 1),.moveRight .input,
   .write .input (key 2),.moveRight .input,.branch .output 17 17 19,
   .write .input false,.jump 20,.write .input true,.moveRight .input,
   .moveLeft .input,.moveLeft .input,.moveLeft .input,.moveLeft .input,
   .erase .output,.moveRight .output,.halt]

def word (key : Fin 3 → Bool) (ciphertext : Bool) : List Bool := [key 0,key 1,key 2,ciphertext]

def prepared (pc : Nat) (key : Fin 3 → Bool) (ciphertext : Bool)
    (before beforeOut : List (Option Bool)) : Configuration :=
  {pc := pc,inputTape := preload (word key ciphertext) {left := List.replicate 19 none ++ before},
   outputTape := {left := none :: beforeOut},halted := true}

theorem leaf_run (key : Fin 3 → Bool) (ciphertext : Bool) (before beforeOut : List (Option Bool)) :
    evalConfigWithin (leaf key)
      (NativeBitChoice.start (NativeKeyPairObserver.keyed key {left := List.replicate 16 none ++ before})
        {left := some ciphertext :: beforeOut}) 27 = PMF.pure (prepared 27 key ciphertext before beforeOut) := by
  cases ciphertext <;>
    simp [leaf,prepared,word,NativeKeyPairObserver.keyed,preload,evalConfigWithin,stepPMF,next,
      NativeBitChoice.start,Instruction.next,Configuration.tape,Configuration.updateTape,Configuration.advance,
      Tape.moveLeft,Tape.moveRight,Tape.write,List.replicate_succ]

theorem leaf_stops (key : Fin 3 → Bool) : StopsEverywhere (leaf key) 27 := by
  intro input output finish trace
  have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  cases h : output.left with
  | nil =>
    simp [leaf,evalConfigWithin,stepPMF,next,NativeBitChoice.start,Instruction.next,
      Configuration.tape,Configuration.updateTape,Configuration.advance,Tape.moveLeft,Tape.moveRight,Tape.write,h] at member
    subst finish
    rfl
  | cons value rest =>
    cases value with
    | none =>
      simp [leaf,evalConfigWithin,stepPMF,next,NativeBitChoice.start,Instruction.next,
        Configuration.tape,Configuration.updateTape,Configuration.advance,Tape.moveLeft,Tape.moveRight,Tape.write,h] at member
      subst finish
      rfl
    | some bit =>
      cases bit <;>
        simp [leaf,evalConfigWithin,stepPMF,next,NativeBitChoice.start,Instruction.next,
          Configuration.tape,Configuration.updateTape,Configuration.advance,Tape.moveLeft,Tape.moveRight,Tape.write,h] at member <;>
          subst finish <;> rfl

def decoder : Program := compile 3 leaf
def code : Program := NativeKeyPairObserver.rewind.followedBy decoder

theorem decoder_stops : StopsEverywhere decoder 36 :=
  NativeBitDecoderTotal.compile_stops_everywhere 3 leaf 27 leaf_stops

theorem stops : StopsEverywhere code 47 :=
  NativeUniformSequence.stops _ _ 10 36 NativeKeyPairObserver.rewind_stops decoder_stops

theorem run (pc : Nat) (key : Fin 5) (ciphertext : Bool) (before beforeOut : List (Option Bool)) :
    evalConfigWithin code ((NativeCleanFairRecovery.finish pc key ciphertext {left := before} {left := beforeOut}).resumeAt 0) 47 =
      PMF.pure (prepared (NativeKeyPairObserver.rewind.length + decoder.length + 2)
        (NativeEightBitCipher.encodeKey key) ciphertext before beforeOut) := by
  unfold code
  change evalConfigWithin (NativeKeyPairObserver.rewind.followedBy decoder)
    (NativeBitChoice.start (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey key) {left := List.replicate 16 none ++ before})
      {left := some ciphertext :: beforeOut}) 47 = _
  rw [NativeUniformSequence.run _ _ 10 36 NativeKeyPairObserver.rewind_stops decoder_stops]
  have hr := NativePrivateHistoryErasure.run [.left,.left,.left]
    (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey key) {left := List.replicate 16 none ++ before})
    {left := some ciphertext :: beforeOut}
  rw [NativeKeyPairObserver.rewind_tape] at hr
  change evalConfigWithin NativeKeyPairObserver.rewind
    (NativeBitChoice.start (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey key) {left := List.replicate 16 none ++ before})
      {left := some ciphertext :: beforeOut}) 10 = _ at hr
  rw [hr,PMF.pure_bind]
  change (evalConfigWithin (compile 3 leaf)
    (NativeBitChoice.start (preload (List.ofFn (NativeEightBitCipher.encodeKey key)) {left := List.replicate 16 none ++ before})
      {left := some ciphertext :: beforeOut}) 36).map _ = _
  rw [compile_run 3 leaf 27 (fun bits input output => leaf_stops bits input output),
    NativeKeyPairObserver.after_read_key,leaf_run,PMF.pure_map,PMF.pure_map]
  rfl

theorem prepared_equivalent (pc : Nat) (key : Fin 5) (ciphertext : Bool) (before beforeOut : List (Option Bool)) :
    (prepared pc (NativeEightBitCipher.encodeKey key) ciphertext before beforeOut).resumeAt 0 |>.Equivalent
      (NativeFairRecoverySampler.entry key ciphertext {left := List.replicate 19 none ++ before} {left := none :: beforeOut}) := by
  refine ⟨rfl,rfl,?_,?_⟩
  · have blank := Tape.blank_padding_equivalent (List.replicate 19 none ++ before) 15
    have h := NativeControlledCipherInitial.preload_equivalent (NativeFairRecoverySampler.rawInput key ciphertext) blank
    exact h.symm
  · exact (Tape.blank_padding_equivalent (none :: beforeOut) 1).symm

theorem code_length : code.length ≤ 285 := by
  have h := compile_length_bound 3 leaf 28 (fun bits => by rfl)
  change decoder.length + 6 ≤ 8 * (28 + 6) at h
  rw [code,NativeUniformSequence.code_length]
  have small : NativeKeyPairObserver.rewind.length = 16 := by
    change (NativePrivateHistoryErasure.code [.left,.left,.left]).length = _
    rw [NativePrivateHistoryErasure.code_length]
    rfl
  rw [small]
  omega

theorem haltsWithin (input : List Bool) : HaltsWithin code input 47 := stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 47
  polynomial := PolynomiallyBounded.const 47
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

end Machine.NativeFairRecoveryRequest
