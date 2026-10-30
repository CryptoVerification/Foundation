import Foundation.Crypto.Semantics.Machine.NativeFairRecoveryRequest
import Foundation.Crypto.Semantics.Machine.NativeKeyPairObserver

/-! Read the actual reference-cipher exit and prepare a fair recovery request.
The key and both old output cells are physically erased. Ciphertext toggling
is undone by native branching, without a host-side request conversion. -/
namespace Machine.NativeReferenceFairRequest
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence

def leaf (key : Fin 3 → Bool) : Program :=
  [.moveLeft .input,.erase .input,.moveLeft .input,.erase .input,.moveLeft .input,.erase .input,
   .moveRight .input,.moveRight .input,.moveRight .input,
   .moveLeft .output,.erase .output,.moveLeft .output,
   .write .input (key 0),.moveRight .input,.write .input (key 1),.moveRight .input,
   .write .input (key 2),.moveRight .input,.branch .output 19 19 21,
   .write .input true,.jump 22,.write .input false,.moveRight .input,
   .moveLeft .input,.moveLeft .input,.moveLeft .input,.moveLeft .input,
   .erase .output,.moveRight .output,.moveRight .output,.halt]

def prepared (pc : Nat) (key : Fin 3 → Bool) (ciphertext : Bool) : Configuration :=
  {pc := pc,inputTape := preload (NativeFairRecoveryRequest.word key ciphertext) {left := List.replicate 30 none},
   outputTape := {left := [none,none]},halted := true}

theorem leaf_run (key : Fin 3 → Bool) (ciphertext decision : Bool) :
    evalConfigWithin (leaf key)
      (NativeBitChoice.start (NativeKeyPairObserver.keyed key {left := List.replicate 27 none})
        {left := [some decision,some (!ciphertext)]}) 30 = PMF.pure (prepared 30 key ciphertext) := by
  cases ciphertext <;>
    simp [leaf,prepared,NativeFairRecoveryRequest.word,NativeKeyPairObserver.keyed,preload,evalConfigWithin,stepPMF,next,
      NativeBitChoice.start,Instruction.next,Configuration.tape,Configuration.updateTape,Configuration.advance,
      Tape.moveLeft,Tape.moveRight,Tape.write,List.replicate_succ]

theorem leaf_stops (key : Fin 3 → Bool) : StopsEverywhere (leaf key) 30 := by
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

def decoder : Program := compile 3 leaf
def code : Program := NativeKeyPairObserver.rewind.followedBy decoder

theorem decoder_stops : StopsEverywhere decoder 39 :=
  NativeBitDecoderTotal.compile_stops_everywhere 3 leaf 30 leaf_stops

theorem stops : StopsEverywhere code 50 :=
  NativeUniformSequence.stops _ _ 10 39 NativeKeyPairObserver.rewind_stops decoder_stops

theorem run (pc : Nat) (result : Fin 5 × Bool) :
    evalConfigWithin code ((NativePreparedState.finish pc result).resumeAt 0) 50 =
      PMF.pure (prepared (NativeKeyPairObserver.rewind.length + decoder.length + 2)
        (NativeEightBitCipher.encodeKey result.1) result.2) := by
  unfold code
  change evalConfigWithin (NativeKeyPairObserver.rewind.followedBy decoder)
    (NativeBitChoice.start (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 27 none})
      {left := [some (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.keyPairTest result),some (!result.2)]}) 50 = _
  rw [NativeUniformSequence.run _ _ 10 39 NativeKeyPairObserver.rewind_stops decoder_stops]
  have hr := NativePrivateHistoryErasure.run [.left,.left,.left]
    (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 27 none})
    {left := [some (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.keyPairTest result),some (!result.2)]}
  rw [NativeKeyPairObserver.rewind_tape] at hr
  change evalConfigWithin NativeKeyPairObserver.rewind
    (NativeBitChoice.start (NativeKeyPairObserver.keyed (NativeEightBitCipher.encodeKey result.1) {left := List.replicate 27 none})
      {left := [some (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.keyPairTest result),some (!result.2)]}) 10 = _ at hr
  rw [hr,PMF.pure_bind]
  change (evalConfigWithin (compile 3 leaf)
    (NativeBitChoice.start (preload (List.ofFn (NativeEightBitCipher.encodeKey result.1)) {left := List.replicate 27 none})
      {left := [some (Foundation.Crypto.Semantics.Probability.ClassicalBitRepair.keyPairTest result),some (!result.2)]}) 39).map _ = _
  rw [compile_run 3 leaf 30 (fun bits input output => leaf_stops bits input output),
    NativeKeyPairObserver.after_read_key,leaf_run,PMF.pure_map,PMF.pure_map]
  rfl

theorem prepared_equivalent (pc : Nat) (key : Fin 5) (ciphertext : Bool) :
    ((prepared pc (NativeEightBitCipher.encodeKey key) ciphertext).resumeAt 0).Equivalent
      (NativeFairRecoverySampler.entry key ciphertext {left := List.replicate 30 none} {left := [none,none]}) := by
  refine ⟨rfl,rfl,?_,?_⟩
  · have blank := Tape.blank_padding_equivalent (List.replicate 30 none) 15
    exact (NativeControlledCipherInitial.preload_equivalent (NativeFairRecoverySampler.rawInput key ciphertext) blank).symm
  · exact (Tape.blank_padding_equivalent [none,none] 1).symm

theorem code_length : code.length ≤ 309 := by
  have h := compile_length_bound 3 leaf 31 (fun bits => by rfl)
  change decoder.length + 6 ≤ 8 * (31 + 6) at h
  rw [code,NativeUniformSequence.code_length]
  have small : NativeKeyPairObserver.rewind.length = 16 := by
    change (NativePrivateHistoryErasure.code [.left,.left,.left]).length = _
    rw [NativePrivateHistoryErasure.code_length]
    rfl
  rw [small]
  omega

theorem haltsWithin (input : List Bool) : HaltsWithin code input 50 := stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 50
  polynomial := PolynomiallyBounded.const 50
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

end Machine.NativeReferenceFairRequest
