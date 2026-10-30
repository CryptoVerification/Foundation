import Foundation.Crypto.Semantics.Machine.NativeControlledCipherInitial
import Foundation.Crypto.Semantics.Probability.ClassicalBitRecoverableSampler

/-! One fixed native conditional sampler reads a source bit and ciphertext,
uses seven fair coins, and stores a private three-bit target key. Raw-request
preparation by a larger caller is a separate obligation. -/
namespace Machine.NativeRecoverableKeySampler
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def request (bit ciphertext : Bool) : Fin 2 → Bool := ![bit,ciphertext]
def rawInput (bit ciphertext : Bool) : List Bool := List.ofFn (request bit ciphertext)

def payload (bit ciphertext : Bool) (coins : Fin 7 → Bool) : (Fin 3 → Bool) × Bool :=
  (NativeEightBitCipher.encodeKey (RecoverableSampler.sample bit coins), ciphertext)

def leaves (word : Fin 2 → Bool) : Program := NativeRandomPrivateResult.code 7 (payload (word 0) (word 1))

theorem leaves_stops (word : Fin 2 → Bool) : StopsEverywhere (leaves word) 81 :=
  NativeRandomPrivateResult.code_stops 7 _

theorem leaves_length (word : Fin 2 → Bool) : (leaves word).length ≤ 1995 := by
  have h := NativeRandomPrivateResult.code_length_bound 7 (payload (word 0) (word 1))
  change (leaves word).length + 2 ≤ 15 * 2 ^ 7 + 11 * 7 at h
  omega

def code : Program := compile 2 leaves

theorem code_def : code = compile 2 leaves := rfl

theorem stops : StopsEverywhere code 87 :=
  NativeBitDecoderTotal.compile_stops_everywhere 2 leaves 81 leaves_stops

theorem code_length : code.length + 6 ≤ 8004 := by
  rw [code_def]
  exact compile_length_bound 2 leaves 1995 leaves_length

def entry (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) : Configuration :=
  NativeBitChoice.start
    (preload (rawInput bit ciphertext) (NativeBitGenerator.blankBlock 7 (NativePrivateBitResult.keyBuffer inputSuffix)))
    (NativePrivateBitResult.outputBuffer outputSuffix)

def finish (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) (coins : Fin 7 → Bool) : Configuration :=
  finishControl 2 leaves (NativeRandomPrivateResult.finish 7 (payload bit ciphertext) coins
    (afterRead (rawInput bit ciphertext) inputSuffix) outputSuffix)

theorem leaves_request (bit ciphertext : Bool) :
    leaves (request bit ciphertext) = NativeRandomPrivateResult.code 7 (payload bit ciphertext) := rfl

theorem full_run (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin code (entry bit ciphertext inputSuffix outputSuffix) 87 =
      (uniform (Fin 7 → Bool)).map (finish bit ciphertext inputSuffix outputSuffix) := by
  rw [code_def]
  unfold entry rawInput
  rw [compile_run 2 leaves 81 (fun word input output => leaves_stops word input output),
    leaves_request, NativeBitGenerator.afterRead_blankBlock, NativePrivateBitResult.afterRead_keyBuffer,
    NativeRandomPrivateResult.run, PMF.map_comp]
  rfl

theorem observe_finishControl (n : ℕ) (table : (Fin n → Bool) → Program) (c : Configuration) :
    NativeEightBitCipher.observe (finishControl n table c) = NativeEightBitCipher.observe c := by
  cases n <;> rfl

theorem finishControl_resume (n : ℕ) (table : (Fin n → Bool) → Program) (c : Configuration) :
    (finishControl n table c).resumeAt 0 = c.resumeAt 0 := by
  cases n <;> rfl

theorem observe_finish (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) (coins : Fin 7 → Bool) :
    NativeEightBitCipher.observe (finish bit ciphertext inputSuffix outputSuffix coins) =
      some (RecoverableSampler.sample bit coins,ciphertext) := by
  rw [finish, observe_finishControl]
  change NativeEightBitCipher.decodeResult (NativeRandomPrivateResult.observe
    (NativeRandomPrivateResult.finish 7 (payload bit ciphertext) coins (afterRead (rawInput bit ciphertext) inputSuffix) outputSuffix)) = _
  rw [NativeRandomPrivateResult.observe_finish]
  simp [NativeEightBitCipher.decodeResult, payload, NativeEightBitCipher.decode_encodeKey]

theorem framed_law (bit ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin code (entry bit ciphertext inputSuffix outputSuffix) 87).map NativeEightBitCipher.observe =
      (Recoverable.forward bit).map (fun key => some (key,ciphertext)) := by
  rw [full_run, PMF.map_comp]
  have h : NativeEightBitCipher.observe ∘ finish bit ciphertext inputSuffix outputSuffix =
      (fun key => some (key,ciphertext)) ∘ RecoverableSampler.sample bit := by
    funext coins
    exact observe_finish bit ciphertext inputSuffix outputSuffix coins
  rw [h, ← PMF.map_comp, RecoverableSampler.sample_law]

theorem entry_equivalent (bit ciphertext : Bool) :
    (entry bit ciphertext {} {}).Equivalent (Configuration.initial (rawInput bit ciphertext)) := by
  refine ⟨rfl, rfl, ?_, Tape.blank_padding_equivalent [] 1⟩
  have blank : (NativeBitGenerator.blankBlock 7 (NativePrivateBitResult.keyBuffer {})).Equivalent {} :=
    Tape.blank_padding_equivalent [] 10
  exact (NativeControlledCipherInitial.preload_equivalent _ blank).trans (NativeControlledCipherInitial.preload_empty _)

theorem initial_law (bit ciphertext : Bool) :
    (evalConfigWithin code (Configuration.initial (rawInput bit ciphertext)) 87).map NativeEightBitCipher.observe =
      (Recoverable.forward bit).map (fun key => some (key,ciphertext)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (entry_equivalent bit ciphertext).symm
    87 _ NativeControlledCipherInitial.observe_equivalent]
  exact framed_law bit ciphertext {} {}

theorem input_length (bit ciphertext : Bool) : (rawInput bit ciphertext).length = 2 := by
  simp only [rawInput, List.length_ofFn]

theorem haltsWithin (input : List Bool) : HaltsWithin code input 87 := stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 87
  polynomial := PolynomiallyBounded.const 87
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

end Machine.NativeRecoverableKeySampler
