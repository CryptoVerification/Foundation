import Foundation.Crypto.Semantics.Machine.NativeRecoverableKeySampler
import Foundation.Crypto.Semantics.Probability.ClassicalBitFairRecovery

/-! Two fixed native programs for the finitely fair five-state kernels.
Each reads a three-bit key and ciphertext, draws twelve fresh bits, and writes
an encoded private key and unchanged ciphertext. Request and coin history
remain on tape; erasure and full caller adapters are separate obligations. -/
namespace Machine.NativeFairRecoverySampler
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def sample (backward : Bool) (key : Fin 5) : (Fin 12 → Bool) → Fin 5 :=
  if backward then FairRecovery.sampleReverse key else FairRecovery.sampleForward key

noncomputable def kernel (backward : Bool) : Fin 5 → PMF (Fin 5) :=
  if backward then FairRecovery.reverse else FairRecovery.forward

theorem sample_law (backward : Bool) (key : Fin 5) :
    (uniform (Fin 12 → Bool)).map (sample backward key) = kernel backward key := by
  cases backward
  · exact FairRecovery.forward_sample_law key
  · exact FairRecovery.reverse_sample_law key

def request (key : Fin 5) (ciphertext : Bool) : Fin 4 → Bool :=
  ![NativeEightBitCipher.encodeKey key 0, NativeEightBitCipher.encodeKey key 1,
    NativeEightBitCipher.encodeKey key 2, ciphertext]
def rawInput (key : Fin 5) (ciphertext : Bool) : List Bool := List.ofFn (request key ciphertext)
def readKey (word : Fin 4 → Bool) : Fin 5 :=
  (NativeEightBitCipher.decodeKey ![word 0,word 1,word 2]).getD 0

theorem read_request (key : Fin 5) (ciphertext : Bool) : readKey (request key ciphertext) = key := by
  have same : ![NativeEightBitCipher.encodeKey key 0, NativeEightBitCipher.encodeKey key 1,
      NativeEightBitCipher.encodeKey key 2] = NativeEightBitCipher.encodeKey key := by
    funext i
    fin_cases i <;> rfl
  change (NativeEightBitCipher.decodeKey
    ![NativeEightBitCipher.encodeKey key 0, NativeEightBitCipher.encodeKey key 1,
      NativeEightBitCipher.encodeKey key 2]).getD 0 = _
  rw [same,NativeEightBitCipher.decode_encodeKey]
  rfl

def payload (backward : Bool) (key : Fin 5) (ciphertext : Bool) (coins : Fin 12 → Bool) : (Fin 3 → Bool) × Bool :=
  (NativeEightBitCipher.encodeKey (sample backward key coins), ciphertext)
def leaves (backward : Bool) (word : Fin 4 → Bool) : Program :=
  NativeRandomPrivateResult.code 12 (payload backward (readKey word) (word 3))

theorem leaves_stops (backward : Bool) (word : Fin 4 → Bool) : StopsEverywhere (leaves backward word) 131 :=
  NativeRandomPrivateResult.code_stops 12 _

theorem leaves_length (backward : Bool) (word : Fin 4 → Bool) : (leaves backward word).length ≤ 61570 := by
  have h := NativeRandomPrivateResult.code_length_bound 12 (payload backward (readKey word) (word 3))
  change (leaves backward word).length + 2 ≤ 15 * 2 ^ 12 + 11 * 12 at h
  omega

def code (backward : Bool) : Program := compile 4 (leaves backward)

theorem code_def (backward : Bool) : code backward = compile 4 (leaves backward) := rfl

theorem stops (backward : Bool) : StopsEverywhere (code backward) 143 :=
  NativeBitDecoderTotal.compile_stops_everywhere 4 (leaves backward) 131 (leaves_stops backward)

theorem code_length (backward : Bool) : (code backward).length + 6 ≤ 985216 := by
  rw [code_def]
  exact compile_length_bound 4 (leaves backward) 61570 (leaves_length backward)

def entry (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) : Configuration :=
  NativeBitChoice.start
    (preload (rawInput key ciphertext) (NativeBitGenerator.blankBlock 12 (NativePrivateBitResult.keyBuffer inputSuffix)))
    (NativePrivateBitResult.outputBuffer outputSuffix)

def finish (backward : Bool) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape)
    (coins : Fin 12 → Bool) : Configuration :=
  finishControl 4 (leaves backward) (NativeRandomPrivateResult.finish 12 (payload backward key ciphertext) coins
    (afterRead (rawInput key ciphertext) inputSuffix) outputSuffix)

theorem leaves_request (backward : Bool) (key : Fin 5) (ciphertext : Bool) :
    leaves backward (request key ciphertext) = NativeRandomPrivateResult.code 12 (payload backward key ciphertext) := by
  unfold leaves
  rw [read_request]
  rfl

theorem full_run (backward : Bool) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (code backward) (entry key ciphertext inputSuffix outputSuffix) 143 =
      (uniform (Fin 12 → Bool)).map (finish backward key ciphertext inputSuffix outputSuffix) := by
  rw [code_def]
  unfold entry rawInput
  rw [compile_run 4 (leaves backward) 131 (fun word input output => leaves_stops backward word input output),
    leaves_request, NativeBitGenerator.afterRead_blankBlock, NativePrivateBitResult.afterRead_keyBuffer,
    NativeRandomPrivateResult.run, PMF.map_comp]
  rfl

theorem observe_finish (backward : Bool) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape)
    (coins : Fin 12 → Bool) :
    NativeEightBitCipher.observe (finish backward key ciphertext inputSuffix outputSuffix coins) =
      some (sample backward key coins,ciphertext) := by
  rw [finish, NativeRecoverableKeySampler.observe_finishControl]
  change NativeEightBitCipher.decodeResult (NativeRandomPrivateResult.observe
    (NativeRandomPrivateResult.finish 12 (payload backward key ciphertext) coins
      (afterRead (rawInput key ciphertext) inputSuffix) outputSuffix)) = _
  rw [NativeRandomPrivateResult.observe_finish]
  simp [NativeEightBitCipher.decodeResult, payload, NativeEightBitCipher.decode_encodeKey]

theorem framed_law (backward : Bool) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin (code backward) (entry key ciphertext inputSuffix outputSuffix) 143).map NativeEightBitCipher.observe =
      (kernel backward key).map (fun result => some (result,ciphertext)) := by
  rw [full_run, PMF.map_comp]
  have h : NativeEightBitCipher.observe ∘ finish backward key ciphertext inputSuffix outputSuffix =
      (fun result => some (result,ciphertext)) ∘ sample backward key := by
    funext coins
    exact observe_finish backward key ciphertext inputSuffix outputSuffix coins
  rw [h, ← PMF.map_comp, sample_law]

theorem entry_equivalent (key : Fin 5) (ciphertext : Bool) :
    (entry key ciphertext {} {}).Equivalent (Configuration.initial (rawInput key ciphertext)) := by
  refine ⟨rfl,rfl,?_,Tape.blank_padding_equivalent [] 1⟩
  have blank : (NativeBitGenerator.blankBlock 12 (NativePrivateBitResult.keyBuffer {})).Equivalent {} :=
    Tape.blank_padding_equivalent [] 15
  exact (NativeControlledCipherInitial.preload_equivalent _ blank).trans (NativeControlledCipherInitial.preload_empty _)

theorem initial_law (backward : Bool) (key : Fin 5) (ciphertext : Bool) :
    (evalConfigWithin (code backward) (Configuration.initial (rawInput key ciphertext)) 143).map NativeEightBitCipher.observe =
      (kernel backward key).map (fun result => some (result,ciphertext)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (entry_equivalent key ciphertext).symm
    143 _ NativeControlledCipherInitial.observe_equivalent]
  exact framed_law backward key ciphertext {} {}

theorem input_length (key : Fin 5) (ciphertext : Bool) : (rawInput key ciphertext).length = 4 := by
  simp [rawInput]

theorem haltsWithin (backward : Bool) (input : List Bool) : HaltsWithin (code backward) input 143 :=
  stops backward (Tape.ofBits input) {}

def bounded (backward : Bool) : CryptoLogic.BoundedProgram where
  program := code backward
  budget := fun _ => 143
  polynomial := PolynomiallyBounded.const 143
  halts := haltsWithin backward

theorem polynomial_time (backward : Bool) : PolynomialTime (code backward) := (bounded backward).polynomialTime

end Machine.NativeFairRecoverySampler
