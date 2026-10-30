import Foundation.Crypto.Semantics.Machine.NativeFairRecoverySampler

/-! A native contract uniform over every deterministic five-state sampler
using twelve fresh bits. The four-bit request format is fixed. Resources do
not depend on the sampler table. Request and random history remain on tape. -/
namespace Machine.NativeFiveStateSampler
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

abbrev Sampler := Fin 5 → (Fin 12 → Bool) → Fin 5

noncomputable def kernel (draw : Sampler) (key : Fin 5) : PMF (Fin 5) :=
  (uniform (Fin 12 → Bool)).map (draw key)

theorem sample_law (draw : Sampler) (key : Fin 5) :
    (uniform (Fin 12 → Bool)).map (draw key) = kernel draw key := rfl

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

def payload (draw : Sampler) (key : Fin 5) (ciphertext : Bool) (coins : Fin 12 → Bool) : (Fin 3 → Bool) × Bool :=
  (NativeEightBitCipher.encodeKey (draw key coins), ciphertext)
def leaves (draw : Sampler) (word : Fin 4 → Bool) : Program :=
  NativeRandomPrivateResult.code 12 (payload draw (readKey word) (word 3))

theorem leaves_stops (draw : Sampler) (word : Fin 4 → Bool) : StopsEverywhere (leaves draw word) 131 :=
  NativeRandomPrivateResult.code_stops 12 _

theorem leaves_length (draw : Sampler) (word : Fin 4 → Bool) : (leaves draw word).length ≤ 61570 := by
  have h := NativeRandomPrivateResult.code_length_bound 12 (payload draw (readKey word) (word 3))
  change (leaves draw word).length + 2 ≤ 15 * 2 ^ 12 + 11 * 12 at h
  omega

def code (draw : Sampler) : Program := compile 4 (leaves draw)

theorem code_def (draw : Sampler) : code draw = compile 4 (leaves draw) := rfl

theorem stops (draw : Sampler) : StopsEverywhere (code draw) 143 :=
  NativeBitDecoderTotal.compile_stops_everywhere 4 (leaves draw) 131 (leaves_stops draw)

theorem code_length (draw : Sampler) : (code draw).length + 6 ≤ 985216 := by
  rw [code_def]
  exact compile_length_bound 4 (leaves draw) 61570 (leaves_length draw)

def entry (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) : Configuration :=
  NativeBitChoice.start
    (preload (rawInput key ciphertext) (NativeBitGenerator.blankBlock 12 (NativePrivateBitResult.keyBuffer inputSuffix)))
    (NativePrivateBitResult.outputBuffer outputSuffix)

def finish (draw : Sampler) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape)
    (coins : Fin 12 → Bool) : Configuration :=
  finishControl 4 (leaves draw) (NativeRandomPrivateResult.finish 12 (payload draw key ciphertext) coins
    (afterRead (rawInput key ciphertext) inputSuffix) outputSuffix)

theorem leaves_request (draw : Sampler) (key : Fin 5) (ciphertext : Bool) :
    leaves draw (request key ciphertext) = NativeRandomPrivateResult.code 12 (payload draw key ciphertext) := by
  unfold leaves
  rw [read_request]
  rfl

theorem full_run (draw : Sampler) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (code draw) (entry key ciphertext inputSuffix outputSuffix) 143 =
      (uniform (Fin 12 → Bool)).map (finish draw key ciphertext inputSuffix outputSuffix) := by
  rw [code_def]
  unfold entry rawInput
  rw [compile_run 4 (leaves draw) 131 (fun word input output => leaves_stops draw word input output),
    leaves_request, NativeBitGenerator.afterRead_blankBlock, NativePrivateBitResult.afterRead_keyBuffer,
    NativeRandomPrivateResult.run, PMF.map_comp]
  rfl

theorem observe_finish (draw : Sampler) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape)
    (coins : Fin 12 → Bool) :
    NativeEightBitCipher.observe (finish draw key ciphertext inputSuffix outputSuffix coins) =
      some (draw key coins,ciphertext) := by
  rw [finish, NativeRecoverableKeySampler.observe_finishControl]
  change NativeEightBitCipher.decodeResult (NativeRandomPrivateResult.observe
    (NativeRandomPrivateResult.finish 12 (payload draw key ciphertext) coins
      (afterRead (rawInput key ciphertext) inputSuffix) outputSuffix)) = _
  rw [NativeRandomPrivateResult.observe_finish]
  simp [NativeEightBitCipher.decodeResult, payload, NativeEightBitCipher.decode_encodeKey]

theorem framed_law (draw : Sampler) (key : Fin 5) (ciphertext : Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin (code draw) (entry key ciphertext inputSuffix outputSuffix) 143).map NativeEightBitCipher.observe =
      (kernel draw key).map (fun result => some (result,ciphertext)) := by
  rw [full_run, PMF.map_comp]
  have h : NativeEightBitCipher.observe ∘ finish draw key ciphertext inputSuffix outputSuffix =
      (fun result => some (result,ciphertext)) ∘ draw key := by
    funext coins
    exact observe_finish draw key ciphertext inputSuffix outputSuffix coins
  rw [h, ← PMF.map_comp, sample_law]

theorem entry_equivalent (key : Fin 5) (ciphertext : Bool) :
    (entry key ciphertext {} {}).Equivalent (Configuration.initial (rawInput key ciphertext)) := by
  refine ⟨rfl,rfl,?_,Tape.blank_padding_equivalent [] 1⟩
  have blank : (NativeBitGenerator.blankBlock 12 (NativePrivateBitResult.keyBuffer {})).Equivalent {} :=
    Tape.blank_padding_equivalent [] 15
  exact (NativeControlledCipherInitial.preload_equivalent _ blank).trans (NativeControlledCipherInitial.preload_empty _)

theorem initial_law (draw : Sampler) (key : Fin 5) (ciphertext : Bool) :
    (evalConfigWithin (code draw) (Configuration.initial (rawInput key ciphertext)) 143).map NativeEightBitCipher.observe =
      (kernel draw key).map (fun result => some (result,ciphertext)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (entry_equivalent key ciphertext).symm
    143 _ NativeControlledCipherInitial.observe_equivalent]
  exact framed_law draw key ciphertext {} {}

theorem input_length (key : Fin 5) (ciphertext : Bool) : (rawInput key ciphertext).length = 4 := by
  simp [rawInput]

theorem haltsWithin (draw : Sampler) (input : List Bool) : HaltsWithin (code draw) input 143 :=
  stops draw (Tape.ofBits input) {}

def bounded (draw : Sampler) : CryptoLogic.BoundedProgram where
  program := code draw
  budget := fun _ => 143
  polynomial := PolynomiallyBounded.const 143
  halts := haltsWithin draw

theorem polynomial_time (draw : Sampler) : PolynomialTime (code draw) := (bounded draw).polynomialTime

end Machine.NativeFiveStateSampler
