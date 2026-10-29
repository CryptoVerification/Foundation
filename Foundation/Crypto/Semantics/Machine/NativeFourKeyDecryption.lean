import Foundation.Crypto.Semantics.Machine.NativeCipherRealization
import Foundation.Crypto.Semantics.Machine.NativeKeyPairObserver
import Foundation.Crypto.Semantics.Machine.NativeControlledFourKeyCipher

/-! One closed native decryption program for all labelled four-key table
ciphers. It reads a 19-bit control/ciphertext header and a three-bit key label,
then writes the decrypted bit. The compiler has a finite exponential size
bound; no practical or polynomial-size compilation claim is made. -/
namespace Machine.NativeFourKeyDecryption
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

abbrev Vertex := OrderedGridVertex 32

def request (v : Vertex) (key : Fin 4) (ciphertext : Bool) : Fin 22 → Bool :=
  Fin.append (EightBitCipherControl.request v ciphertext) (NativeFourKeySampler.encodeKey key)

def header (word : Fin 22 → Bool) : Fin 19 → Bool := fun i => word (i.castAdd 3)
def keyBits (word : Fin 22 → Bool) : Fin 3 → Bool := fun i => word (i.natAdd 19)

theorem header_request (v : Vertex) (key : Fin 4) (ciphertext : Bool) :
    header (request v key ciphertext) = EightBitCipherControl.request v ciphertext := by
  funext i
  exact Fin.append_left _ _ i

theorem keyBits_request (v : Vertex) (key : Fin 4) (ciphertext : Bool) :
    keyBits (request v key ciphertext) = NativeFourKeySampler.encodeKey key := by
  funext i
  exact Fin.append_right _ _ i

def parse (word : Fin 22 → Bool) : Option Bool :=
  match EightBitCipherControl.parseRequest (header word), NativeFourKeySampler.decodeKey (keyBits word) with
  | some (v, ciphertext), some key => some (fourEncryptBit v key ciphertext)
  | _, _ => none

theorem parse_request (v : Vertex) (key : Fin 4) (ciphertext : Bool) :
    parse (request v key ciphertext) = some (fourEncryptBit v key ciphertext) := by
  simp only [parse, header_request, keyBits_request, EightBitCipherControl.parseRequest_request,
    NativeFourKeySampler.decode_encodeKey]

def leaves (word : Fin 22 → Bool) : Program :=
  match parse word with
  | none => [.halt]
  | some bit => NativeKeyPairObserver.leaf bit

theorem leaves_stops (word : Fin 22 → Bool) : StopsEverywhere (leaves word) 3 := by
  cases h : parse word with
  | none =>
    intro input output
    simpa only [leaves, h] using NativeBitDecoderTotal.stops_mono [.halt] input output 1 3 (by decide)
      (NativeBitGenerator.code_stops 0 input output)
  | some bit => simpa only [leaves, h] using NativeKeyPairObserver.leaf_stops bit

theorem leaves_request (v : Vertex) (key : Fin 4) (ciphertext : Bool) :
    leaves (request v key ciphertext) = NativeKeyPairObserver.leaf (fourEncryptBit v key ciphertext) := by
  rw [leaves, parse_request]

def code : Program := compile 22 leaves

theorem code_def : code = compile 22 leaves := rfl

theorem stops : StopsEverywhere code 69 :=
  NativeBitDecoderTotal.compile_stops_everywhere 22 leaves 3 leaves_stops

def rawInput (v : Vertex) (key : Fin 4) (ciphertext : Bool) : List Bool := List.ofFn (request v key ciphertext)

theorem input_length (v : Vertex) (key : Fin 4) (ciphertext : Bool) : (rawInput v key ciphertext).length = 22 :=
  by simp only [rawInput, List.length_ofFn]

def entry (v : Vertex) (key : Fin 4) (ciphertext : Bool) : Configuration :=
  NativeBitChoice.start (preload (rawInput v key ciphertext) {}) (NativePrivateBitResult.outputBuffer {})

theorem entry_equivalent (v : Vertex) (key : Fin 4) (ciphertext : Bool) :
    (entry v key ciphertext).Equivalent (Configuration.initial (rawInput v key ciphertext)) :=
  ⟨rfl, rfl, NativeControlledCipherInitial.preload_empty _, Tape.blank_padding_equivalent [] 1⟩

theorem framed_law (v : Vertex) (key : Fin 4) (ciphertext : Bool) :
    (evalConfigWithin code (entry v key ciphertext) 69).map NativeKeyPairDecisionExecution.readDecision =
      PMF.pure (some (fourEncryptBit v key ciphertext)) := by
  rw [code_def]
  unfold entry rawInput
  rw [compile_run 22 leaves 3 (fun word input output => leaves_stops word input output),
    leaves_request, NativeKeyPairObserver.leaf_run, PMF.pure_map, PMF.pure_map]
  rfl

theorem initial_law (v : Vertex) (key : Fin 4) (ciphertext : Bool) :
    (evalConfigWithin code (Configuration.initial (rawInput v key ciphertext)) 69).map
      NativeKeyPairDecisionExecution.readDecision = PMF.pure (some (fourEncryptBit v key ciphertext)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (entry_equivalent v key ciphertext).symm 69 _
    NativeKeyPairDecisionExecution.readDecision_equivalent]
  exact framed_law v key ciphertext

theorem haltsWithin (input : List Bool) : HaltsWithin code input 69 := stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 69
  polynomial := PolynomiallyBounded.const 69
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

theorem correctness (v : Vertex) (key : Fin 4) (message : Bool) :
    (evalConfigWithin code (Configuration.initial (rawInput v key (fourEncryptBit v key message))) 69).map
      NativeKeyPairDecisionExecution.readDecision = PMF.pure (some message) := by
  rw [initial_law, fourEncryptBit_correct]

theorem atom_probability (v : Vertex) (key : Fin 4) (ciphertext message : Bool) :
    (eventProb ((evalConfigWithin code (Configuration.initial (rawInput v key ciphertext)) 69).map
      NativeKeyPairDecisionExecution.readDecision) (· = some message)).toReal =
      NativeCipherRealization.decryptionAtom (FourKeyWitness.cipher v).toCipher key ciphertext message := by
  rw [initial_law]
  have hz : (if ciphertext then (FourKeyWitness.cipher v).toCipher.dec1 key else (FourKeyWitness.cipher v).toCipher.dec0 key) =
      if fourEncryptBit v key ciphertext then (0 : ℝ) else 1 := fourEncryptBit_probability v key ciphertext
  unfold NativeCipherRealization.decryptionAtom
  rw [hz]
  cases fourEncryptBit v key ciphertext <;> cases message <;> simp [eventProb]

theorem code_length_bound : code.length + 6 ≤ 9 * 2 ^ 22 := by
  rw [code_def]
  apply compile_length_bound 22 leaves 3
  intro word
  cases h : parse word <;> simp [leaves, h, NativeKeyPairObserver.leaf]

end Machine.NativeFourKeyDecryption
