import Foundation.Crypto.Semantics.Machine.NativeEightBitCipher
import Foundation.Crypto.Semantics.Machine.EightBitCipherControl

/-! One fixed native program reads a control point and plaintext from input.
The finite decision-tree construction has a large code-size bound; this is a
reference realization, not a polynomial-size compiler in the request width. -/
namespace Machine.NativeControlledEightBitCipher
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence EightBitCipherControl
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def leaves (word : Fin 19 → Bool) : Program :=
  match parseRequest word with
  | none => [.halt]
  | some (v, message) => NativeEightBitCipher.code v message

theorem halt_stops : StopsEverywhere [.halt] 91 := by
  intro input output
  exact NativeBitDecoderTotal.stops_mono [.halt] input output 1 91 (by decide)
    (NativeBitGenerator.code_stops 0 input output)

theorem leaves_stops (word : Fin 19 → Bool) : StopsEverywhere (leaves word) 91 := by
  cases h : parseRequest word with
  | none => simpa only [leaves, h] using halt_stops
  | some result =>
    obtain ⟨v, message⟩ := result
    simpa only [leaves, h] using NativeEightBitCipher.stops v message

theorem leaves_length_bound (word : Fin 19 → Bool) : (leaves word).length ≤ 3926 := by
  cases h : parseRequest word with
  | none => simp [leaves, h]
  | some result =>
    obtain ⟨v, message⟩ := result
    simpa only [leaves, h] using NativeEightBitCipher.code_length_bound v message

def code : Program := compile 19 leaves

theorem code_def : code = compile 19 leaves := rfl

theorem code_stops : StopsEverywhere code 148 :=
  NativeBitDecoderTotal.compile_stops_everywhere 19 leaves 91 leaves_stops

theorem code_length_bound : code.length + 6 ≤ 3932 * 2 ^ 19 := by
  rw [code_def]
  exact compile_length_bound 19 leaves 3926 leaves_length_bound

def entry (v : OrderedGridVertex 32) (message : Bool) (inputSuffix outputSuffix : Tape) : Configuration :=
  NativeBitChoice.start
    (preload (List.ofFn (request v message))
      (NativeBitGenerator.blankBlock 8 (NativePrivateBitResult.keyBuffer inputSuffix)))
    (NativePrivateBitResult.outputBuffer outputSuffix)

theorem leaves_request (v : OrderedGridVertex 32) (message : Bool) :
    leaves (request v message) = NativeEightBitCipher.code v message := by
  simp [leaves, parseRequest_request]

theorem law (v : OrderedGridVertex 32) (message : Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin code (entry v message inputSuffix outputSuffix) 148).map
      NativeEightBitCipher.observe = (tableEightBitLaw v message).map some := by
  unfold code entry
  rw [compile_run 19 leaves 91 (fun word input output => leaves_stops word input output),
    leaves_request, NativeBitGenerator.afterRead_blankBlock,
    NativePrivateBitResult.afterRead_keyBuffer, PMF.map_comp]
  have hObserve : NativeEightBitCipher.observe ∘ finishControl 19 leaves =
      NativeEightBitCipher.observe := by
    funext c
    rfl
  rw [hObserve]
  exact NativeEightBitCipher.law v message (afterRead (List.ofFn (request v message)) inputSuffix) outputSuffix

theorem haltsWithin (input : List Bool) : HaltsWithin code input 148 :=
  code_stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 148
  polynomial := PolynomiallyBounded.const 148
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

end Machine.NativeControlledEightBitCipher
