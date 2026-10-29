import Foundation.Crypto.Semantics.Machine.NativeFourKeySampler
import Foundation.Crypto.Semantics.Machine.EightBitCipherControl

/-! One fixed native program reads a control point and plaintext from input.
The finite decision-tree construction has a large code-size bound; this is a
reference realization, not a polynomial-size compiler in the request width. -/
namespace Machine.NativeControlledFourKeyCipher
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence EightBitCipherControl
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def leaves (word : Fin 19 → Bool) : Program :=
  match parseRequest word with
  | none => [.halt]
  | some (v, message) => NativeFourKeySampler.code v message

theorem halt_stops : StopsEverywhere [.halt] 91 := by
  intro input output
  exact NativeBitDecoderTotal.stops_mono [.halt] input output 1 91 (by decide)
    (NativeBitGenerator.code_stops 0 input output)

theorem leaves_stops (word : Fin 19 → Bool) : StopsEverywhere (leaves word) 91 := by
  cases h : parseRequest word with
  | none => simpa only [leaves, h] using halt_stops
  | some result =>
    obtain ⟨v, message⟩ := result
    simpa only [leaves, h] using NativeFourKeySampler.stops v message

theorem leaves_length_bound (word : Fin 19 → Bool) : (leaves word).length ≤ 3926 := by
  cases h : parseRequest word with
  | none => simp [leaves, h]
  | some result =>
    obtain ⟨v, message⟩ := result
    simpa only [leaves, h] using NativeFourKeySampler.code_length_bound v message

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
    leaves (request v message) = NativeFourKeySampler.code v message := by
  simp [leaves, parseRequest_request]

theorem law (v : OrderedGridVertex 32) (message : Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin code (entry v message inputSuffix outputSuffix) 148).map
      NativeFourKeySampler.observe = (fourEightBitLaw v message).map some := by
  unfold code entry
  rw [compile_run 19 leaves 91 (fun word input output => leaves_stops word input output),
    leaves_request, NativeBitGenerator.afterRead_blankBlock,
    NativePrivateBitResult.afterRead_keyBuffer, PMF.map_comp]
  have hObserve : NativeFourKeySampler.observe ∘ finishControl 19 leaves =
      NativeFourKeySampler.observe := by
    funext c
    rfl
  rw [hObserve]
  exact NativeFourKeySampler.law v message (afterRead (List.ofFn (request v message)) inputSuffix) outputSuffix

theorem haltsWithin (input : List Bool) : HaltsWithin code input 148 :=
  code_stops (Tape.ofBits input) {}

def bounded : CryptoLogic.BoundedProgram where
  program := code
  budget := fun _ => 148
  polynomial := PolynomiallyBounded.const 148
  halts := haltsWithin

theorem polynomial_time : PolynomialTime code := bounded.polynomialTime

end Machine.NativeControlledFourKeyCipher

namespace Machine.NativeControlledFourKeyCipher
open Foundation.Probability NativeBitDecisionTree
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def rawInput (v : OrderedGridVertex 32) (message : Bool) : List Bool :=
  List.ofFn (EightBitCipherControl.request v message)

theorem entry_equivalent (v : OrderedGridVertex 32) (message : Bool) :
    (entry v message {} {}).Equivalent (Configuration.initial (rawInput v message)) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact (NativeControlledCipherInitial.preload_equivalent _
      NativeControlledCipherInitial.blank_workspace).trans (NativeControlledCipherInitial.preload_empty _)
  · exact Tape.blank_padding_equivalent [] 1

theorem initial_law (v : OrderedGridVertex 32) (message : Bool) :
    (evalConfigWithin code (Configuration.initial (rawInput v message)) 148).map
      NativeFourKeySampler.observe = (fourEightBitLaw v message).map some := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _ (entry_equivalent v message).symm
    148 _ NativeFourKeySampler.observe_equivalent]
  exact law v message {} {}

theorem atom_probability (v : OrderedGridVertex 32) (message : Bool) (result : Fin 4 × Bool) :
    (eventProb ((evalConfigWithin code (Configuration.initial (rawInput v message)) 148).map
      NativeFourKeySampler.observe) (· = some result)).toReal =
      (eventProb (fourEightBitLaw v message) (· = result)).toReal := by
  rw [initial_law, eventProb_map]
  simp only [Option.some.injEq]

end Machine.NativeControlledFourKeyCipher
