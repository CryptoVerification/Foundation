import Foundation.Crypto.Semantics.Machine.NativeRandomPrivateResult
import Foundation.Crypto.Semantics.Machine.CertifiedReduction
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitExperiment

/-! Native realizations of the fixed control-point/message eight-bit experiments.
The program is generated for each control point and message; a common program
that reads those parameters, and caller encapsulation, remain separate tasks. -/
namespace Machine.NativeEightBitCipher
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

def encodeKey (key : Fin 5) : Fin 3 → Bool :=
  (bitIndexEquiv 3).symm (key.castLE (by decide : 5 ≤ 2 ^ 3))

def decodeKey (bits : Fin 3 → Bool) : Option (Fin 5) :=
  let index := bitIndexEquiv 3 bits
  if h : index.val < 5 then some ⟨index.val, h⟩ else none

theorem decode_encodeKey (key : Fin 5) : decodeKey (encodeKey key) = some key := by
  simp [decodeKey, encodeKey]

def payload (v : OrderedGridVertex 32) (message : Bool) (bits : Fin 8 → Bool) :
    (Fin 3 → Bool) × Bool :=
  let result := tableEightBitResult v message bits
  (encodeKey result.1, result.2)

def code (v : OrderedGridVertex 32) (message : Bool) : Program :=
  NativeRandomPrivateResult.code 8 (payload v message)

def entry (inputSuffix outputSuffix : Tape) : Configuration :=
  NativeBitChoice.start
    (NativeBitGenerator.blankBlock 8 (NativePrivateBitResult.keyBuffer inputSuffix))
    (NativePrivateBitResult.outputBuffer outputSuffix)

def decodeResult (value : Option ((Fin 3 → Bool) × Bool)) : Option (Fin 5 × Bool) :=
  value.bind fun result => (decodeKey result.1).map (fun key => (key, result.2))

def observe (c : Configuration) : Option (Fin 5 × Bool) :=
  decodeResult (NativeRandomPrivateResult.observe c)

theorem observe_control (c : Configuration) (pc : ℕ) :
    observe {c with pc := pc, halted := true} = observe c := rfl

theorem law (v : OrderedGridVertex 32) (message : Bool) (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin (code v message) (entry inputSuffix outputSuffix) 91).map observe =
      (tableEightBitLaw v message).map some := by
  change (evalConfigWithin (NativeRandomPrivateResult.code 8 (payload v message))
    (NativeBitChoice.start
      (NativeBitGenerator.blankBlock 8 (NativePrivateBitResult.keyBuffer inputSuffix))
      (NativePrivateBitResult.outputBuffer outputSuffix)) (10 * 8 + 11)).map
        (decodeResult ∘ NativeRandomPrivateResult.observe) = _
  rw [← PMF.map_comp, NativeRandomPrivateResult.observed_run, PMF.map_comp]
  unfold tableEightBitLaw
  rw [PMF.map_comp]
  congr 1
  funext bits
  simp [decodeResult, payload, decode_encodeKey]

theorem stops (v : OrderedGridVertex 32) (message : Bool) :
    NativeUniformSequence.StopsEverywhere (code v message) 91 :=
  NativeRandomPrivateResult.eight_bit_stops (payload v message)

theorem haltsWithin (v : OrderedGridVertex 32) (message : Bool) (input : List Bool) :
    HaltsWithin (code v message) input 91 :=
  NativeRandomPrivateResult.haltsWithin 8 (payload v message) input

theorem polynomial_time (v : OrderedGridVertex 32) (message : Bool) :
    PolynomialTime (code v message) :=
  NativeRandomPrivateResult.polynomial_time 8 (payload v message)

theorem code_length_bound (v : OrderedGridVertex 32) (message : Bool) :
    (code v message).length ≤ 3926 :=
  NativeRandomPrivateResult.eight_bit_code_length_bound (payload v message)

def bounded (v : OrderedGridVertex 32) (message : Bool) : CryptoLogic.BoundedProgram where
  program := code v message
  budget := fun _ => 91
  polynomial := PolynomiallyBounded.const 91
  halts := haltsWithin v message

end Machine.NativeEightBitCipher
