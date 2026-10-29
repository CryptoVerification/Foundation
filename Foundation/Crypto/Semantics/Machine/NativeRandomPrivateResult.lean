import Foundation.Crypto.Semantics.Machine.NativeBitGenerator
import Foundation.Crypto.Semantics.Machine.NativeBitDecoderTotal
import Foundation.Crypto.Semantics.Machine.PolynomialTime

/-! Fresh native coins flow directly into native decoding and private result storage. -/
namespace Machine.NativeRandomPrivateResult
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence

def code (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool) : Program :=
  (NativeBitGenerator.code n).followedBy (NativePrivateBitResult.compiled n payload)

def returnPc (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool) : ℕ :=
  (NativeBitGenerator.code n).length + (NativePrivateBitResult.compiled n payload).length + 2

def finish (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool)
    (bits : Fin n → Bool) (inputSuffix outputSuffix : Tape) : Configuration :=
  {NativePrivateBitResult.bufferedFinish (List.ofFn bits) (payload bits).1 (payload bits).2
      inputSuffix outputSuffix with pc := returnPc n payload, halted := true}

theorem code_stops (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool) :
    StopsEverywhere (code n payload) (10 * n + 11) := by
  have h := NativeUniformSequence.stops (NativeBitGenerator.code n)
    (NativePrivateBitResult.compiled n payload) (7 * n + 1) (9 + 3 * n)
    (NativeBitGenerator.code_stops n) (NativeBitDecoderTotal.private_payload_stops_everywhere n payload)
  have hTime : (7 * n + 1) + (9 + 3 * n) + 1 = 10 * n + 11 := by omega
  rw [hTime] at h
  exact h

theorem code_length_bound (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool) :
    (code n payload).length + 2 ≤ 15 * 2 ^ n + 11 * n := by
  have h := NativePrivateBitResult.compiled_length_bound n payload
  simp only [code, NativeUniformSequence.code_length, NativeBitGenerator.code_length]
  omega

theorem run (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool)
    (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (code n payload)
      (NativeBitChoice.start
        (NativeBitGenerator.blankBlock n (NativePrivateBitResult.keyBuffer inputSuffix))
        (NativePrivateBitResult.outputBuffer outputSuffix)) (10 * n + 11) =
      (uniform (Fin n → Bool)).map (fun bits => finish n payload bits inputSuffix outputSuffix) := by
  rw [show 10 * n + 11 = (7 * n + 1) + (9 + 3 * n) + 1 by omega,
    code, NativeUniformSequence.run _ _ _ _ (NativeBitGenerator.code_stops n)
      (NativeBitDecoderTotal.private_payload_stops_everywhere n payload),
    NativeBitGenerator.run, PMF.bind_map]
  have hDecode (bits : Fin n → Bool) :
      evalConfigWithin (NativePrivateBitResult.compiled n payload)
        ((NativeBitGenerator.finish n bits (NativePrivateBitResult.keyBuffer inputSuffix)
          (NativePrivateBitResult.outputBuffer outputSuffix)).resumeAt 0) (9 + 3 * n) =
      PMF.pure (finishControl n (fun word => NativePrivateBitResult.code (payload word).1 (payload word).2)
        (NativePrivateBitResult.bufferedFinish (List.ofFn bits) (payload bits).1 (payload bits).2
          inputSuffix outputSuffix)) :=
    NativePrivateBitResult.compiled_buffers_run n payload bits inputSuffix outputSuffix
  simp only [Function.comp_def, hDecode, PMF.pure_map]
  rw [PMF.map]
  congr 1
  funext bits
  apply congrArg PMF.pure
  exact finishControl_overwrite n _ _ _

def observe (c : Configuration) : Option ((Fin 3 → Bool) × Bool) :=
  match c.inputTape.left, c.outputTape.left with
  | some b2 :: some b1 :: some b0 :: _, some ciphertext :: _ =>
      some (![b0, b1, b2], ciphertext)
  | _, _ => none

theorem observe_finish (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool)
    (bits : Fin n → Bool) (inputSuffix outputSuffix : Tape) :
    observe (finish n payload bits inputSuffix outputSuffix) = some (payload bits) := by
  have hkey : ![(payload bits).1 0, (payload bits).1 1, (payload bits).1 2] = (payload bits).1 := by
    funext i
    fin_cases i <;> rfl
  change some (![(payload bits).1 0, (payload bits).1 1, (payload bits).1 2], (payload bits).2) = _
  rw [hkey, Prod.mk.eta]

theorem observed_run (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool)
    (inputSuffix outputSuffix : Tape) :
    (evalConfigWithin (code n payload)
      (NativeBitChoice.start
        (NativeBitGenerator.blankBlock n (NativePrivateBitResult.keyBuffer inputSuffix))
        (NativePrivateBitResult.outputBuffer outputSuffix)) (10 * n + 11)).map observe =
      (uniform (Fin n → Bool)).map (fun bits => some (payload bits)) := by
  rw [run, PMF.map_comp]
  congr 1
  funext bits
  exact observe_finish n payload bits inputSuffix outputSuffix

theorem haltsWithin (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool)
    (input : List Bool) : HaltsWithin (code n payload) input (10 * n + 11) :=
  code_stops n payload (Tape.ofBits input) {}

theorem polynomial_time (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool) :
    PolynomialTime (code n payload) :=
  ⟨fun _ => 10 * n + 11, PolynomiallyBounded.const _, haltsWithin n payload⟩

theorem eight_bit_stops (payload : (Fin 8 → Bool) → (Fin 3 → Bool) × Bool) :
    StopsEverywhere (code 8 payload) 91 := code_stops 8 payload

theorem eight_bit_code_length_bound (payload : (Fin 8 → Bool) → (Fin 3 → Bool) × Bool) :
    (code 8 payload).length ≤ 3926 := by
  have h := code_length_bound 8 payload
  norm_num at h
  omega

end Machine.NativeRandomPrivateResult
