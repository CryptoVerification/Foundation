import Foundation.Crypto.Semantics.Machine.NativeBitDecisionTree

/-! Native leaves write three private key bits and one output ciphertext bit.
The generic decoder is a fixed finite program for every fixed payload table. -/
namespace Machine.NativePrivateBitResult
open Foundation.Probability NativeBitDecisionTree

def code (key : Fin 3 → Bool) (ciphertext : Bool) : Program :=
  [.write .input (key 0), .moveRight .input,
   .write .input (key 1), .moveRight .input,
   .write .input (key 2), .moveRight .input,
   .write .output ciphertext, .moveRight .output, .halt]

def writeKey (key : Fin 3 → Bool) (input : Tape) : Tape :=
  let first := (input.write (some (key 0))).moveRight
  let second := (first.write (some (key 1))).moveRight
  (second.write (some (key 2))).moveRight

def finish (key : Fin 3 → Bool) (ciphertext : Bool) (input output : Tape) : Configuration :=
  {pc := 8, inputTape := writeKey key input,
    outputTape := (output.write (some ciphertext)).moveRight, halted := true}

theorem code_length (key : Fin 3 → Bool) (ciphertext : Bool) :
    (code key ciphertext).length = 9 := rfl

theorem run (key : Fin 3 → Bool) (ciphertext : Bool) (input output : Tape) :
    evalConfigWithin (code key ciphertext) (NativeBitChoice.start input output) 9 =
      PMF.pure (finish key ciphertext input output) := by
  simp [evalConfigWithin, stepPMF, next, code, NativeBitChoice.start, Instruction.next,
    Configuration.updateTape, Configuration.advance, finish, writeKey]

theorem stops (key : Fin 3 → Bool) (ciphertext : Bool) (input output : Tape) :
    Stops (code key ciphertext) input output 9 := by
  intro target trace
  have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  rw [run, PMF.mem_support_pure_iff] at member
  subst target
  rfl

def keyBuffer (suffix : Tape) : Tape :=
  {left := suffix.left, right := none :: none :: suffix.current :: suffix.right}

def outputBuffer (suffix : Tape) : Tape :=
  {left := suffix.left, right := suffix.current :: suffix.right}

theorem writeKey_buffer (key : Fin 3 → Bool) (suffix : Tape) :
    writeKey key (keyBuffer suffix) =
      {suffix with left := some (key 2) :: some (key 1) :: some (key 0) :: suffix.left} := by
  simp [writeKey, keyBuffer, Tape.write, Tape.moveRight]

theorem writeOutput_buffer (ciphertext : Bool) (suffix : Tape) :
    ((outputBuffer suffix).write (some ciphertext)).moveRight =
      {suffix with left := some ciphertext :: suffix.left} := by
  simp [outputBuffer, Tape.write, Tape.moveRight]

def compiled (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool) : Program :=
  compile n (fun bits => code (payload bits).1 (payload bits).2)

theorem compiled_halts (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool)
    (bits : Fin n → Bool) (suffix output : Tape) :
    Stops (compiled n payload) (preload (List.ofFn bits) suffix) output (9 + 3 * n) :=
  compile_halts n _ 9 (fun _bits input output => stops _ _ input output) bits suffix output

theorem compiled_run (n : ℕ) (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool)
    (bits : Fin n → Bool) (suffix output : Tape) :
    evalConfigWithin (compiled n payload)
      (NativeBitChoice.start (preload (List.ofFn bits) suffix) output) (9 + 3 * n) =
      PMF.pure (finishControl n (fun word => code (payload word).1 (payload word).2)
        (finish (payload bits).1 (payload bits).2 (afterRead (List.ofFn bits) suffix) output)) := by
  unfold compiled
  rw [compile_run n _ 9 (fun _bits input output => stops _ _ input output), run, PMF.pure_map]

theorem compiled_length_bound (n : ℕ)
    (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool) :
    (compiled n payload).length + 6 ≤ 15 * 2 ^ n := by
  exact compile_length_bound n _ 9 (fun bits => by rw [code_length])

def bufferedFinish (word : List Bool) (key : Fin 3 → Bool) (ciphertext : Bool)
    (inputSuffix outputSuffix : Tape) : Configuration :=
  {pc := 8,
    inputTape := {inputSuffix with left := some (key 2) :: some (key 1) :: some (key 0) ::
      (word.reverse.map some ++ inputSuffix.left)},
    outputTape := {outputSuffix with left := some ciphertext :: outputSuffix.left},
    halted := true}

theorem afterRead_keyBuffer (word : List Bool) (suffix : Tape) :
    afterRead word (keyBuffer suffix) = keyBuffer (afterRead word suffix) := rfl

theorem finish_buffers (word : List Bool) (key : Fin 3 → Bool) (ciphertext : Bool)
    (inputSuffix outputSuffix : Tape) :
    finish key ciphertext (afterRead word (keyBuffer inputSuffix))
      (outputBuffer outputSuffix) = bufferedFinish word key ciphertext inputSuffix outputSuffix := by
  unfold finish
  rw [afterRead_keyBuffer, writeKey_buffer, writeOutput_buffer]
  rfl

theorem compiled_buffers_run (n : ℕ)
    (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool) (bits : Fin n → Bool)
    (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (compiled n payload)
      (NativeBitChoice.start (preload (List.ofFn bits) (keyBuffer inputSuffix))
        (outputBuffer outputSuffix)) (9 + 3 * n) =
      PMF.pure (finishControl n (fun word => code (payload word).1 (payload word).2)
        (bufferedFinish (List.ofFn bits) (payload bits).1 (payload bits).2
          inputSuffix outputSuffix)) := by
  rw [compiled_run, finish_buffers]

end Machine.NativePrivateBitResult
