import Foundation.Crypto.Semantics.Machine.NativeFlaggedRequestPreparation

/-! Fixed-count raw bit transfer by native reads, writes and source erasure.
The input-to-output and output-to-input programs are static operand variants.
No runtime tape exchange or state reload is performed. -/
namespace Machine.NativeFixedRawTransfer
open Foundation.Probability NativeUniformSequence NativeBitDecisionTree NativeBoundedFlaggedTransfer

def one : Program :=
  [.branch .input 8 1 3, .write .output false, .jump 5,
   .write .output true, .jump 5, .erase .input, .moveRight .input, .moveRight .output, .halt]

theorem one_run (bit : Bool) (input output : Tape) :
    evalConfigWithin one (NativeBitChoice.start (preload [bit] input) output) 7 =
      PMF.pure {pc := 8, inputTape := erasedBefore 1 input, outputTape := (output.write (some bit)).moveRight, halted := true} := by
  cases bit <;> simp [one, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
    Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape,
    preload, Tape.moveRight, Tape.write, erasedBefore]

theorem one_stops : StopsEverywhere one 7 := by
  intro input output finish trace
  have h := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  cases hc : input.current with
  | none =>
    simp [one, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
      Instruction.next, Configuration.tape, hc] at h
    subst finish
    rfl
  | some bit =>
    cases bit <;>
      simp [one, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next,
        Configuration.tape, Configuration.updateTape, Configuration.advance,
        Tape.moveRight, Tape.write, hc] at h <;> subst finish <;> rfl

def code : ℕ → Program
  | 0 => [.halt]
  | n + 1 => one.followedBy (code n)

theorem code_length (n : ℕ) : (code n).length = 12 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [code, NativeUniformSequence.code_length, one, ih]; omega

theorem stops (n : ℕ) : StopsEverywhere (code n) (8 * n + 1) := by
  induction n with
  | zero => exact NativeBitGenerator.code_stops 0
  | succ n ih =>
    have h := NativeUniformSequence.stops one (code n) 7 (8 * n + 1) one_stops ih
    have hTime : 7 + (8 * n + 1) + 1 = 8 * (n + 1) + 1 := by omega
    simpa only [code, hTime] using h

def finish (bits : List Bool) (inputSuffix outputSuffix : Tape) : Configuration :=
  {pc := 12 * bits.length, inputTape := erasedBefore bits.length inputSuffix,
   outputTape := afterRead bits outputSuffix, halted := true}

theorem run (bits : List Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (code bits.length)
      (NativeBitChoice.start (preload bits inputSuffix) (NativeBitGenerator.blankBlock bits.length outputSuffix))
      (8 * bits.length + 1) = PMF.pure (finish bits inputSuffix outputSuffix) := by
  induction bits generalizing inputSuffix outputSuffix with
  | nil =>
    simp [code, finish, preload, erasedBefore, afterRead, NativeBitGenerator.blankBlock,
      evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next]
  | cons bit bits ih =>
    rw [show 8 * (bit :: bits).length + 1 = 7 + (8 * bits.length + 1) + 1 by simp; omega,
      show code (bit :: bits).length = one.followedBy (code bits.length) from rfl,
      NativeUniformSequence.run _ _ _ _ one_stops (stops bits.length)]
    have hload : preload (bit :: bits) inputSuffix = preload [bit] (preload bits inputSuffix) :=
      preload_append [bit] bits inputSuffix
    rw [hload, one_run, PMF.pure_bind, ← preload_erasedBefore]
    simp only [List.length_cons]
    rw [NativeBitGenerator.blankBlock_written_move]
    change (evalConfigWithin (code bits.length)
      (NativeBitChoice.start (preload bits (erasedBefore 1 inputSuffix))
        (NativeBitGenerator.blankBlock bits.length {outputSuffix with left := some bit :: outputSuffix.left}))
      (8 * bits.length + 1)).map _ = _
    rw [ih, PMF.pure_map]
    have hi : erasedBefore bits.length (erasedBefore 1 inputSuffix) =
        erasedBefore (bit :: bits).length inputSuffix := by
      rw [erasedBefore_add]
      rfl
    have ho := afterRead_cons bit bits outputSuffix
    apply congrArg PMF.pure
    simp only [finish, hi, ho, code_length]
    congr 1
    simp [one]
    omega

def backCode (n : ℕ) : Program := (code n).swapTapes

theorem back_stops (n : ℕ) : StopsEverywhere (backCode n) (8 * n + 1) :=
  NativeFixedWordRewind.stops_swap _ _ (stops n)

theorem back_run (bits : List Bool) (destination source : Tape) :
    evalConfigWithin (backCode bits.length)
      (NativeBitChoice.start (NativeBitGenerator.blankBlock bits.length destination) (preload bits source))
      (8 * bits.length + 1) =
      PMF.pure {pc := 12 * bits.length, inputTape := afterRead bits destination, outputTape := erasedBefore bits.length source, halted := true} := by
  unfold backCode
  change evalConfigWithin (code bits.length).swapTapes
    (NativeBitChoice.start (preload bits source) (NativeBitGenerator.blankBlock bits.length destination)).swapTapes _ = _
  rw [evalConfigWithin_swapTapes, run, PMF.pure_map]
  rfl

def restoredCode (n : ℕ) : Program := (backCode n).followedBy (NativeFixedWordRewind.inputCode n)

theorem restored_stops (n : ℕ) : StopsEverywhere (restoredCode n) (11 * n + 3) := by
  have h := NativeUniformSequence.stops (backCode n) (NativeFixedWordRewind.inputCode n)
    (8 * n + 1) (3 * n + 1) (back_stops n) (NativeFixedWordRewind.input_stops n)
  have hTime : (8 * n + 1) + (3 * n + 1) + 1 = 11 * n + 3 := by omega
  simpa only [restoredCode, hTime] using h

theorem restored_length (n : ℕ) : (restoredCode n).length = 17 * n + 5 := by
  simp [restoredCode, backCode, NativeFixedWordRewind.inputCode, NativeUniformSequence.code_length,
    Program.swapTapes_length, code_length, NativePrivateHistoryErasure.code_length, List.length_replicate]
  omega

def restoredFinish (bits : List Bool) (destination source : Tape) : Configuration :=
  {pc := 17 * bits.length + 4, inputTape := preload bits destination,
   outputTape := erasedBefore bits.length source, halted := true}

theorem restored_run (bits : List Bool) (destination source : Tape) :
    evalConfigWithin (restoredCode bits.length)
      (NativeBitChoice.start (NativeBitGenerator.blankBlock bits.length destination) (preload bits source))
      (11 * bits.length + 3) = PMF.pure (restoredFinish bits destination source) := by
  unfold restoredCode
  rw [show 11 * bits.length + 3 = (8 * bits.length + 1) + (3 * bits.length + 1) + 1 by omega,
    NativeUniformSequence.run _ _ _ _ (back_stops bits.length) (NativeFixedWordRewind.input_stops bits.length),
    back_run, PMF.pure_bind]
  change (evalConfigWithin (NativePrivateHistoryErasure.code (List.replicate bits.length .left))
    (NativeBitChoice.start (afterRead bits destination) (erasedBefore bits.length source))
      (3 * bits.length + 1)).map _ = _
  have h := NativePrivateHistoryErasure.run (List.replicate bits.length .left)
    (afterRead bits destination) (erasedBefore bits.length source)
  simp only [List.length_replicate, NativeFixedWordRewind.left_actions] at h
  rw [h, PMF.pure_map]
  apply congrArg PMF.pure
  simp [restoredFinish, backCode, NativeFixedWordRewind.inputCode,
    Program.swapTapes_length, code_length, NativePrivateHistoryErasure.code_length, List.length_replicate]
  omega

end Machine.NativeFixedRawTransfer
