import Foundation.Crypto.Semantics.Machine.NativeFixedWordRewind

/-! A fixed-size caller decodes flags, erases its consumed input and rewinds
the physical request on the other tape. It stops even on malformed inputs. -/
namespace Machine.NativeFlaggedRequestPreparation
open Foundation.Probability NativeUniformSequence NativeBitDecisionTree NativeBoundedFlaggedTransfer

def terminal : Program := [.branch .input 4 1 4, .erase .input, .moveRight .input, .halt, .halt]

theorem terminal_run (input output : Tape) :
    evalConfigWithin terminal (NativeBitChoice.start (preload [false] input) output) 4 =
      PMF.pure {pc := 3, inputTape := erasedBefore 1 input, outputTape := output, halted := true} := by
  simp [terminal, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next,
    Configuration.tape, Configuration.updateTape, Configuration.advance, preload,
    Tape.moveRight, Tape.write, erasedBefore]

theorem terminal_stops : StopsEverywhere terminal 4 := by
  intro input output finish trace
  have h := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  cases hc : input.current with
  | none =>
    simp [terminal, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
      Instruction.next, Configuration.tape, hc] at h
    subst finish
    rfl
  | some bit =>
    cases bit <;>
      simp [terminal, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next,
        Configuration.tape, Configuration.updateTape, Configuration.advance, hc] at h <;> subst finish <;> rfl

def decode (n : ℕ) : Program := (copies n).followedBy terminal

theorem decode_stops (n : ℕ) : StopsEverywhere (decode n) (11 * n + 6) := by
  have h := NativeUniformSequence.stops (copies n) terminal (11 * n + 1) 4 (copies_stops n) terminal_stops
  simpa only [decode, Nat.add_assoc] using h

def decodeFinish (bits : List Bool) (inputSuffix outputSuffix : Tape) : Configuration :=
  {pc := 15 * bits.length + 8, inputTape := erasedBefore (2 * bits.length + 1) inputSuffix,
   outputTape := afterRead bits outputSuffix, halted := true}

theorem decode_run (bits : List Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (decode bits.length)
      (NativeBitChoice.start (preload (FiniteBitEncoding.delimit bits) inputSuffix)
        (NativeBitGenerator.blankBlock bits.length outputSuffix)) (11 * bits.length + 6) =
      PMF.pure (decodeFinish bits inputSuffix outputSuffix) := by
  unfold decode
  rw [show 11 * bits.length + 6 = (11 * bits.length + 1) + 4 + 1 by omega,
    NativeUniformSequence.run _ _ _ _ (copies_stops bits.length) terminal_stops,
    copies_run, PMF.pure_bind]
  change (evalConfigWithin terminal
    (NativeBitChoice.start (erasedBefore (2 * bits.length) (preload [false] inputSuffix))
      (afterRead bits outputSuffix)) 4).map _ = _
  rw [← preload_erasedBefore, terminal_run, PMF.pure_map]
  have he : erasedBefore 1 (erasedBefore (2 * bits.length) inputSuffix) =
      erasedBefore (2 * bits.length + 1) inputSuffix := by
    rw [erasedBefore_add, Nat.add_comm 1]
  apply congrArg PMF.pure
  simp [decodeFinish, he, copies_length, terminal]

def code (n : ℕ) : Program := (decode n).followedBy (NativeFixedWordRewind.outputCode n)

theorem stops (n : ℕ) : StopsEverywhere (code n) (14 * n + 8) := by
  have h := NativeUniformSequence.stops (decode n) (NativeFixedWordRewind.outputCode n)
    (11 * n + 6) (3 * n + 1) (decode_stops n) (NativeFixedWordRewind.output_stops n)
  have hTime : (11 * n + 6) + (3 * n + 1) + 1 = 14 * n + 8 := by omega
  simpa only [code, hTime] using h

def finish (bits : List Bool) (inputSuffix outputSuffix : Tape) : Configuration :=
  {pc := 20 * bits.length + 12, inputTape := erasedBefore (2 * bits.length + 1) inputSuffix,
   outputTape := preload bits outputSuffix, halted := true}

theorem code_length (n : ℕ) : (code n).length = 20 * n + 13 := by
  simp [code, decode, NativeUniformSequence.code_length, copies_length,
    NativeFixedWordRewind.output_length, terminal]
  omega

theorem run (bits : List Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (code bits.length)
      (NativeBitChoice.start (preload (FiniteBitEncoding.delimit bits) inputSuffix)
        (NativeBitGenerator.blankBlock bits.length outputSuffix)) (14 * bits.length + 8) =
      PMF.pure (finish bits inputSuffix outputSuffix) := by
  unfold code
  rw [show 14 * bits.length + 8 = (11 * bits.length + 6) + (3 * bits.length + 1) + 1 by omega,
    NativeUniformSequence.run _ _ _ _ (decode_stops bits.length) (NativeFixedWordRewind.output_stops bits.length),
    decode_run, PMF.pure_bind]
  change (evalConfigWithin (NativeFixedWordRewind.outputCode bits.length)
    (NativeBitChoice.start (erasedBefore (2 * bits.length + 1) inputSuffix) (afterRead bits outputSuffix))
    (3 * bits.length + 1)).map _ = _
  rw [NativeFixedWordRewind.output_run, PMF.pure_map]
  apply congrArg PMF.pure
  simp [finish, decode, NativeUniformSequence.code_length, copies_length,
    NativeFixedWordRewind.output_length, terminal]
  omega

end Machine.NativeFlaggedRequestPreparation
