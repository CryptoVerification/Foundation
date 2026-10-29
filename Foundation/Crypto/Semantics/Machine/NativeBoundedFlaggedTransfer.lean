import Foundation.Crypto.Semantics.Machine.NativeKeyPairDecisionExecution
import Foundation.Crypto.Semantics.Machine.Encoding
import Foundation.Crypto.Semantics.Machine.TapeSwap

/-! Fixed-count decoding of a flagged request by native instructions.
Every consumed flag/data cell is erased. Malformed inputs still have a fixed
stopping bound; only well-formed requests satisfy the exact data/frame law. -/
namespace Machine.NativeBoundedFlaggedTransfer
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence

def consBit (bit : Bool) (suffix : Tape) : Tape :=
  {left := suffix.left, current := some bit, right := suffix.current :: suffix.right}

theorem preload_cons (bit : Bool) (bits : List Bool) (suffix : Tape) :
    preload (bit :: bits) suffix = consBit bit (preload bits suffix) := by
  cases bits <;> rfl

theorem preload_append (xs ys : List Bool) (suffix : Tape) :
    preload (xs ++ ys) suffix = preload xs (preload ys suffix) := by
  induction xs with
  | nil => rfl
  | cons bit xs ih => rw [List.cons_append, preload_cons, preload_cons, ih]

def erasedBefore (n : ℕ) (suffix : Tape) : Tape :=
  {suffix with left := List.replicate n none ++ suffix.left}

theorem preload_erasedBefore (bits : List Bool) (n : ℕ) (suffix : Tape) :
    preload bits (erasedBefore n suffix) = erasedBefore n (preload bits suffix) := by
  cases bits <;> rfl

theorem erasedBefore_add (n m : ℕ) (suffix : Tape) :
    erasedBefore n (erasedBefore m suffix) = erasedBefore (n + m) suffix := by
  simp only [erasedBefore, List.replicate_add, List.append_assoc]

def pair : Program :=
  [.branch .input 11 11 1, .erase .input, .moveRight .input,
   .branch .input 11 4 6, .write .output false, .jump 8,
   .write .output true, .jump 8, .erase .input, .moveRight .input,
   .moveRight .output, .halt]

theorem pair_run (bit : Bool) (input output : Tape) :
    evalConfigWithin pair (NativeBitChoice.start (preload [true, bit] input) output) 10 =
      PMF.pure {pc := 11, inputTape := erasedBefore 2 input, outputTape := (output.write (some bit)).moveRight, halted := true} := by
  cases bit <;> simp [pair, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
    Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape,
    preload, Tape.moveRight, Tape.write, erasedBefore]

theorem pair_stops : StopsEverywhere pair 10 := by
  intro input output finish trace
  have h := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  cases hc : input.current with
  | none =>
    simp [pair, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next,
      Configuration.tape, hc] at h
    subst finish
    rfl
  | some flag =>
    cases flag with
    | false =>
      simp [pair, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next,
        Configuration.tape, hc] at h
      subst finish
      rfl
    | true =>
      cases hr : input.right with
      | nil =>
        simp [pair, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next,
          Configuration.tape, Configuration.updateTape, Configuration.advance,
          Tape.moveRight, Tape.write, hc, hr] at h
        subst finish
        rfl
      | cons cell rest =>
        cases cell with
        | none =>
          simp [pair, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next,
            Configuration.tape, Configuration.updateTape, Configuration.advance,
            Tape.moveRight, Tape.write, hc, hr] at h
          subst finish
          rfl
        | some bit =>
          cases bit <;>
            simp [pair, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next,
              Configuration.tape, Configuration.updateTape, Configuration.advance,
              Tape.moveRight, Tape.write, hc, hr] at h <;> subst finish <;> rfl

def copies : ℕ → Program
  | 0 => [.halt]
  | n + 1 => pair.followedBy (copies n)

theorem copies_length (n : ℕ) : (copies n).length = 15 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [copies, NativeUniformSequence.code_length, pair, ih]; omega

theorem copies_stops (n : ℕ) : StopsEverywhere (copies n) (11 * n + 1) := by
  induction n with
  | zero => exact NativeBitGenerator.code_stops 0
  | succ n ih =>
    have h := NativeUniformSequence.stops pair (copies n) 10 (11 * n + 1) pair_stops ih
    have hTime : 10 + (11 * n + 1) + 1 = 11 * (n + 1) + 1 := by omega
    simpa only [copies, hTime] using h

def copyFinish (bits : List Bool) (inputSuffix outputSuffix : Tape) : Configuration :=
  {pc := 15 * bits.length,
   inputTape := erasedBefore (2 * bits.length) (preload [false] inputSuffix),
   outputTape := afterRead bits outputSuffix, halted := true}

theorem copies_run (bits : List Bool) (inputSuffix outputSuffix : Tape) :
    evalConfigWithin (copies bits.length)
      (NativeBitChoice.start (preload (FiniteBitEncoding.delimit bits) inputSuffix)
        (NativeBitGenerator.blankBlock bits.length outputSuffix)) (11 * bits.length + 1) =
      PMF.pure (copyFinish bits inputSuffix outputSuffix) := by
  induction bits generalizing inputSuffix outputSuffix with
  | nil =>
    simp [copies, copyFinish, FiniteBitEncoding.delimit, NativeBitGenerator.blankBlock,
      erasedBefore, afterRead, evalConfigWithin, stepPMF, next, NativeBitChoice.start, Instruction.next]
  | cons bit bits ih =>
    rw [show 11 * (bit :: bits).length + 1 = 10 + (11 * bits.length + 1) + 1 by simp; omega,
      show copies (bit :: bits).length = pair.followedBy (copies bits.length) from rfl,
      NativeUniformSequence.run _ _ _ _ pair_stops (copies_stops bits.length)]
    have hload : preload (FiniteBitEncoding.delimit (bit :: bits)) inputSuffix =
        preload [true, bit] (preload (FiniteBitEncoding.delimit bits) inputSuffix) :=
      (preload_append [true, bit] (FiniteBitEncoding.delimit bits) inputSuffix)
    rw [hload, pair_run, PMF.pure_bind]
    rw [← preload_erasedBefore]
    simp only [List.length_cons]
    rw [NativeBitGenerator.blankBlock_written_move]
    change (evalConfigWithin (copies bits.length)
      (NativeBitChoice.start (preload (FiniteBitEncoding.delimit bits) (erasedBefore 2 inputSuffix))
        (NativeBitGenerator.blankBlock bits.length {outputSuffix with left := some bit :: outputSuffix.left}))
      (11 * bits.length + 1)).map _ = _
    rw [ih, PMF.pure_map]
    have hi : erasedBefore (2 * bits.length) (preload [false] (erasedBefore 2 inputSuffix)) =
        erasedBefore (2 * (bit :: bits).length) (preload [false] inputSuffix) := by
      rw [preload_erasedBefore, erasedBefore_add]
      congr 1
    have ho := afterRead_cons bit bits outputSuffix
    apply congrArg PMF.pure
    simp only [copyFinish, hi, ho, copies_length]
    congr 1
    simp [pair]
    omega

end Machine.NativeBoundedFlaggedTransfer
