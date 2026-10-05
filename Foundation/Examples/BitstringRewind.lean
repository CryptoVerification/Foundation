import Foundation.Crypto.Semantics.Machine.BitstringCopy
import Foundation.Crypto.Semantics.Machine.BitstringRewind

namespace Machine.Examples

example : rewindBitstringFinish [true, false, true] {} =
    { pc := 3,
      inputTape := {
        left := [none]
        current := some true
        right := [some false, some true, none] },
      halted := true } := rfl

example (output : Tape) :
    RunsFor rewindBitstring (rewindBitstringStart [true, false, true] output)
      (rewindBitstringFinish [true, false, true] output) 10 :=
  rewindBitstring_runs _ _

example (bits : List Bool) (output : Tape) :
    (rewindBitstringFinish bits output).outputTape = output :=
  rewindBitstringFinish_output _ _

/-- Actual finite code: copy the input, return into the rewind routine, then
halt. No intermediate tape is reset by the semantics. The copied output is
kept, while the input head is restored to its first bit. -/
def copyAndRewind : Program :=
  Program.withSubroutine [] copyBitstring
    (rewindBitstring.asSubroutine 9 14 ++ [.halt]) 9

private theorem copyAndRewind_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ copyAndRewind := by
  simp [copyAndRewind, copyBitstring, rewindBitstring,
    Program.withSubroutine, Program.asSubroutine, Instruction.asSubroutine,
    subroutineAddress]

theorem copyAndRewind_runs (input : List Bool) :
    ∃ used, used ≤ 8 * input.length + 7 ∧
      RunsFor copyAndRewind (Configuration.initial input)
        ({ rewindBitstringFinish input { left := input.reverse.map some }
          with pc := 14 } : Configuration) used := by
  obtain ⟨copied, hCopied, hCopy⟩ := (copyBitstring_runs input).withSubroutine_halted
    [] copyBitstring (rewindBitstring.asSubroutine 9 14 ++ [.halt])
    9 (by simp [Configuration.initial]) rfl rfl
  obtain ⟨rewound, hRewound, hRewind⟩ :=
    (rewindBitstring_runs input { left := input.reverse.map some }).withSubroutine_halted
      (copyBitstring.asSubroutine 0 9) rewindBitstring [.halt] 14
      (by simp [rewindBitstringStart]) rfl rfl
  have hWrapper : Program.withSubroutine (copyBitstring.asSubroutine 0 9)
      rewindBitstring [.halt] 14 = copyAndRewind := by
    simp [Program.withSubroutine, copyAndRewind, Program.asSubroutine,
      copyBitstring, List.append_assoc]
  rw [hWrapper] at hRewind
  have hMiddle : (copyBitstringFinish input).resumeAt 9 =
      (rewindBitstringStart input { left := input.reverse.map some }).rebasePc
        (copyBitstring.asSubroutine 0 9).length := by
    simp [copyBitstringFinish, rewindBitstringStart, Configuration.resumeAt,
      Configuration.rebasePc, Program.asSubroutine, copyBitstring]
  have hStart : (Configuration.initial input).rebasePc ([] : Program).length =
      Configuration.initial input := rfl
  rw [hStart, hMiddle] at hCopy
  change RunsFor copyAndRewind _ _ copied at hCopy
  have hHalt : Step copyAndRewind
      ((rewindBitstringFinish input { left := input.reverse.map some }).resumeAt 14)
      ({ rewindBitstringFinish input { left := input.reverse.map some }
        with pc := 14 } : Configuration) := by
    simp [Step, successors, next, copyAndRewind, Program.withSubroutine,
      Program.asSubroutine, copyBitstring, rewindBitstring, Instruction.asSubroutine,
      Instruction.next, rewindBitstringFinish, Configuration.resumeAt]
  refine ⟨copied + rewound + 1, ?_, RunsFor.succ (hCopy.trans hRewind) hHalt⟩
  have hCopyBound := copyBitstringSteps_le input
  omega

theorem copyAndRewind_haltsWith (input : List Bool) :
    ∃ used, used ≤ 8 * input.length + 7 ∧
      HaltsWith copyAndRewind input input used := by
  obtain ⟨used, hBound, run⟩ := copyAndRewind_runs input
  refine ⟨used, hBound, _, run, rfl, ?_⟩
  simp [rewindBitstringFinish, Configuration.outputBits, Tape.bits]

theorem copyAndRewind_haltsWithin (input : List Bool) :
    HaltsWithin copyAndRewind input (8 * input.length + 7) := by
  obtain ⟨used, hBound, hHalt⟩ := copyAndRewind_haltsWith input
  exact (hHalt.haltsWithin_of_no_randomBit copyAndRewind_no_randomBit).mono hBound

theorem copyAndRewind_eval (input : List Bool) :
    evalWithin copyAndRewind input (8 * input.length + 7) =
      PMF.pure (some input) := by
  obtain ⟨used, _, hHalt⟩ := copyAndRewind_haltsWith input
  have hUsed := hHalt.haltsWithin_of_no_randomBit copyAndRewind_no_randomBit
  rw [evalWithin_eq_of_haltsWithin copyAndRewind input
    (8 * input.length + 7) used (copyAndRewind_haltsWithin input) hUsed]
  exact hHalt.evalWithin_eq_pure_of_no_randomBit copyAndRewind_no_randomBit

example : PolynomialTime copyAndRewind := by
  refine ⟨fun m => 8 * m + 7, ?_, copyAndRewind_haltsWithin⟩
  exact ((PolynomiallyBounded.const 8).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 7)

example (input : List Bool) :
    ({ rewindBitstringFinish input { left := input.reverse.map some }
      with pc := 14 } : Configuration).inputTape.Equivalent (Tape.ofBits input) :=
  rewindBitstringFinish_input_equivalent input { left := input.reverse.map some }

example : evalWithin copyAndRewind [true, false, true] 31 =
    PMF.pure (some [true, false, true]) := copyAndRewind_eval _

end Machine.Examples
