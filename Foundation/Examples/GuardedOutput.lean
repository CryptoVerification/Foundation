import Foundation.Crypto.Semantics.Machine.GuardedOutput

namespace Machine.Examples

open GuardedCompiler

example : decodeRegion.length = 21 := rfl
example : extractToScratch.length = 48 := rfl
example : extractOutput.length = 64 := rfl

/-- The head is inside the logical output and its blanks are internal.
Correct extraction cannot merely stop at the first logical blank. -/
private def outputWithHoles : Tape :=
  { left := [some true, none, some false],
    right := [some true, none] }

example : outputWithHoles.bits = [false, true, true] := rfl
example : extractToScratchSteps {} outputWithHoles = 110 := rfl
example : extractOutputSteps {} outputWithHoles = 139 := rfl

example : RunsFor extractOutput (extractToScratchStart [] [] {} outputWithHoles)
    (extractOutputFinish [] [] {} outputWithHoles) 139 :=
  extractOutput_runs [] [] {} outputWithHoles

example : RunsFor extractOutput (extractToScratchStart [] [] {} {})
    (extractOutputFinish [] [] {} {}) 43 := extractOutput_runs [] [] {} {}

example (beforeInput beforeOutput : List (Option Bool)) (input output : Tape) :
    evalConfigWithin extractOutput (extractToScratchStart beforeInput beforeOutput input output)
      (extractOutputSteps input output) = PMF.pure (extractOutputFinish beforeInput beforeOutput input output) :=
  extractOutput_eval beforeInput beforeOutput input output

example : (extractOutputFinish [] [] {} outputWithHoles).outputBits = [false, true, true] :=
  extractOutputFinish_outputBits [] {} outputWithHoles

/-- The common bound charges the represented logical blanks too.
Every random branch is covered, although this subroutine uses no randomness. -/
example (beforeInput beforeOutput : List (Option Bool)) (input output : Tape) (final : Configuration)
    (run : PaddedRunsFor extractOutput (extractToScratchStart beforeInput beforeOutput input output)
      final (28 * (input.cells + output.cells) + 26)) : final.halted = true :=
  extractOutput_all_branches_halted beforeInput beforeOutput input output final run

example (beforeInput : List (Option Bool)) (input output : Tape) :
    (evalConfigWithin extractOutput (extractToScratchStart beforeInput [] input output)
      (28 * (input.cells + output.cells) + 26)).map
        (fun c => if c.halted then some c.outputBits else none) = PMF.pure (some output.bits) :=
  extractOutput_rawOutput_eval beforeInput input output

/-- Full tape-state correctness is retained inside a caller with random
instructions outside the extracted routine. There is no global assumption
that the whole caller contains only deterministic instructions. -/
example (beforeInput beforeOutput : List (Option Bool)) (input output : Tape) :
    evalConfigWithin
      (Program.withSubroutine [.randomBit .output] extractOutput [.randomBit .input, .halt] 66)
      ((extractToScratchStart beforeInput beforeOutput input output).rebasePc 1)
      (extractOutputSteps input output) =
      PMF.pure ((extractOutputFinish beforeInput beforeOutput input output).resumeAt 66) :=
  extractOutput_withSubroutine_eval [.randomBit .output] [.randomBit .input, .halt] 66
    beforeInput beforeOutput input output

example (beforeInput beforeOutput : List (Option Bool)) (input output : Tape) :
    (extractOutputFinish beforeInput beforeOutput input output).inputTape =
        (extractToScratchFinish beforeInput beforeOutput input output).inputTape ∧
      (extractOutputFinish beforeInput beforeOutput input output).outputTape.left.drop
        output.bits.length = beforeOutput :=
  extractOutputFinish_preserves_saved_data beforeInput beforeOutput input output

example (before : List (Option Bool)) (bits : List Bool) (output : Tape) :
    RunsFor rewindBitstring (rewindScratchStart before bits output)
      (rewindScratchFinish before bits output) (2 * bits.length + 4) :=
  rewindScratch_runs before bits output

end Machine.Examples
