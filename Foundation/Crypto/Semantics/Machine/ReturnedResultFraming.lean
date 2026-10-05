import Foundation.Crypto.Semantics.Machine.ContextualFrame
import Foundation.Crypto.Semantics.Machine.OppositeCall

namespace Machine

/-- Rewind a returned raw result and frame it after a fresh separator on
the other tape. Every scan, copy, and separator crossing is a native step.
The retained source scratch and caller prefixes are not discarded. -/
def frameReturnedResult : Program :=
  rewindBitstring.asSubroutine 0 5 ++ [.moveRight .output] ++
    writeFrame.asSubroutine 6 31 ++ [.halt]

def frameReturnedResultStart (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  { inputTape := { left := bits.reverse.map some ++ none :: savedInput, right := tail },
    outputTape := { left := beforeOutput, right := List.replicate blanks none } }

def frameReturnedResultFinish (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  { pc := 31,
    inputTape := { left := bits.reverse.map some ++ none :: savedInput, right := tail },
    outputTape := {
      left := (frame bits).reverse.map some ++ none :: beforeOutput
      right := List.replicate (blanks - 1 - (2*bits.length + 1)) none },
    halted := true }

def frameReturnedResultSteps (bits : List Bool) : Nat :=
  (2*bits.length + 4) + 1 + writeFrameSteps bits + 1

theorem frameReturnedResult_runs (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    RunsFor frameReturnedResult (frameReturnedResultStart savedInput beforeOutput tail bits blanks)
      (frameReturnedResultFinish savedInput beforeOutput tail bits blanks) (frameReturnedResultSteps bits) := by
  let output : Tape := { left := beforeOutput, right := List.replicate blanks none }
  have hRewind := (rewindScratch_runs_from savedInput bits none tail output).withSubroutine_halted_of_closed
    [] rewindBitstring ([.moveRight .output] ++ writeFrame.asSubroutine 6 31 ++ [.halt]) 5
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  let rewound : Configuration :=
    { pc := 5, inputTape := { ({ right := bits.map some ++ none :: tail } : Tape).moveRight with
        left := none :: savedInput }, outputTape := output }
  have hRewindFinish : ({
      pc := 3,
      inputTape := ({ left := savedInput, right := bits.map some ++ none :: tail } : Tape).moveRight,
      outputTape := output, halted := true } : Configuration).resumeAt 5 = rewound := by
    cases bits <;> simp [rewound, Configuration.resumeAt, Tape.moveRight]
  rw [hRewindFinish] at hRewind
  change RunsFor frameReturnedResult (frameReturnedResultStart savedInput beforeOutput tail bits blanks)
    rewound (2*bits.length + 4) at hRewind
  let frameStart := writeFrameContextPaddedStart savedInput (none :: beforeOutput) tail bits (blanks-1)
  have hMove : Step frameReturnedResult rewound (frameStart.rebasePc 6) := by
    cases blanks <;> simp [Step, successors, next, frameReturnedResult, rewound, frameStart,
      writeFrameContextPaddedStart_layout, output, Program.asSubroutine, Instruction.asSubroutine,
      rewindBitstring, Configuration.rebasePc, Instruction.next, Configuration.updateTape,
      Configuration.advance, Tape.moveRight, List.replicate_succ]
  have hFrame := (writeFrameContextPadded_runs savedInput (none :: beforeOutput) tail bits (blanks-1)).withSubroutine_halted_of_closed
    (rewindBitstring.asSubroutine 0 5 ++ [.moveRight .output]) writeFrame [.halt] 31
    (by change 0 < 24; decide) rfl rfl writeFrame_control_closed
  change RunsFor frameReturnedResult (frameStart.rebasePc 6)
    ((frameReturnedResultFinish savedInput beforeOutput tail bits blanks).resumeAt 31)
    (writeFrameSteps bits) at hFrame
  have hHalt : Step frameReturnedResult
      ((frameReturnedResultFinish savedInput beforeOutput tail bits blanks).resumeAt 31)
      (frameReturnedResultFinish savedInput beforeOutput tail bits blanks) := by
    simp [Step, successors, next, frameReturnedResult, frameReturnedResultFinish,
      writeFrame, writeFrameHeader, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ ((RunsFor.succ hRewind hMove).trans hFrame) hHalt

theorem frameReturnedResult_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ frameReturnedResult := by
  simp [frameReturnedResult, writeFrame, writeFrameHeader, rewindBitstring, copyBitstring,
    Program.asSubroutine, Instruction.asSubroutine]

theorem frameReturnedResult_eval (savedInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    evalConfigWithin frameReturnedResult (frameReturnedResultStart savedInput beforeOutput tail bits blanks)
      (frameReturnedResultSteps bits) =
      PMF.pure (frameReturnedResultFinish savedInput beforeOutput tail bits blanks) :=
  (frameReturnedResult_runs _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit frameReturnedResult_no_randomBit

theorem frameReturnedResult_steps_le (bits : List Bool) :
    frameReturnedResultSteps bits ≤ 15*bits.length + 17 := by
  have h := writeFrameSteps_le bits
  simp only [frameReturnedResultSteps]
  omega

/-- The opposite-tape guarded call leaves precisely this starting layout.
The second copy of the source output is behind the new frame's separator.
All virtual source cells, request cells, and caller data remain represented. -/
theorem rawResultFrom_frameReturnedResultStart (source : Program) (input : List Bool)
    (beforeInput savedOutput : List (Option Bool)) (c : Configuration) :
    ((GuardedCompiler.rawResultFrom source input beforeInput (none :: savedOutput) c).swapTapes).resumeAt 0 =
      frameReturnedResultStart savedOutput
        (c.outputBits.reverse.map some ++ GuardedCompiler.scratchPrefix
          (input.reverse.map some ++ beforeInput) c.inputTape)
        (List.replicate (2*c.outputTape.cells + 2 - c.outputBits.length) none) c.outputBits 0 := by
  rfl

/-- Execute framing on the full configuration actually returned by the
guarded arithmetic call; no canonical result is loaded into a new tape. -/
theorem frameReturnedResult_rawResult_eval (source : Program) (input : List Bool)
    (beforeInput savedOutput : List (Option Bool)) (c : Configuration) :
    evalConfigWithin frameReturnedResult
      (((GuardedCompiler.rawResultFrom source input beforeInput (none :: savedOutput) c).swapTapes).resumeAt 0)
      (frameReturnedResultSteps c.outputBits) =
      PMF.pure (frameReturnedResultFinish savedOutput
        (c.outputBits.reverse.map some ++ GuardedCompiler.scratchPrefix
          (input.reverse.map some ++ beforeInput) c.inputTape)
        (List.replicate (2*c.outputTape.cells + 2 - c.outputBits.length) none) c.outputBits 0) := by
  rw [rawResultFrom_frameReturnedResultStart]
  exact frameReturnedResult_eval _ _ _ _ _

set_option maxHeartbeats 600000 in
theorem frameReturnedResult_control_closed (c d : Configuration)
    (hPc : c.pc < frameReturnedResult.length) (step : Step frameReturnedResult c d)
    (_hRunning : d.halted = false) : d.pc < frameReturnedResult.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 32 at hPc
  change d.pc < 32
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, frameReturnedResult,
    writeFrame, writeFrameHeader, rewindBitstring, copyBitstring,
    Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

end Machine
