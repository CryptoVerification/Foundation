import Foundation.Crypto.Semantics.Machine.FramedInput

namespace Machine.Examples

example : (skipFrameFinish 2 ([true, false] ++ [false, true])).inputTape =
    { left := [some false, some true, some false, some true, some true],
      current := some false, right := [some true] } := rfl

example : evalConfigWithin skipFrame
    (Configuration.initial (frame [true, false] ++ [false, true])) 25 =
      PMF.pure (skipFrameFinish 2 ([true, false] ++ [false, true])) :=
  skipFrame_eval _ _

example : HaltsWithin skipFrame [true, true, true] 35 := skipFrame_haltsWithin _
example : HaltsWithin skipFrame [true, true, false] 35 := skipFrame_haltsWithin _
example : PolynomialTime skipFrame := skipFrame_polynomialTime

/-- A finite caller advances past a one-bit protocol tag and invokes the
framed-field routine. The old tag is retained on the input tape, and the
scratch output tape is erased by actual instructions before returning. -/
def taggedFrameCaller : Program :=
  Program.withSubroutine [.moveRight .input, .jump 2] skipFrame [.halt] 16

private def taggedFrameSource (input : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits input.tail with left := [input.head?] } }

private theorem after_tag (input : List Bool) :
    (Configuration.initial input).inputTape.moveRight =
      (taggedFrameSource input).inputTape := by
  cases input with
  | nil => rfl
  | cons tag rest => cases rest <;> rfl

private theorem taggedFrameCaller_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ taggedFrameCaller := by
  simp [taggedFrameCaller, skipFrame, Program.withSubroutine,
    Program.asSubroutine, Instruction.asSubroutine, subroutineAddress]

private theorem taggedFrameCaller_of_run (input : List Bool)
    {finish : Configuration} {sourceSteps : Nat}
    (run : RunsFor skipFrame (taggedFrameSource input) finish sourceSteps)
    (hHalted : finish.halted = true) :
    ∃ used, used ≤ sourceSteps + 3 ∧
      RunsFor taggedFrameCaller (Configuration.initial input)
        ({ finish with pc := 16 } : Configuration) used := by
  obtain ⟨invoked, hInvoked, hCall⟩ := run.withSubroutine_halted
    [.moveRight .input, .jump 2] skipFrame [.halt] 16
    (by simp [taggedFrameSource]) rfl hHalted
  let moved : Configuration :=
    { Configuration.initial input with
      pc := 1
      inputTape := (Configuration.initial input).inputTape.moveRight }
  have hMove : Step taggedFrameCaller (Configuration.initial input) moved := by
    simp [Step, successors, next, taggedFrameCaller, Program.withSubroutine,
      Instruction.next, Configuration.initial, moved,
      Configuration.updateTape, Configuration.advance]
  have hEnter : Step taggedFrameCaller moved
      ((taggedFrameSource input).rebasePc 2) := by
    simp [Step, successors, next, taggedFrameCaller, Program.withSubroutine,
      Instruction.next, moved, Configuration.initial, Configuration.rebasePc,
      taggedFrameSource]
    exact (after_tag input).symm
  have hHalt : Step taggedFrameCaller (finish.resumeAt 16)
      ({ finish with pc := 16 } : Configuration) := by
    simp [Step, successors, next, taggedFrameCaller, Program.withSubroutine,
      Program.asSubroutine, skipFrame, Instruction.asSubroutine,
      Instruction.next, Configuration.resumeAt, hHalted]
  refine ⟨2 + invoked + 1, by omega, ?_⟩
  exact RunsFor.succ
    ((RunsFor.succ (RunsFor.succ (RunsFor.zero _) hMove) hEnter).trans hCall) hHalt

/-- The caller also terminates on arbitrary malformed inputs. Its first
head move is charged; the parser then runs from that actual caller state. -/
theorem taggedFrameCaller_terminates (input : List Bool) :
    ∃ finish used, used ≤ 10 * input.length + 8 ∧
      RunsFor taggedFrameCaller (Configuration.initial input) finish used ∧
      finish.halted = true := by
  obtain ⟨sourceFinish, sourceSteps, hSourceBound, sourceRun, hSourceHalted⟩ :=
    skipFrame_terminates_from [input.head?] input.tail
  obtain ⟨used, hUsed, run⟩ := taggedFrameCaller_of_run input sourceRun hSourceHalted
  refine ⟨_, used, ?_, run, ?_⟩
  · have hTail : input.tail.length ≤ input.length := by simp
    omega
  · exact hSourceHalted

theorem taggedFrameCaller_haltsWithin (input : List Bool) :
    HaltsWithin taggedFrameCaller input (10 * input.length + 8) := by
  obtain ⟨finish, used, hBound, run, hHalted⟩ := taggedFrameCaller_terminates input
  have halts : HaltsWith taggedFrameCaller input finish.outputBits used :=
    ⟨finish, run, hHalted, rfl⟩
  exact (halts.haltsWithin_of_no_randomBit taggedFrameCaller_no_randomBit).mono hBound

example : PolynomialTime taggedFrameCaller := by
  refine ⟨fun m => 10 * m + 8, ?_, taggedFrameCaller_haltsWithin⟩
  exact ((PolynomiallyBounded.const 10).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 8)

theorem taggedFrameCaller_runs (tag : Bool) (bits rest : List Bool) :
    ∃ used, used ≤ 10 * bits.length + 8 ∧
      RunsFor taggedFrameCaller (Configuration.initial (tag :: (frame bits ++ rest)))
        ({ skipFrameFinish bits.length (bits ++ rest) [some tag]
          with pc := 16 } : Configuration) used := by
  have hStart : skipFrameStart bits.length (bits ++ rest) [some tag] =
      taggedFrameSource (tag :: (frame bits ++ rest)) := by
    simp [skipFrameStart, taggedFrameSource, frame, List.append_assoc]
  have sourceRun := skipFrame_runs_from [some tag] bits.length (bits ++ rest)
  rw [hStart] at sourceRun
  obtain ⟨used, hUsed, run⟩ := taggedFrameCaller_of_run
    (tag :: (frame bits ++ rest)) sourceRun rfl
  exact ⟨used, by omega, run⟩

example (tag : Bool) (bits rest : List Bool) :
    ({ skipFrameFinish bits.length (bits ++ rest) [some tag]
      with pc := 16 } : Configuration).inputTape =
      { Tape.ofBits rest with
        left := bits.reverse.map some ++
          some false :: (List.replicate bits.length (some true) ++ [some tag]) } :=
  skipFrameFinish_input bits rest [some tag]

example (tag : Bool) (bits rest : List Bool) :
    ({ skipFrameFinish bits.length (bits ++ rest) [some tag]
      with pc := 16 } : Configuration).outputTape.Equivalent ({} : Tape) :=
  skipFrameFinish_output_blank bits.length (bits ++ rest) [some tag]


-- A dirty caller scratch tape is allowed for stopping, even though frame
-- parsing correctness is only claimed for the documented counter layout.
example (input output : Tape) :
    ∃ finish used, used ≤ 20 * (input.cells + output.cells) + 20 ∧
      RunsFor skipFrame ({ inputTape := input, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true :=
  skipFrame_terminates_from_anyTape _ _

-- Internal blanks and old nonblank scratch cells occur in this concrete
-- malformed caller fixture; no fresh tape is substituted before execution.
example :
    ∃ finish used, used ≤ 240 ∧
      RunsFor skipFrame
        ({ inputTape := { left := [some true], current := some true, right := [some true, some false, some true, none] }, outputTape := { left := [some false, some true], current := some false, right := [some true, none] } } : Configuration)
        finish used ∧ finish.halted = true := by
  simpa [Tape.cells] using skipFrame_terminates_from_anyTape
    ({ left := [some true], current := some true, right := [some true, some false, some true, none] } : Tape)
    ({ left := [some false, some true], current := some false, right := [some true, none] } : Tape)

end Machine.Examples
