import Foundation.Machine.SubroutineSimulation
import Foundation.Machine.Execution
import Foundation.Machine.Compiler

namespace Machine.Examples

/-- The first instruction calls the embedded one-instruction source program;
after its rewritten halt returns, the final instruction halts the wrapper. -/
def tinySubroutineWrapper : Program :=
  Program.withSubroutine [.jump 1] [.halt] [.halt] 3

example : tinySubroutineWrapper =
    [.jump 1, .jump 3, .jump 3, .halt] := rfl

example : HaltsWith tinySubroutineWrapper [] [] 3 := by
  refine ⟨{ pc := 3, halted := true }, ?_, rfl, rfl⟩
  have h₀ : Step tinySubroutineWrapper (Configuration.initial [])
      { pc := 1 } := by decide
  have h₁ : Step tinySubroutineWrapper ({ pc := 1 } : Configuration)
      { pc := 3 } := by decide
  have h₂ : Step tinySubroutineWrapper ({ pc := 3 } : Configuration)
      { pc := 3, halted := true } := by decide
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.zero _) h₀) h₁) h₂

/-- The compiler inserts the same finite source code twice, with separate
return addresses. This example checks the layout and the actual steps. -/
def tinyTwoCallCompiler : ProgramCompiler :=
  .twoCalls [.jump 1] [.jump 4] [.halt]

example : tinyTwoCallCompiler.run [.halt] =
    [.jump 1, .jump 3, .jump 3, .jump 4,
      .jump 6, .jump 6, .halt] := rfl

example : tinyTwoCallCompiler.runCode (Program.encode [.halt]) =
    some (Program.encode (tinyTwoCallCompiler.run [.halt])) := by simp

example : HaltsWith (tinyTwoCallCompiler.run [.halt]) [] [] 5 := by
  refine ⟨{ pc := 6, halted := true }, ?_, rfl, rfl⟩
  let wrapper := tinyTwoCallCompiler.run [.halt]
  have hSource : RunsInside [.halt]
      (Configuration.initial []) (Configuration.initial []) 0 :=
    RunsInside.zero _
  have hSourceHalt : Step [.halt] (Configuration.initial [])
      { halted := true } := by decide
  have hPrefix : RunsFor wrapper (Configuration.initial [])
      { pc := 1 } 1 :=
    RunsFor.succ (RunsFor.zero _) (by decide)
  have hFirst : RunsFor wrapper
      ({ pc := 1 } : Configuration) { pc := 3 } 1 := by
    simpa [wrapper, tinyTwoCallCompiler, Configuration.rebasePc,
      Configuration.resumeAt, Configuration.initial, Tape.ofBits] using
      Program.withTwoSubroutines_first_run_halt
        [.jump 1] [.jump 4] [.halt] [.halt]
        hSource (by decide) (by decide) hSourceHalt
  have hMiddle : RunsFor wrapper
      ({ pc := 3 } : Configuration) { pc := 4 } 1 :=
    RunsFor.succ (RunsFor.zero _) (by decide)
  have hSecond : RunsFor wrapper
      ({ pc := 4 } : Configuration) { pc := 6 } 1 := by
    simpa [wrapper, tinyTwoCallCompiler, Configuration.rebasePc,
      Configuration.resumeAt, Configuration.initial, Tape.ofBits] using
      Program.withTwoSubroutines_second_run_halt
        [.jump 1] [.jump 4] [.halt] [.halt]
        hSource (by decide) (by decide) hSourceHalt
  have hPost : RunsFor wrapper
      ({ pc := 6 } : Configuration) { pc := 6, halted := true } 1 :=
    RunsFor.succ (RunsFor.zero _) (by decide)
  simpa [wrapper] using
    ((((hPrefix.trans hFirst).trans hMiddle).trans hSecond).trans hPost)

/-- Both random-bit outcomes of the source remain possible inside the
rebased code block. -/
example (bit : Bool) :
    Step (Program.withSubroutine [.jump 1]
      [.randomBit .output, .halt] [.halt] 4)
      ((Configuration.initial []).rebasePc 1)
      (({ pc := 1, outputTape := { current := some bit } } : Configuration).rebasePc 1) := by
  refine Program.step_withSubroutine_sequential [.jump 1]
    [.randomBit .output, .halt] [.halt] 4
    (c := Configuration.initial [])
    (d := { pc := 1, outputTape := { current := some bit } }) ?_ ?_ ?_
  · decide
  · simp [Instruction.IsSequential, Configuration.initial]
  · cases bit <;> decide

/-- An entire randomized source invocation, including its final halt, runs
inside the wrapper with the same two machine transitions. Its output tape
retains the bit chosen by the random instruction. -/
example (bit : Bool) :
    RunsFor (Program.withSubroutine [.jump 1]
      [.randomBit .output, .halt] [.halt] 4)
      ((Configuration.initial []).rebasePc 1)
      (({ pc := 1, outputTape := { current := some bit }, halted := true } :
          Configuration).resumeAt 4) 2 := by
  let middle : Configuration :=
    { pc := 1, outputTape := { current := some bit } }
  have hRandom : Step [.randomBit .output, .halt]
      (Configuration.initial []) middle := by
    cases bit <;> decide
  have hInside : RunsInside [.randomBit .output, .halt]
      (Configuration.initial []) middle 1 := by
    exact RunsInside.succ (RunsInside.zero _) (by decide)
      (by simp [middle]) (by rfl) hRandom
  have hHalt : Step [.randomBit .output, .halt] middle
      { pc := 1, outputTape := { current := some bit }, halted := true } := by
    cases bit <;> decide
  exact hInside.withSubroutine_halt [.jump 1]
    [.randomBit .output, .halt] [.halt] 4
    (by simp [middle]) (by simp [middle]) hHalt

example (bit : Bool) :
    (({ pc := 1, outputTape := { current := some bit }, halted := true } :
        Configuration).resumeAt 4).outputBits = [bit] := by
  rfl

/-- Falling off immediately after a random instruction is also preserved:
the appended wrapper instruction returns in place of the source's halt. -/
example (bit : Bool) :
    RunsFor (Program.withSubroutine [.jump 1]
      [.randomBit .output] [.halt] 3)
      ((Configuration.initial []).rebasePc 1)
      (({ pc := 1, outputTape := { current := some bit }, halted := true } :
          Configuration).resumeAt 3) 2 := by
  let outside : Configuration :=
    { pc := 1, outputTape := { current := some bit } }
  have hRandom : Step [.randomBit .output]
      (Configuration.initial []) outside := by
    cases bit <;> decide
  have hHalt : Step [.randomBit .output] outside
      { pc := 1, outputTape := { current := some bit }, halted := true } := by
    cases bit <;> decide
  exact (RunsInside.zero (Configuration.initial [])).withSubroutine_sequential_fallthrough
    [.jump 1] [.randomBit .output] [.halt] 3
    (by decide)
    (by simp [Instruction.IsSequential])
    hRandom
    (by simp [outside])
    hHalt

/-- A source jump outside its code halts only on its next source step. The
embedded jump returns immediately, so the wrapper uses one fewer step. -/
example :
    RunsFor (Program.withSubroutine [.jump 1] [.jump 5] [.halt] 3)
      ((Configuration.initial []).rebasePc 1)
      (({ pc := 5, halted := true } : Configuration).resumeAt 3) 1 := by
  let outside : Configuration := { pc := 5 }
  have hJump : Step [.jump 5] (Configuration.initial []) outside := by
    decide
  have hHalt : Step [.jump 5] outside
      { pc := 5, halted := true } := by
    decide
  exact (RunsInside.zero (Configuration.initial [])).withSubroutine_jump_exit
    [.jump 1] [.jump 5] [.halt] 3 5
    (by decide) (by rfl) hJump (by simp [outside])
    (by rfl) hHalt

example :
    RunsFor (Program.withSubroutine [.jump 1]
      [.branch .input 5 5 5] [.halt] 3)
      ((Configuration.initial []).rebasePc 1)
      (({ pc := 5, halted := true } : Configuration).resumeAt 3) 1 := by
  let outside : Configuration := { pc := 5 }
  have hBranch : Step [.branch .input 5 5 5]
      (Configuration.initial []) outside := by
    decide
  have hHalt : Step [.branch .input 5 5 5] outside
      { pc := 5, halted := true } := by
    decide
  exact (RunsInside.zero (Configuration.initial [])).withSubroutine_branch_exit
    [.jump 1] [.branch .input 5 5 5] [.halt] 3
    .input 5 5 5 (by decide) (by rfl) hBranch
    (by simp [outside]) (by rfl) hHalt

/-- Standalone correctness from `Configuration.initial` cannot by itself be
used as correctness of a call inside a wrapper. Even a source consisting only
of `halt` inherits a pre-existing output bit from its caller. A simulator
must prepare and later inspect the tapes explicitly. -/
example : HaltsWith [.halt] [] [] 1 := by
  refine ⟨{ halted := true }, ?_, rfl, rfl⟩
  exact RunsFor.succ (RunsFor.zero _) (by decide)

example :
    RunsFor (Program.withSubroutine [.jump 1] [.halt] [.halt] 3)
      (({ outputTape := { current := some true } } : Configuration).rebasePc 1)
      (({ outputTape := { current := some true }, halted := true } :
          Configuration).resumeAt 3) 1 ∧
    (({ outputTape := { current := some true }, halted := true } :
          Configuration).resumeAt 3).outputBits = [true] := by
  constructor
  · exact (RunsInside.zero
      ({ outputTape := { current := some true } } : Configuration)).withSubroutine_halt
        [.jump 1] [.halt] [.halt] 3
        (by decide) (by decide) (by decide)
  · rfl

end Machine.Examples
