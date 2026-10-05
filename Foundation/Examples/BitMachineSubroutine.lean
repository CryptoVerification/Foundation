import Foundation.Crypto.Semantics.Machine.SubroutineRuntime
import Foundation.Crypto.Semantics.Machine.SubroutineProbability
import Foundation.Crypto.Semantics.Machine.Execution
import Foundation.Crypto.Semantics.Machine.Compiler
import Foundation.Examples.BitMachineExecution

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

/-- The general trace theorem handles random output followed by an arbitrary
out-of-range jump. The wrapper trace and its resource bound come entirely
from the generic theorem, rather than a hand-written wrapper execution. -/
example (bit : Bool) :
    ∃ returned used, used ≤ 3 ∧
      RunsFor (Program.withSubroutine [.jump 1]
        [.randomBit .output, .jump 99] [.halt] 4)
        ((Configuration.initial []).rebasePc 1) returned used ∧
      returned.pc = 4 ∧ returned.halted = false ∧
      returned.outputBits = [bit] := by
  have hSource : HaltsWith [.randomBit .output, .jump 99] [] [bit] 3 := by
    refine ⟨{ pc := 99, outputTape := { current := some bit }, halted := true },
      ?_, rfl, rfl⟩
    have hRandom : Step [.randomBit .output, .jump 99]
        (Configuration.initial [])
        { pc := 1, outputTape := { current := some bit } } := by
      cases bit <;> decide
    have hJump : Step [.randomBit .output, .jump 99]
        ({ pc := 1, outputTape := { current := some bit } } : Configuration)
        { pc := 99, outputTape := { current := some bit } } := by
      cases bit <;> decide
    have hHalt : Step [.randomBit .output, .jump 99]
        ({ pc := 99, outputTape := { current := some bit } } : Configuration)
        { pc := 99, outputTape := { current := some bit }, halted := true } := by
      cases bit <;> decide
    exact RunsFor.succ (RunsFor.succ (RunsFor.succ
      (RunsFor.zero _) hRandom) hJump) hHalt
  exact hSource.withSubroutine_returns [.jump 1]
    [.randomBit .output, .jump 99] [.halt] 4

/-- The empty source program halts by fall-through. It needs no special
restriction in the general returning-invocation theorem. -/
example (input : List Bool) :
    ∃ returned used, used ≤ 1 ∧
      RunsFor (Program.withSubroutine [.jump 1] [] [.halt] 2)
        ((Configuration.initial input).rebasePc 1) returned used ∧
      returned.pc = 2 ∧ returned.halted = false ∧
      returned.outputBits = [] := by
  have hSource : HaltsWith [] input [] 1 := by
    refine ⟨{ (Configuration.initial input) with halted := true }, ?_, rfl, rfl⟩
    exact RunsFor.succ (RunsFor.zero _) (by
      simp [Step, successors, next, Configuration.initial])
  exact hSource.withSubroutine_returns [.jump 1] [] [.halt] 2

/-- Return bounds cover every random outcome, rather than a chosen successful
source execution. The caller's continuation is deliberately not executed. -/
example : ReturnsWithin
    (Program.withSubroutine [.jump 1] randomOutputBit [.halt] 4)
    ((Configuration.initial []).rebasePc 1) 4 2 :=
  randomOutputBit_haltsWithin.withSubroutine_returnsWithin
    [.jump 1] randomOutputBit [.halt] 4

/-- A random write followed by an out-of-range jump takes three source steps
(including fall-off halt), and its embedded invocation returns within that
bound on both branches. -/
example : ReturnsWithin
    (Program.withSubroutine [.jump 1]
      [.randomBit .output, .jump 99] [.halt] 4)
    ((Configuration.initial []).rebasePc 1) 4 3 := by
  have hSource : HaltsWithin [.randomBit .output, .jump 99] [] 3 := by
    rw [haltsWithin_iff_reachableStates]
    decide
  exact hSource.withSubroutine_returnsWithin [.jump 1]
    [.randomBit .output, .jump 99] [.halt] 4

example (input : List Bool) : ReturnsWithin
    (Program.withSubroutine [.jump 1] [.halt] [.halt] 3)
    ((Configuration.initial input).rebasePc 1) 3 1 :=
  (haltInstruction_haltsWithin input).withSubroutine_returnsWithin
    [.jump 1] [.halt] [.halt] 3

example : ∃ finish used, used ≤ 2 ∧
    RunsFor (Program.withSubroutine [.jump 1] randomOutputBit [.halt] 4)
      ((Configuration.initial []).rebasePc 1) finish used ∧ finish.pc = 4 :=
  randomOutputBit_haltsWithin.withSubroutine_return_actual
    [.jump 1] randomOutputBit [.halt] 4

/-- Both source-code copies retain the universal source runtime bound when
entered with the matching fresh initial tapes. -/
example : ReturnsWithin
    (Program.withTwoSubroutines [.jump 1] [.jump 5] [.halt] randomOutputBit)
    ((Configuration.initial []).rebasePc 1) 4 2 :=
  randomOutputBit_haltsWithin.withTwoSubroutines_first_returnsWithin
    [.jump 1] [.jump 5] [.halt] randomOutputBit

example : ReturnsWithin
    (Program.withTwoSubroutines [.jump 1] [.jump 5] [.halt] randomOutputBit)
    ((Configuration.initial []).rebasePc 5) 8 2 :=
  randomOutputBit_haltsWithin.withTwoSubroutines_second_returnsWithin
    [.jump 1] [.jump 5] [.halt] randomOutputBit

/-- The invocation bound is an upper bound on real transitions after padding
is removed; padding does not create fictitious machine work. -/
example {p : Program} {returnPc bound : Nat} {start finish : Configuration}
    (hBound : ReturnsWithin p start returnPc bound)
    (run : ReturnRunsFor p returnPc start finish bound) :
    ∃ used, used ≤ bound ∧ RunsFor p start finish used ∧
      finish.pc = returnPc := by
  obtain ⟨used, hle, hActual⟩ := run.toRunsFor
  exact ⟨used, hle, hActual, hBound finish run⟩

/-- The invocation evaluator retains both fair outcomes and their exact
probabilities, stopping before the caller's final halt. -/
example : (evalReturnWithin
    (Program.withSubroutine [.jump 1] randomOutputBit [.halt] 4) 4
    ((Configuration.initial []).rebasePc 1) 2).map
      (fun c => if c.pc = 4 then some c.outputBits else none) =
    Foundation.Probability.sampleBit.map (fun b => some [b]) := by
  simpa only [List.length_cons, List.length_nil] using
    (randomOutputBit_haltsWithin.withSubroutine_evalReturn
    [.jump 1] randomOutputBit [.halt] 4
    (by intro pc hpc; simp [randomOutputBit] at hpc ⊢; omega)).trans
      randomOutputBit_eval

/-- No supported random outcome remains inside the source block at the
source's universal stopping bound. -/
example {finish : Configuration}
    (hSupport : finish ∈ (evalReturnWithin
      (Program.withSubroutine [.jump 1] randomOutputBit [.halt] 4) 4
      ((Configuration.initial []).rebasePc 1) 2).support) : finish.pc = 4 :=
  randomOutputBit_haltsWithin.withSubroutine_return_support
    [.jump 1] randomOutputBit [.halt] 4 hSupport

/-- Both invocations use the same finite randomized source code. Their
individual output distributions follow from the generic two-copy theorem,
provided each invocation is entered with matching fresh initial tapes. -/
example : (evalReturnWithin
    (Program.withTwoSubroutines [.jump 1] [.jump 5] [.halt] randomOutputBit) 4
    ((Configuration.initial []).rebasePc 1) 2).map
      (fun c => if c.pc = 4 then some c.outputBits else none) =
    Foundation.Probability.sampleBit.map (fun b => some [b]) := by
  simpa [randomOutputBit] using
    (randomOutputBit_haltsWithin.withTwoSubroutines_first_evalReturn
      [.jump 1] [.jump 5] [.halt] randomOutputBit).trans randomOutputBit_eval

example : (evalReturnWithin
    (Program.withTwoSubroutines [.jump 1] [.jump 5] [.halt] randomOutputBit) 8
    ((Configuration.initial []).rebasePc 5) 2).map
      (fun c => if c.pc = 8 then some c.outputBits else none) =
    Foundation.Probability.sampleBit.map (fun b => some [b]) := by
  simpa [randomOutputBit] using
    (randomOutputBit_haltsWithin.withTwoSubroutines_second_evalReturn
      [.jump 1] [.jump 5] [.halt] randomOutputBit).trans randomOutputBit_eval

/-- An out-of-range exit may shorten the invocation, but does not change its
output distribution. This uses the general theorem, with no source-address
restriction or separate hand-written wrapper probability calculation. -/
example : (evalReturnWithin
    (Program.withSubroutine [.jump 1]
      [.randomBit .output, .jump 99] [.halt] 4) 4
    ((Configuration.initial []).rebasePc 1) 3).map
      (fun c => if c.pc = 4 then some c.outputBits else none) =
    evalWithin [.randomBit .output, .jump 99] [] 3 := by
  have hSource : HaltsWithin [.randomBit .output, .jump 99] [] 3 := by
    rw [haltsWithin_iff_reachableStates]
    decide
  exact hSource.withSubroutine_evalReturn [.jump 1]
    [.randomBit .output, .jump 99] [.halt] 4
    (by intro pc hpc; simp at hpc ⊢; omega)

/-- A return address inside the source block would cause premature stopping.
Here the invocation stops before its random instruction, so the layout
hypothesis in the probability theorem cannot simply be dropped. -/
example : (evalReturnWithin
    (Program.withSubroutine [.jump 1] randomOutputBit [.halt] 1) 1
    ((Configuration.initial []).rebasePc 1) 2).map Configuration.outputBits =
      PMF.pure [] := by
  rw [evalReturnWithin_of_returned _ 1 _ 2 rfl, PMF.pure_map]
  rfl

end Machine.Examples
