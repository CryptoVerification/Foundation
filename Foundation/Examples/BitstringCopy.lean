import Foundation.Crypto.Semantics.Machine.BitstringCopy
import Foundation.Crypto.Semantics.Machine.SubroutineRuntime

namespace Machine.Examples

example : copyBitstringSteps [] = 2 := rfl
example : copyBitstringSteps [true, false, true] = 18 := rfl
example : copyBitstringSteps [false, false] = 14 := rfl

example : evalWithin copyBitstring [true, false, true] 20 =
    PMF.pure (some [true, false, true]) :=
  copyBitstring_eval [true, false, true]

/-- A genuine caller invokes the copying routine and then halts. Each copied
bit still requires several actual machine transitions. The input is loaded
and the output tape is blank at the initial configuration. -/
def copyCaller : Program :=
  Program.withSubroutine [.jump 1] copyBitstring [.halt] 10

private theorem copyCaller_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ copyCaller := by
  simp [copyCaller, copyBitstring, Program.withSubroutine,
    Program.asSubroutine, Instruction.asSubroutine, subroutineAddress]

theorem copyCaller_haltsWith (input : List Bool) :
    ∃ steps, steps ≤ 6 * input.length + 4 ∧
      HaltsWith copyCaller input input steps := by
  obtain ⟨returned, used, hUsed, hInvocation, hPc, hActive, hOutput⟩ :=
    (copyBitstring_haltsWith input).withSubroutine_returns
      [.jump 1] copyBitstring [.halt] 10
  have hCall : Step copyCaller (Configuration.initial input)
      ((Configuration.initial input).rebasePc 1) := by
    simp [Step, successors, next, copyCaller, Program.withSubroutine,
      Program.asSubroutine, copyBitstring, Instruction.asSubroutine,
      Instruction.next, Configuration.initial, Configuration.rebasePc]
  have hHalt : Step copyCaller returned { returned with halted := true } := by
    simp [Step, successors, next, copyCaller, Program.withSubroutine,
      Program.asSubroutine, copyBitstring, Instruction.asSubroutine,
      Instruction.next, hPc, hActive]
  refine ⟨1 + used + 1, ?_,
    { returned with halted := true }, ?_, rfl, ?_⟩
  · have hSource := copyBitstringSteps_le input
    omega
  · exact ((RunsFor.succ (RunsFor.zero _) hCall).trans hInvocation).trans
      (RunsFor.succ (RunsFor.zero _) hHalt)
  · exact hOutput

theorem copyCaller_haltsWithin (input : List Bool) :
    HaltsWithin copyCaller input (6 * input.length + 4) := by
  obtain ⟨steps, hLe, hRun⟩ := copyCaller_haltsWith input
  exact (hRun.haltsWithin_of_no_randomBit copyCaller_no_randomBit).mono hLe

theorem copyCaller_eval (input : List Bool) :
    evalWithin copyCaller input (6 * input.length + 4) =
      PMF.pure (some input) := by
  obtain ⟨steps, _, hRun⟩ := copyCaller_haltsWith input
  have hSteps := hRun.haltsWithin_of_no_randomBit copyCaller_no_randomBit
  rw [evalWithin_eq_of_haltsWithin copyCaller input
    (6 * input.length + 4) steps (copyCaller_haltsWithin input) hSteps]
  exact hRun.evalWithin_eq_pure_of_no_randomBit copyCaller_no_randomBit

example : PolynomialTime copyCaller := by
  refine ⟨fun m => 6 * m + 4, ?_, copyCaller_haltsWithin⟩
  exact ((PolynomiallyBounded.const 6).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 4)

example (input : List Bool) : ReturnsWithin copyCaller
    ((Configuration.initial input).rebasePc 1) 10
    (6 * input.length + 2) :=
  (copyBitstring_haltsWithin input).withSubroutine_returnsWithin
    [.jump 1] copyBitstring [.halt] 10

end Machine.Examples
