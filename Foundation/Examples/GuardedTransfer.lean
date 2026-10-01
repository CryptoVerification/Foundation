import Foundation.Machine.GuardedTransfer

namespace Machine.Examples

open GuardedCompiler

example : transferPackedInput.length = 28 := rfl

example : RunsFor transferPackedInput
    (transferPackedInputStart [] [] [true, false, true])
    (transferPackedInputFinish [] [] [true, false, true]) 43 :=
  transferPackedInput_runs [] [] [true, false, true]

/-- Exact configuration distributions cover the whole routine, not just
its output or a selected forward trace. Saved caller prefixes are arbitrary. -/
example (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    evalConfigWithin transferPackedInput (transferPackedInputStart beforeInput beforeOutput input)
      (11 * input.length + 10) =
      PMF.pure (transferPackedInputFinish beforeInput beforeOutput input) :=
  transferPackedInput_eval beforeInput beforeOutput input

example : (transferPackedInputFinish [] [] [true, false, true]).inputTape =
    encodeTape [] { left := [some true, some false, some true] } := rfl

example : (transferPackedInputFinish [] [] [true, false, true]).outputTape =
    encodeTape [] { left := [none, none, none] } := rfl

example : prepareTapes.length = 86 := rfl

example : RunsFor prepareTapes (Configuration.initial [true, false, true])
    (prepareTapesFinish [] [] [true, false, true]) 135 :=
  prepareTapes_runs [] [] [true, false, true]

example : RunsFor prepareTapes (Configuration.initial [])
    (prepareTapesFinish [] [] []) 42 := prepareTapes_runs [] [] []

example : (prepareTapesFinish [] [] [true, false, true]).inputTape =
    encodeTape [some true, some false, some true]
      { current := some true, right := [some false, some true, none] } := rfl

example : (prepareTapesFinish [] [] [true, false, true]).outputTape =
    encodeTape [] { right := [none, none, none] } := rfl

example : PolynomialTime prepareTapes := prepareTapes_polynomialTime

example (input : List Bool) : (preparedSource input).Equivalent (Configuration.initial input) :=
  preparedSource_equivalent_initial input

example (source : Program) (input : List Bool) (steps : Nat)
    (halts : HaltsWithin source input steps) :
    ∀ final, PaddedRunsFor source (preparedSource input) final steps → final.halted = true :=
  preparedSource_all_branches_halted source input steps halts

example (source : Program) (input : List Bool) (steps : Nat) :
    (evalConfigWithin source (preparedSource input) steps).map
        (fun c => if c.halted then some c.outputBits else none) =
      evalWithin source input steps := preparedSource_evalOutput source input steps

/-- Surrounding random instructions do not become an assumption that the
whole caller is deterministic. Initialization retains the full tape contract. -/
example (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    evalConfigWithin
      (Program.withSubroutine [.randomBit .output] prepareTapes [.halt] 88)
      ((packInputStart beforeInput beforeOutput input).rebasePc 1) (31 * input.length + 42) =
      PMF.pure ((prepareTapesFinish beforeInput beforeOutput input).resumeAt 88) :=
  prepareTapes_withSubroutine_eval [.randomBit .output] [.halt] 88 beforeInput beforeOutput input

end Machine.Examples
