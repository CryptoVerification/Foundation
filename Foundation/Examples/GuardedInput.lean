import Foundation.Machine.GuardedInput

namespace Machine.Examples

open GuardedCompiler

example : packInput.length = 22 := rfl

/-- Three raw bits are copied by 31 actual one-cell transitions. -/
example : RunsFor packInput (Configuration.initial [true, false, true])
    (packInputFinish [] [] [true, false, true]) 31 :=
  packInput_runs [] [] [true, false, true]

example : (packInputFinish [] [] [true, false, true]).outputBits =
    [false, true, true, true, true, false, true, true, false, false] := rfl

example : RunsFor packInput (Configuration.initial []) (packInputFinish [] [] []) 10 :=
  packInput_runs [] [] []

example : (packInputFinish [] [] []).outputBits = [false, true, false, false] := rfl

/-- The caller data beyond each entry head remains in the explicit
postcondition. The output head is at the final logical blank pair. -/
example (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    evalConfigWithin packInput (packInputStart beforeInput beforeOutput input)
      (7 * input.length + 10) = PMF.pure (packInputFinish beforeInput beforeOutput input) :=
  packInput_eval beforeInput beforeOutput input

example (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    (packInputFinish beforeInput beforeOutput input).outputTape =
      encodeTape beforeOutput { left := input.reverse.map some } := rfl

example (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    (packInputFinish beforeInput beforeOutput input).inputTape.left.drop input.length =
      beforeInput := by
  simp [packInputFinish]

example (input : List Bool) : HaltsWithin packInput input (7 * input.length + 10) :=
  packInput_haltsWithin input

example : PolynomialTime packInput := packInput_polynomialTime

/-- A caller containing a random opcode outside the invoked block still
gets the deterministic packed state after exactly 31 transitions. -/
example : evalConfigWithin
    (Program.withSubroutine [.randomBit .output] packInput [.halt] 23)
    ((packInputStart [none, some true] [some false] [true, false, true]).rebasePc 1)
    31 = PMF.pure ((packInputFinish [none, some true] [some false]
      [true, false, true]).resumeAt 23) :=
  packInput_withSubroutine_eval [.randomBit .output] [.halt] 23
    [none, some true] [some false] [true, false, true]

end Machine.Examples
