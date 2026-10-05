import Foundation.Crypto.Semantics.Machine.GuardedRewind

namespace Machine.Examples

open GuardedCompiler

example : (rewindRegion .output).length = 10 := rfl

example : rewindRegionSteps [some false, none, some true] = 20 := rfl

/-- A logical blank inside the region is crossed rather than confused with
the `01` boundary. Saved caller data and the other tape are retained. -/
example (before : List (Option Bool)) (other : Tape) :
    evalConfigWithin (rewindRegion .output)
      (rewindRegionStart .output before
        { left := [some false, none, some true], current := some false } other)
      20 = PMF.pure (rewindRegionFinish .output before
        { left := [some false, none, some true], current := some false } other) :=
  rewindRegion_eval .output before _ other

example : packAndRewind.length = 35 := rfl

example : RunsFor packAndRewind (Configuration.initial [true, false, true])
    (packAndRewindFinish [] [] [true, false, true]) 48 :=
  packAndRewind_runs [] [] [true, false, true]

example : packedLogicalInput [true, false, true] =
    ({ current := some true, right := [some false, some true, none] } : Tape) := rfl

example : packedLogicalInput [] = ({} : Tape) := rfl

example (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    evalConfigWithin packAndRewind (packInputStart beforeInput beforeOutput input)
      (10 * input.length + 18) = PMF.pure (packAndRewindFinish beforeInput beforeOutput input) :=
  packAndRewind_eval beforeInput beforeOutput input

example : HaltsWithin packAndRewind [] 18 := packAndRewind_haltsWithin []

example : PolynomialTime packAndRewind := packAndRewind_polynomialTime

/-- Head positioning can be called inside a caller containing randomness.
The entry and exit configurations explicitly retain the caller tape. -/
example (before : List (Option Bool)) (logical other : Tape) :
    evalConfigWithin
      (Program.withSubroutine [.randomBit .input] (rewindRegion .output) [.halt] 12)
      ((rewindRegionStart .output before logical other).rebasePc 1)
      (rewindRegionSteps logical.left) =
      PMF.pure ((rewindRegionFinish .output before logical other).resumeAt 12) :=
  rewindRegion_withSubroutine_eval [.randomBit .input] [.halt] 12 .output before logical other

end Machine.Examples
