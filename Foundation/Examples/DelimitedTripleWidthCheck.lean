import Foundation.Crypto.Semantics.Machine.DelimitedTripleWidthCheck

namespace Foundation.Examples.DelimitedTripleWidthCheck

/-- Three concatenated two-bit instance fields act as a six-cell counter
for one two-bit delimited element. The actual bits may be mixed. -/
example :
    Machine.RunsFor Machine.DelimitedTripleWidthCheck.program
      (Machine.DelimitedTripleWidthCheck.start [] []
        ([true, false] ++ [false, true] ++ [true, true]) [false, true] [])
      (Machine.DelimitedTripleWidthCheck.finish [] []
        ([true, false] ++ [false, true] ++ [true, true]) [false, true] [])
      23 := by
  apply Machine.DelimitedTripleWidthCheck.runs_matching_length
  decide

example :
    (Machine.evalConfigWithin Machine.DelimitedTripleWidthCheck.program
      (Machine.DelimitedTripleWidthCheck.start [] []
        ([true, false] ++ [false, true] ++ [true, true]) [false, true] [])
      (9 * (2 + 2 + 1) + 6)).map
        (fun c => c.outputTape.current) = PMF.pure (some true) := by
  apply Machine.DelimitedTripleWidthCheck.eval_width_status
  decide

example :
    (Machine.evalConfigWithin Machine.DelimitedTripleWidthCheck.program
      (Machine.DelimitedTripleWidthCheck.start [] []
        ([true, false] ++ [false, true] ++ [true, true]) [false] [])
      (9 * (2 + 1 + 1) + 6)).map
        (fun c => c.outputTape.current) = PMF.pure (some false) := by
  apply Machine.DelimitedTripleWidthCheck.eval_width_status
  decide

example (input output : Machine.Tape) :
    ∃ target used, used ≤ 9 * (input.right.length + 1) + 6 ∧
      Machine.RunsFor Machine.DelimitedTripleWidthCheck.program
        { inputTape := input, outputTape := output } target used ∧
      target.halted = true :=
  Machine.DelimitedTripleWidthCheck.terminates_from_anyTape input output

end Foundation.Examples.DelimitedTripleWidthCheck
