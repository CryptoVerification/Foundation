import Foundation.Crypto.Semantics.Machine.DelimitedWidthCheck

namespace Foundation.Examples.DelimitedWidthCheck

/-- A two-bit delimited payload consumes exactly two counter cells and leaves
the tail unread. The trace is for actual finite machine instructions. -/
example :
    Machine.RunsFor Machine.DelimitedWidthCheck.program
      (Machine.DelimitedWidthCheck.start [] [] 2 [true, false] [true])
      (Machine.DelimitedWidthCheck.finish [] [] [true, false] [true]) 19 := by
  simpa using Machine.DelimitedWidthCheck.runs_valid [] [] [true, false] [true]

example :
    ∃ finish used, used ≤ 11 ∧
      Machine.RunsFor Machine.DelimitedWidthCheck.program
        (Machine.DelimitedWidthCheck.start [] [] 1 [true, false] []) finish used ∧
      finish.halted = true ∧ finish.outputTape.current = some false := by
  exact Machine.DelimitedWidthCheck.rejects_too_long [] [] 1 [true, false] [] (by decide)

example :
    ∃ finish used, used ≤ 12 ∧
      Machine.RunsFor Machine.DelimitedWidthCheck.program
        (Machine.DelimitedWidthCheck.start [] [] 2 [true] []) finish used ∧
      finish.halted = true ∧ finish.outputTape.current = some false := by
  exact Machine.DelimitedWidthCheck.rejects_too_short [] [] 2 [true] [] (by decide)

example :
    (Machine.evalConfigWithin Machine.DelimitedWidthCheck.program
      (Machine.DelimitedWidthCheck.start [] [] 2 [true, false] [])
      (7 * (2 + [true, false].length + 1) + 6)).map
        (fun c => c.outputTape.current) = PMF.pure (some true) := by
  simpa using Machine.DelimitedWidthCheck.eval_canonical_status
    [] [] 2 [true, false] []

example :
    (Machine.evalConfigWithin Machine.DelimitedWidthCheck.program
      (Machine.DelimitedWidthCheck.start [] [] 1 [true, false] [])
      (7 * (1 + [true, false].length + 1) + 6)).map
        (fun c => c.outputTape.current) = PMF.pure (some false) := by
  simpa using Machine.DelimitedWidthCheck.eval_canonical_status
    [] [] 1 [true, false] []

/-- A copied modulus code works as the width counter even when its bits are
not all false. No numerical interpretation of the modulus is used. -/
example :
    (Machine.evalConfigWithin Machine.DelimitedWidthCheck.program
      (Machine.DelimitedWidthCheck.startCounter [] []
        [true, false, true] [false, true, false] [])
      (7 * (3 + 3 + 1) + 6)).map
        (fun c => c.outputTape.current) = PMF.pure (some true) := by
  simpa using Machine.DelimitedWidthCheck.eval_counter_status
    [] [] [true, false, true] [false, true, false] []

/-- The same code has a bounded stopping trace on malformed finite tapes. -/
example (input output : Machine.Tape) :
    ∃ finish used,
      used ≤ 7 * (input.right.length + 1) + 6 ∧
      Machine.RunsFor Machine.DelimitedWidthCheck.program
        { inputTape := input, outputTape := output } finish used ∧
      finish.halted = true :=
  Machine.DelimitedWidthCheck.terminates_from_anyTape input output

end Foundation.Examples.DelimitedWidthCheck
