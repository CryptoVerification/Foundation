import Foundation.Machine.ChooseResponseParser

namespace Foundation.Examples.ChooseResponseParser

/-- The complete native framing and delimiter parser uses one fixed code. -/
example :
    let reply := Machine.canonicalMessageBits [true, false] [false] [true]
    let raw := Machine.encodeSecurityParameter 2 ++
      Machine.frame [true, false] ++ Machine.frame reply
    Machine.evalWithin Machine.ChooseResponseParser.program raw
      (Machine.ChooseResponseParser.budget raw.length) =
        PMF.pure (some [true, false, true, false, true]) := by
  simpa using Machine.ChooseResponseParser.eval_canonical
    2 [true, false] [true, false] [false] [true]

example : Machine.HaltsWithin Machine.ChooseResponseParser.program
    [true, false, true]
    (Machine.ChooseResponseParser.budget 3) :=
  Machine.ChooseResponseParser.haltsWithin [true, false, true]

end Foundation.Examples.ChooseResponseParser
