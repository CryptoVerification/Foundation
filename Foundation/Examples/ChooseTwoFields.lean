import Foundation.Crypto.Semantics.Machine.ChooseTwoFields

namespace Foundation.Examples.ChooseTwoFields

/-- Two native delimiter scans retain both payloads and both success bits. -/
example :
    let raw := false ::
      (Machine.FiniteBitEncoding.delimit [true, false] ++
        Machine.FiniteBitEncoding.delimit [false] ++ [true])
    Machine.evalWithin Machine.ChooseTwoFields.program raw
      (Machine.ChooseTwoFields.budget raw.length) =
        PMF.pure (some [true, false, true, false, true]) := by
  simpa using Machine.ChooseTwoFields.eval_canonical [true, false] [false] [true]

/-- Wrong-stage and truncated responses are covered by the same native
all-input stopping certificate. -/
example : Machine.HaltsWithin Machine.ChooseTwoFields.program [true, true]
    (Machine.ChooseTwoFields.budget 2) :=
  Machine.ChooseTwoFields.haltsWithin [true, true]

end Foundation.Examples.ChooseTwoFields
