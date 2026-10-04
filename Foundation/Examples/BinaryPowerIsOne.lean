import Foundation.Machine.BinaryPowerIsOne

namespace Foundation.Examples.BinaryPowerIsOne

/-- The connected finite code recognizes 2³ mod 7 = 1. -/
example :
    let raw := Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns 4 7 2 3)
    Machine.evalWithin Machine.BinaryPowerIsOne.program raw
      (Machine.BinaryPowerIsOne.budget raw.length) =
        PMF.pure (some [true]) := by
  have h := Machine.BinaryPowerIsOne.eval_numbers 4 7 2 3
    (by omega) (by omega) (by norm_num) (by norm_num)
  simpa [Machine.BinaryIsOneInPlace.accepts,
    Machine.BinaryIsOne.accepts, Machine.Binary.encode] using h

/-- 3³ mod 7 is not one, using the same fixed finite program. -/
example :
    let raw := Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns 4 7 3 3)
    Machine.evalWithin Machine.BinaryPowerIsOne.program raw
      (Machine.BinaryPowerIsOne.budget raw.length) =
        PMF.pure (some [false]) := by
  have h := Machine.BinaryPowerIsOne.eval_numbers 4 7 3 3
    (by omega) (by omega) (by norm_num) (by norm_num)
  simpa [Machine.BinaryIsOneInPlace.accepts,
    Machine.BinaryIsOne.accepts, Machine.Binary.encode] using h

example (raw : List Bool) :
    Machine.HaltsWithin Machine.BinaryPowerIsOne.program raw
      (Machine.BinaryPowerIsOne.budget raw.length) :=
  Machine.BinaryPowerIsOne.haltsWithin raw

end Foundation.Examples.BinaryPowerIsOne
