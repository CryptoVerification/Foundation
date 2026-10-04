import Foundation.Machine.BinaryPowerExternalWidth

namespace Machine.Examples.BinaryPowerExternalWidth

/-- The native code returns exactly three external bits for 2² mod 7. -/
example :
    let raw := BinaryModularAddition.interleave
      (BinaryProductExternalWidth.numberColumns 3 7 2 2)
    evalWithin BinaryPowerExternalWidth.program raw
      (BinaryPowerExternalWidth.budget raw.length) =
      PMF.pure (some [false, false, true]) := by
  simpa [Binary.encode] using
    (BinaryPowerExternalWidth.eval_numbers 3 7 2 2
      (by decide) (by decide) (by decide) (by decide))

example (input : List Bool) :
    HaltsWithin BinaryPowerExternalWidth.program input
      (BinaryPowerExternalWidth.budget input.length) :=
  BinaryPowerExternalWidth.haltsWithin input

example : PolynomialTime BinaryPowerExternalWidth.program :=
  BinaryPowerExternalWidth.polynomialTime

end Machine.Examples.BinaryPowerExternalWidth
