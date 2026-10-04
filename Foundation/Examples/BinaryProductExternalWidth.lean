import Foundation.Machine.BinaryProductExternalWidth

namespace Machine.Examples.BinaryProductExternalWidth

/-- Seven fits in three external bits. The native program uses a fourth
working bit and erases it before returning the product. -/
private def columns : List BinaryModularAddition.Column :=
  [((true, true), true), ((true, false), true), ((false, true), true)]

example : evalWithin BinaryProductExternalWidth.program
    (BinaryModularAddition.interleave columns)
    (BinaryProductExternalWidth.budget (BinaryModularAddition.interleave columns).length) =
    PMF.pure (some [true, false, false]) := by
  simpa [columns, Binary.value, Binary.encode] using
    BinaryProductExternalWidth.eval_product columns (by decide) (by decide)

example (input : List Bool) :
    HaltsWithin BinaryProductExternalWidth.program input
      (BinaryProductExternalWidth.budget input.length) :=
  BinaryProductExternalWidth.haltsWithin input

example : PolynomialTime BinaryProductExternalWidth.program :=
  BinaryProductExternalWidth.polynomialTime

end Machine.Examples.BinaryProductExternalWidth
