import Foundation.Crypto.Semantics.Machine.BinaryProductPadded

namespace Machine.Examples.BinaryProductPadded

/-- Seven fits in three external bits, while twice seven needs four work bits.
The code writes the extra zero column, rewinds, and performs the product. -/
private def columns : List BinaryModularAddition.Column :=
  [((true, true), true), ((true, false), true), ((false, true), true)]

example : evalWithin BinaryProductPadded.program
    (BinaryModularAddition.interleave columns)
    (BinaryProductPadded.budget (BinaryModularAddition.interleave columns).length) =
    PMF.pure (some [true, false, false, false]) := by
  simpa [columns, Binary.value, Binary.encode] using
    BinaryProductPadded.eval_product_padded columns (by decide) (by decide)

example (input : List Bool) :
    HaltsWithin BinaryProductPadded.program input
      (BinaryProductPadded.budget input.length) :=
  BinaryProductPadded.haltsWithin input

example : PolynomialTime BinaryProductPadded.program :=
  BinaryProductPadded.polynomialTime

end Machine.Examples.BinaryProductPadded
