import Foundation.Machine.BinaryPowerProgramSemantics

namespace Machine.Examples.BinaryPower

/-- The finite machine computes 3^5 modulo 7 from four-bit columns. -/
private def columns : List BinaryModularAddition.Column :=
  [((true, true), true), ((true, false), true),
   ((false, true), true), ((false, false), false)]

example : evalWithin BinaryPowerProgram.program (BinaryModularAddition.interleave columns)
    (BinaryPowerProgram.budget (BinaryModularAddition.interleave columns).length) =
    PMF.pure (some [true, false, true, false]) := by
  simpa [columns, Binary.value, Binary.encode] using
    BinaryPowerProgramSemantics.eval_power_encoded columns (by decide)
      (by decide) (by decide) (by decide)

/-- Raw malformed inputs also terminate; the numerical identity above is
claimed only under its explicit modulus and workspace hypotheses. -/
example (input : List Bool) : HaltsWithin BinaryPowerProgram.program input
    (BinaryPowerProgram.budget input.length) := BinaryPowerProgram.haltsWithin input

example : PolynomialTime BinaryPowerProgram.program := BinaryPowerProgram.polynomialTime

end Machine.Examples.BinaryPower
