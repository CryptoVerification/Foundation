import Foundation.Crypto.Semantics.Machine.BinaryProductSemantics

namespace Machine.Examples.BinaryProduct

/-- Actual complete native product code, not an evaluation of its arithmetic
reference function: 3 * 5 modulo 7 is 1 in the four-bit workspace. -/
private def columns : List BinaryModularAddition.Column :=
  [((true, true), true), ((true, false), true),
   ((false, true), true), ((false, false), false)]

example : evalWithin BinaryProductProgram.program (BinaryModularAddition.interleave columns)
    (BinaryProductProgram.budget (BinaryModularAddition.interleave columns).length) =
    PMF.pure (some [true, false, false, false]) := by
  simpa [columns, Binary.value, Binary.encode] using
    BinaryProductSemantics.eval_product_encoded columns (by decide) (by decide)

/-- Empty, incomplete, and zero-modulus raw inputs are covered by the same
all-input theorem. This statement makes no arithmetic claim on bad moduli. -/
example (input : List Bool) : HaltsWithin BinaryProductProgram.program input
    (1000000 * (input.length + 1) ^ 4) := BinaryProductProgram.haltsWithin input

example : PolynomialTime BinaryProductProgram.program := BinaryProductProgram.polynomialTime

example : ∃ output : List Bool, output.length = 4 ∧
    evalWithin BinaryProductProgram.program (BinaryModularAddition.interleave columns)
      (BinaryProductProgram.budget (BinaryModularAddition.interleave columns).length) = PMF.pure (some output) :=
  BinaryProductSemantics.complete_output columns

end Machine.Examples.BinaryProduct
