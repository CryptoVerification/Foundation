import Foundation.Machine.BinaryAddition
import Foundation.Machine.BinarySubtraction
import Foundation.Machine.BinaryDoubleReduction
import Foundation.Machine.BinaryModularAddition
import Foundation.Machine.BinaryModularProduct

namespace Machine.Examples

private def operands : List (Bool × Bool) := [(true, true), (true, false), (false, true)]

/-- The operands are the three-bit little-endian encodings of 3 and 5. -/
example : Binary.value (operands.map Prod.fst) = 3 ∧
    Binary.value (operands.map Prod.snd) = 5 := by decide

example : evalWithin BinaryComparison.program (BinaryComparison.interleave operands) 18 =
    PMF.pure (some [true]) := by
  simpa [operands, Binary.value] using BinaryComparison.eval_lt operands

example : evalWithin BinaryAddition.program (BinaryComparison.interleave operands) 24 =
    PMF.pure (some [false, false, false, true]) := by
  simpa [operands, BinaryAddition.sumBits, BinaryAddition.lowerBits,
    BinaryAddition.carryOut, BinaryAddition.digit, BinaryAddition.nextCarry] using
    BinaryAddition.eval_interleave operands

example : (evalWithin BinaryAddition.program (BinaryComparison.interleave operands) 24).map
    (Option.map Binary.value) = PMF.pure (some 8) := by
  simpa [operands, Binary.value] using BinaryAddition.eval_sum operands

example : PolynomialTime BinaryComparison.program := BinaryComparison.polynomialTime
example : PolynomialTime BinaryAddition.program := BinaryAddition.polynomialTime

example : HaltsWithin BinaryComparison.program [true] 10 := BinaryComparison.haltsWithin _
example : HaltsWithin BinaryAddition.program [true] 14 := BinaryAddition.haltsWithin _

/-- Fixed-width subtraction is executed by the same one-cell instruction
set, with a one-bit borrow in finite control. -/
example : PolynomialTime BinarySubtraction.program := BinarySubtraction.polynomialTime

example (pairs : List (Bool × Bool))
    (h : Binary.value (pairs.map Prod.snd) ≤ Binary.value (pairs.map Prod.fst)) :
    (evalWithin BinarySubtraction.program (BinaryComparison.interleave pairs)
      (7 * pairs.length + 3)).map (Option.map Binary.value) =
      PMF.pure (some (Binary.value (pairs.map Prod.fst) - Binary.value (pairs.map Prod.snd))) :=
  BinarySubtraction.eval_difference pairs h

example : Binary.value (BinarySubtraction.differenceBits false
    [(true, true), (false, true), (true, false)]) = 2 := by decide

/-- Both sides of the conditional subtraction use actual finite code. At
modulus seven, doubling two and adding one copies five after underflow; doing
this with three subtracts the modulus and returns zero. -/
example : PolynomialTime BinaryDoubleReduction.program := BinaryDoubleReduction.polynomialTime

private def residueTwo : List (Bool × Bool) :=
  [(false, true), (true, true), (false, true), (false, false)]

private def residueThree : List (Bool × Bool) :=
  [(true, true), (true, true), (false, true), (false, false)]

example : evalWithin BinaryDoubleReduction.program
    (true :: BinaryComparison.interleave residueTwo) 87 =
    PMF.pure (some [true, false, true, false]) := by
  simpa [residueTwo, Binary.value, Binary.encode] using
    BinaryDoubleReduction.eval_double_mod_encoded true residueTwo (by decide) (by decide)

example : evalWithin BinaryDoubleReduction.program
    (true :: BinaryComparison.interleave residueThree) 87 =
    PMF.pure (some [false, false, false, false]) := by
  simpa [residueThree, Binary.value, Binary.encode] using
    BinaryDoubleReduction.eval_double_mod_encoded true residueThree (by decide) (by decide)

/-- The modular-addition kernel preserves both operands. For 2+3 modulo 7,
the tentative difference underflows and the code rewrites the original sum.
For 3+4 modulo 7, the difference is accepted without that rewrite. -/
private def modularSumFive : List BinaryModularAddition.Column :=
  [((false, true), true), ((true, true), true),
    ((false, false), true), ((false, false), false)]

private def modularSumSeven : List BinaryModularAddition.Column :=
  [((true, false), true), ((true, false), true),
    ((false, true), true), ((false, false), false)]

example : evalWithin BinaryModularAddition.program
    (BinaryModularAddition.interleave modularSumFive) 106 =
    PMF.pure (some [true, false, true, false]) := by
  simpa [modularSumFive, BinaryModularAddition.operands, BinaryModularAddition.moduli,
    Binary.value, Binary.encode] using
    BinaryModularAddition.eval_add_mod_encoded modularSumFive (by decide) (by decide) (by decide)

example : evalWithin BinaryModularAddition.program
    (BinaryModularAddition.interleave modularSumSeven) 106 =
    PMF.pure (some [false, false, false, false]) := by
  simpa [modularSumSeven, BinaryModularAddition.operands, BinaryModularAddition.moduli,
    Binary.value, Binary.encode] using
    BinaryModularAddition.eval_add_mod_encoded modularSumSeven (by decide) (by decide) (by decide)

example : PolynomialTime BinaryModularAddition.program := BinaryModularAddition.polynomialTime

/-- Both possible truncated-column lengths are included in the all-input
stopping theorem, independently of the numeric preconditions for correctness. -/
example : HaltsWithin BinaryModularAddition.program [true] 48 := BinaryModularAddition.haltsWithin _
example : HaltsWithin BinaryModularAddition.program [false, true] 72 := BinaryModularAddition.haltsWithin _

/-- The product-loop invariant is checked separately from machine assembly.
These are specifications, not a claim that a full multiplier already exists. -/
example : BinaryModularProduct.product 7 3 [true, false, true] = 1 := by decide

example (bits : List Bool) : BinaryModularProduct.product 7 3 bits =
    3 * Binary.value bits % 7 := BinaryModularProduct.product_value 7 3 bits

/-- Both arithmetic kernels of one iteration execute their actual finite
codes. Preparing the second input on tape remains a separate assembly task. -/
example :
    evalWithin BinaryDoubleReduction.program
      (false :: BinaryComparison.interleave (BinaryModularProduct.doubleInput 4 3 7)) 87 =
      PMF.pure (some (Binary.encode 4 6)) ∧
    evalWithin BinaryModularAddition.program
      (BinaryModularAddition.interleave (BinaryModularProduct.addInput 4 6 5 7)) 106 =
      PMF.pure (some (Binary.encode 4 4)) := by
  simpa [BinaryModularProduct.step] using
    BinaryModularProduct.step_kernels_correct 4 7 5 3 true (by decide) (by decide) (by decide) (by decide)

end Machine.Examples
