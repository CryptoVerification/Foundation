import Foundation.Crypto.Semantics.Machine.BinaryProductGather

namespace Machine.Examples.BinaryProductWorkspace

open BinaryProductSelection

/-- Regression operands are 3 and 5, modulus 7, padded to four binary
columns. This is a test of native work components, not a security claim. -/
private def inputColumns : List BinaryModularAddition.Column :=
  [((true, true), true), ((true, false), true),
    ((false, true), true), ((false, false), false)]

private def columns : List Column := initialColumns inputColumns

example : evalWithin BinaryProductInitialization.program
    (BinaryModularAddition.interleave inputColumns) 70 =
    PMF.pure (some (matrix columns)) := by
  simpa [columns, inputColumns, initialColumns_matrix] using
    BinaryProductInitialization.eval_interleave inputColumns

example : pendingCount columns = 4 := by
  simpa [columns, inputColumns] using initialColumns_pendingCount inputColumns

/-- The most significant padding bit is selected first. Its actual pending
flag is changed on the input tape, with the operand and modulus retained. -/
example :
    (evalConfigWithin BinaryProductSelection.program (Configuration.initial (matrix columns)) 92).map
      (fun c => (c.halted, c.inputTape.bits, c.outputBits)) =
      PMF.pure (true, matrix (consume columns.reverse).reverse, [false]) := by
  simpa [columns, inputColumns, initialColumns, matrix, row, selected] using eval_selection columns

/-- A saved result from a previous call stays on the output tape while the
new multiplier bit is selected. The input flag is still physically consumed. -/
example :
    (evalConfigWithin BinaryProductSelection.program
      (selectionStart columns [some true, some false, none]) 92).map
      (fun c => (c.halted, c.inputTape.bits, c.outputBits)) =
      PMF.pure (true, matrix (consume columns.reverse).reverse, [false, true, false]) := by
  simpa [columns, inputColumns, initialColumns, matrix, row, selected] using
    eval_selection_savedBits columns [some true, some false, none]

example : selected ((consume^[4]) columns.reverse) = none := by
  have hCount : pendingCount columns.reverse = 4 := by decide
  simpa only [hCount] using selection_exhausted columns.reverse

/-- The full double input includes a header written by the machine. Caller
prefixes can be retained; no new input tape is supplied between these writes. -/
example : evalWithin BinaryProductGather.doubleInputProgram (matrix columns) 125 =
    PMF.pure (some [false, false, true, false, true, false, true, false, false]) := by
  simpa [columns, inputColumns, initialColumns, BinaryComparison.interleave] using
    BinaryProductGather.eval_doubleInput columns

/-- At a zero selected multiplier bit the operand track is replaced with
zero bits in the prepared add request; a true bit copies the original 3. -/
example : evalWithin (BinaryProductGather.addTriplesProgram false) (matrix columns) 122 =
    PMF.pure (some [false, false, true, false, false, true,
      false, false, true, false, false, false]) := by
  simpa [columns, inputColumns, initialColumns, BinaryModularAddition.interleave] using
    BinaryProductGather.eval_addTriples false columns

example : evalWithin (BinaryProductGather.addTriplesProgram true) (matrix columns) 122 =
    PMF.pure (some [false, true, true, false, true, true,
      false, false, true, false, false, false]) := by
  simpa [columns, inputColumns, initialColumns, BinaryModularAddition.interleave] using
    BinaryProductGather.eval_addTriples true columns

/-- After an arithmetic result is written back, the original factor,
modulus, multiplier, and pending flags remain in the same physical matrix. -/
example :
    (evalConfigWithin BinaryProductWorkspace.scatterProgram
      (BinaryProductWorkspace.scatterStart [] [] (matrix columns) (Binary.encode 4 6)) 46).map
      (fun c => (c.halted, c.inputTape.bits, c.outputBits)) =
      PMF.pure (true,
        matrix (BinaryProductWorkspace.replaceAccumulator columns (Binary.encode 4 6)),
        Binary.encode 4 6) :=
  BinaryProductWorkspace.eval_scatter columns _ (by decide)

example : pendingCount (BinaryProductWorkspace.replaceAccumulator columns (Binary.encode 4 6)) = 4 := by
  rw [BinaryProductWorkspace.replaceAccumulator_pendingCount _ _ (by decide)]
  decide

example : evalWithin BinaryProductGather.resultProgram
    (matrix (BinaryProductWorkspace.replaceAccumulator columns (Binary.encode 4 6))) 122 =
    PMF.pure (some (Binary.encode 4 6)) := by
  simpa [columns, inputColumns, initialColumns, BinaryProductWorkspace.replaceAccumulator, Binary.encode] using
    BinaryProductGather.eval_result
      (BinaryProductWorkspace.replaceAccumulator columns (Binary.encode 4 6))

example : PolynomialTime BinaryProductInitialization.program := BinaryProductInitialization.polynomialTime
example : PolynomialTime BinaryProductSelection.program := BinaryProductSelection.polynomialTime
example : PolynomialTime BinaryProductGather.doubleInputProgram := BinaryProductGather.doubleInput_polynomialTime
example : PolynomialTime (BinaryProductGather.addTriplesProgram false) := BinaryProductGather.addTriples_polynomialTime false
example : PolynomialTime BinaryProductGather.resultProgram := BinaryProductGather.result_polynomialTime

/-- Truncated rows also stop. The scatter certificate permits arbitrary
saved prefixes and both loaded tapes, as required by a later caller. -/
example (finish : Configuration)
    (run : PaddedRunsFor BinaryProductWorkspace.scatterProgram
      (BinaryProductWorkspace.scatterStart [some true, none] [some false]
        [true, false] [false]) finish 33) : finish.halted = true :=
  BinaryProductWorkspace.scatter_haltsFrom _ _ _ _ finish run

end Machine.Examples.BinaryProductWorkspace
