import Foundation.Crypto.Semantics.Machine.BinarySquareGather
import Foundation.Crypto.Semantics.Machine.BinaryProductSemantics

namespace Machine.BinaryPowerPhase

open BinaryProductSelection BinaryProductWorkspace GuardedCompiler

def squareProgram : Program :=
  BinaryProductPhase.program BinarySquareGather.program BinaryProductProgram.program

def multiplyProgram : Program :=
  BinaryProductPhase.program (BinaryProductGather.addTriplesProgram true) BinaryProductProgram.program

def multiplyRequest (columns : List Column) : List Bool :=
  BinaryProductPhase.addRequest true columns

def squareBudget (width : Nat) : Nat :=
  BinaryProductPhase.budget (19 * width + 2) width BinaryProductProgram.budget (3 * width)

def multiplyBudget (width : Nat) : Nat :=
  BinaryProductPhase.budget (30 * width + 2) width BinaryProductProgram.budget (3 * width)

theorem square_no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ squareProgram :=
  BinaryProductPhase.no_randomBit _ _ BinarySquareGather.no_randomBit BinaryProductProgram.no_randomBit tape

theorem multiply_no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ multiplyProgram :=
  BinaryProductPhase.no_randomBit _ _ (BinaryProductGather.addTriples_no_randomBit true)
    BinaryProductProgram.no_randomBit tape

/-- The square phase calls the full native modular multiplier on a request
written by the square gatherer. It retains the same matrix and scratch data. -/
theorem square_runs_from_split (columns : List Column) (leading remaining : List Bool)
    (saved : List (Option Bool)) (hMatrix : leading ++ remaining = matrix columns) :
    ∃ (bits : List Bool) (target : Configuration) (used : Nat) (retained : List (Option Bool)),
      bits.length = columns.length ∧ used ≤ squareBudget columns.length ∧
      RunsFor squareProgram
        { inputTape := { Tape.ofBits remaining with left := leading.reverse.map some },
          outputTape := { left := saved } } target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { left := (matrix (replaceAccumulator columns bits)).reverse.map some ++ [none] } ∧
      target.outputTape.Equivalent { left := bits.reverse.map some ++ none :: retained } ∧
      evalWithin BinaryProductProgram.program (BinarySquareGather.request columns)
        (BinaryProductProgram.budget (BinarySquareGather.request columns).length) = PMF.pure (some bits) := by
  obtain ⟨bits, hLength, hEval⟩ := BinaryProductSemantics.complete_output
    (columns.map fun column => ((column.accumulator, column.accumulator), column.modulus))
  have hLength' : bits.length = columns.length := by simpa using hLength
  obtain ⟨target, used, retained, hUsed, native, hHalt, hInput, hOutput⟩ :=
    BinaryProductPhase.runs_from_split BinarySquareGather.program BinaryProductProgram.program
      columns leading remaining (BinarySquareGather.request columns) bits saved (19 * columns.length + 2)
      BinaryProductProgram.budget hMatrix hLength' BinaryProductProgram.no_randomBit
      (BinaryProductProgram.haltsWithin _) hEval (BinarySquareGather.eval_gather columns saved)
  refine ⟨bits, target, used, retained, hLength', ?_, native, hHalt, hInput, hOutput, hEval⟩
  simpa only [BinarySquareGather.request_length, squareBudget] using hUsed

theorem multiply_runs (columns : List Column) (saved : List (Option Bool)) :
    ∃ (bits : List Bool) (target : Configuration) (used : Nat) (retained : List (Option Bool)),
      bits.length = columns.length ∧ used ≤ multiplyBudget columns.length ∧
      RunsFor multiplyProgram (BinaryProductPhase.start columns saved) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { left := (matrix (replaceAccumulator columns bits)).reverse.map some ++ [none] } ∧
      target.outputTape.Equivalent { left := bits.reverse.map some ++ none :: retained } ∧
      evalWithin BinaryProductProgram.program (multiplyRequest columns)
        (BinaryProductProgram.budget (multiplyRequest columns).length) = PMF.pure (some bits) := by
  obtain ⟨bits, hLength, hEval⟩ := BinaryProductSemantics.complete_output
    (columns.map fun column => ((column.accumulator, column.operand), column.modulus))
  have hLength' : bits.length = columns.length := by simpa using hLength
  have hGather := BinaryProductGather.eval_addTriples_context true columns [none] (none :: saved)
  obtain ⟨target, used, retained, hUsed, native, hHalt, hInput, hOutput⟩ :=
    BinaryProductPhase.runs (BinaryProductGather.addTriplesProgram true) BinaryProductProgram.program
      columns (multiplyRequest columns) bits saved (30 * columns.length + 2) BinaryProductProgram.budget
      hLength' BinaryProductProgram.no_randomBit (BinaryProductProgram.haltsWithin _) hEval
      (by simpa only [multiplyRequest, BinaryProductPhase.addRequest, Bool.true_eq, ↓reduceIte,
        BinaryProductGather.gatherStart, BinaryProductGather.gatherFinish,
        show (BinaryProductGather.addTriplesProgram true).length = 46 from rfl] using hGather)
  refine ⟨bits, target, used, retained, hLength', ?_, native, hHalt, hInput, hOutput, hEval⟩
  have hRequest : (multiplyRequest columns).length = 3 * columns.length := by
    simp only [multiplyRequest, BinaryProductPhase.addRequest, Bool.true_eq, ↓reduceIte,
      BinaryProductSemantics.interleave_length, List.length_map]
  simpa only [hRequest, multiplyBudget] using hUsed

private theorem budget_le (gatherSteps width : Nat) (hGather : gatherSteps ≤ 30 * width + 2) :
    BinaryProductPhase.budget gatherSteps width BinaryProductProgram.budget (3 * width) ≤
      1000000000000000000000 * (width + 1) ^ 9 := by
  have hRaw := rawTraceBudget_bound BinaryProductProgram.budget (3 * width)
  have hWidth : 1 ≤ width + 1 := by omega
  have hCube : width + 1 ≤ (width + 1) ^ 9 := le_self_pow hWidth (by decide)
  have hInput : 3 * width + 1 ≤ 3 * (width + 1) := by omega
  have hPow := Nat.pow_le_pow_left hInput 4
  have hKernel : BinaryProductProgram.budget (3 * width) + 1 ≤ 81000001 * (width + 1) ^ 4 := by
    dsimp only [BinaryProductProgram.budget]
    have hOne : 1 ≤ (width + 1) ^ 4 := one_le_pow₀ hWidth
    nlinarith [hPow, hOne]
  have hFactor := Nat.mul_le_mul hInput (Nat.pow_le_pow_left hKernel 2)
  have hMajorant : rawTraceBudget BinaryProductProgram.budget (3 * width) ≤
      2460375060750000375 * (width + 1) ^ 9 := by
    calc
      _ ≤ 125 * (3 * (width + 1) * (81000001 * (width + 1) ^ 4) ^ 2) := by
        exact hRaw.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 125 hFactor)
      _ = _ := by ring
  dsimp only [BinaryProductPhase.budget, BinaryProductWriteback.budget]
  nlinarith

theorem squareBudget_le (width : Nat) : squareBudget width ≤
    1000000000000000000000 * (width + 1) ^ 9 := budget_le _ _ (by omega)

theorem multiplyBudget_le (width : Nat) : multiplyBudget width ≤
    1000000000000000000000 * (width + 1) ^ 9 := budget_le _ _ (by omega)

/-- A zero exponent bit uses an actual copy phase after the square. The
source accumulator is preserved by native traversal, copying, and writeback. -/
def conditionalProgram (bit : Bool) : Program :=
  if bit then multiplyProgram else BinaryProductPhase.program BinaryProductGather.resultProgram copyBitstring

def conditionalRequest (bit : Bool) (columns : List Column) : List Bool :=
  if bit then multiplyRequest columns else columns.map Column.accumulator

def conditionalKernel (bit : Bool) : Program := if bit then BinaryProductProgram.program else copyBitstring

def conditionalKernelBudget (bit : Bool) : Nat → Nat :=
  if bit then BinaryProductProgram.budget else fun length => 6 * length + 2

def conditionalBudget (bit : Bool) (width : Nat) : Nat :=
  if bit then multiplyBudget width else
    BinaryProductPhase.budget (30 * width + 2) width (fun length => 6 * length + 2) width

theorem conditional_no_randomBit (bit : Bool) (tape : TapeId) :
    Instruction.randomBit tape ∉ conditionalProgram bit := by
  cases bit
  · exact BinaryProductPhase.no_randomBit _ _ (by intro tape; cases tape <;> decide) copyBitstring_no_randomBit tape
  · exact multiply_no_randomBit tape

theorem conditional_runs (bit : Bool) (columns : List Column) (saved : List (Option Bool)) :
    ∃ (bits : List Bool) (target : Configuration) (used : Nat) (retained : List (Option Bool)),
      bits.length = columns.length ∧ used ≤ conditionalBudget bit columns.length ∧
      RunsFor (conditionalProgram bit) (BinaryProductPhase.start columns saved) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { left := (matrix (replaceAccumulator columns bits)).reverse.map some ++ [none] } ∧
      target.outputTape.Equivalent { left := bits.reverse.map some ++ none :: retained } ∧
      evalWithin (conditionalKernel bit) (conditionalRequest bit columns)
        (conditionalKernelBudget bit (conditionalRequest bit columns).length) = PMF.pure (some bits) := by
  cases bit with
  | true => exact multiply_runs columns saved
  | false =>
      let bits := columns.map Column.accumulator
      have hLength : bits.length = columns.length := List.length_map _
      obtain ⟨target, used, retained, hUsed, native, hHalt, hInput, hOutput⟩ :=
        BinaryProductPhase.runs BinaryProductGather.resultProgram copyBitstring columns bits bits saved
          (30 * columns.length + 2) (fun length => 6 * length + 2) hLength
          copyBitstring_no_randomBit (copyBitstring_haltsWithin bits) (copyBitstring_eval bits)
          (by simpa only [BinaryProductGather.gatherStart, BinaryProductGather.gatherFinish,
            show BinaryProductGather.resultProgram.length = 46 from rfl] using
              BinaryProductGather.eval_result_context columns [none] (none :: saved))
      refine ⟨bits, target, used, retained, hLength, ?_, native, hHalt, hInput, hOutput, copyBitstring_eval bits⟩
      simpa only [hLength, conditionalBudget, Bool.false_eq_true, ite_false] using hUsed

theorem conditionalBudget_le (bit : Bool) (width : Nat) : conditionalBudget bit width ≤
    1000000000000000000000 * (width + 1) ^ 9 := by
  cases bit with
  | true => exact multiplyBudget_le width
  | false =>
      have hRaw := rawTraceBudget_bound (fun length => 6 * length + 2) width
      have hOne : 1 ≤ width + 1 := by omega
      have hPoly : width + 1 ≤ (width + 1) ^ 9 := le_self_pow hOne (by decide)
      have hCube : (width + 1) ^ 3 ≤ (width + 1) ^ 9 := pow_le_pow_right₀ hOne (by decide)
      have hRawBound : rawTraceBudget (fun length => 6 * length + 2) width ≤ 10125 * (width + 1) ^ 3 := by
        nlinarith
      simp only [conditionalBudget, Bool.false_eq_true, ite_false]
      dsimp only [BinaryProductPhase.budget, BinaryProductWriteback.budget]
      nlinarith

end Machine.BinaryPowerPhase
