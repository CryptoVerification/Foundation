import Foundation.Crypto.Semantics.Machine.BinaryProductGather

set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace Machine.BinarySquareGather

open BinaryProductSelection

/-- Native preparation of square-product columns from the same five-track
workspace. The accumulator bit is written twice; no list projection or tape
reconstruction is a machine instruction. -/
def program : Program :=
  [.branch .input 27 1 6,
   .write .output false, .moveRight .output, .write .output false, .moveRight .output, .jump 11,
   .write .output true, .moveRight .output, .write .output true, .moveRight .output, .jump 11,
   .moveRight .input, .branch .input 27 13 13, .moveRight .input,
   .branch .input 27 15 18,
   .write .output false, .moveRight .output, .jump 21,
   .write .output true, .moveRight .output, .jump 21,
   .moveRight .input, .branch .input 27 23 23, .moveRight .input,
   .branch .input 27 25 25, .moveRight .input, .jump 0, .halt]

def request (columns : List Column) : List Bool :=
  BinaryModularAddition.interleave (columns.map fun column =>
    ((column.accumulator, column.accumulator), column.modulus))

private def state (before written : List (Option Bool)) (input : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits input with left := before }, outputTape := { left := written } }

private def finish (before written : List (Option Bool)) : Configuration :=
  { pc := 27, inputTape := { left := before }, outputTape := { left := written }, halted := true }

private theorem eval_column (column : Column) (rest : List Column)
    (before written : List (Option Bool)) :
    evalConfigWithin program (state before written (matrix (column :: rest))) 19 =
      PMF.pure (state ((row column).reverse.map some ++ before)
        ([column.accumulator, column.accumulator, column.modulus].reverse.map some ++ written)
        (matrix rest)) := by
  rcases column with ⟨accumulator, operand, modulus, multiplier, pending⟩
  cases accumulator <;> cases modulus <;> cases operand <;> cases multiplier <;> cases pending <;>
    cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, state, matrix, row,
      Instruction.next, Configuration.advance, Configuration.tape, Configuration.updateTape,
      Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_end (before written : List (Option Bool)) :
    evalConfigWithin program (state before written []) 2 = PMF.pure (finish before written) := by
  simp [evalConfigWithin, stepPMF, next, program, state, finish,
    Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

theorem eval_context (columns : List Column) (before written : List (Option Bool)) :
    evalConfigWithin program (state before written (matrix columns)) (19 * columns.length + 2) =
      PMF.pure (finish ((matrix columns).reverse.map some ++ before)
        ((request columns).reverse.map some ++ written)) := by
  induction columns generalizing before written with
  | nil => simpa [matrix, request, BinaryModularAddition.interleave] using eval_end before written
  | cons column rest ih =>
      have time : 19 * (column :: rest).length + 2 = 19 + (19 * rest.length + 2) := by simp; omega
      rw [time, evalConfigWithin_add, eval_column, PMF.pure_bind]
      simpa [matrix, request, BinaryModularAddition.interleave, List.reverse_append,
        List.map_append, List.append_assoc] using ih ((row column).reverse.map some ++ before)
          ([column.accumulator, column.accumulator, column.modulus].reverse.map some ++ written)

theorem eval_gather (columns : List Column) (saved : List (Option Bool)) :
    evalConfigWithin program
      { inputTape := { Tape.ofBits (matrix columns) with left := [none] },
        outputTape := { left := none :: saved } } (19 * columns.length + 2) =
      PMF.pure {
        pc := program.length - 1,
        inputTape := { left := (matrix columns).reverse.map some ++ [none] },
        outputTape := { left := (request columns).reverse.map some ++ none :: saved }, halted := true } :=
  eval_context columns [none] (none :: saved)

theorem request_length (columns : List Column) : (request columns).length = 3 * columns.length := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp [request, BinaryModularAddition.interleave] at ih ⊢; omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> simp [program]

end Machine.BinarySquareGather
