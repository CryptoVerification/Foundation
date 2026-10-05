import Foundation.Crypto.Semantics.Machine.BinaryModularAddition

namespace Machine.BinaryThirdColumnTemplate

/-- From a contiguous modulus bitstring, write three-cell columns with
blank-valued first and second slots. Both placeholders are actual `false`
cells and can later be overwritten by operand bits. This is only a stage of
the framed multiplication request preparation. -/
def program : Program :=
  [.branch .input 13 1 1,
   .write .output false, .moveRight .output,
   .write .output false, .moveRight .output,
   .branch .input 13 6 8,
   .write .output false, .jump 10,
   .write .output true, .jump 10,
   .moveRight .output, .moveRight .input, .jump 0,
   .halt]

def columns (modulus : List Bool) : List Bool :=
  BinaryModularAddition.interleave (modulus.map fun bit => ((false, false), bit))

theorem columns_length (modulus : List Bool) : (columns modulus).length = 3*modulus.length := by
  induction modulus with
  | nil => rfl
  | cons bit rest ih =>
    simp [columns, BinaryModularAddition.interleave] at *
    omega

private def state (beforeInput beforeOutput : List (Option Bool))
    (remaining : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits remaining with left := beforeInput },
    outputTape := { left := beforeOutput } }

private def finish (beforeInput beforeOutput : List (Option Bool)) : Configuration :=
  { pc := 13, inputTape := { left := beforeInput },
    outputTape := { left := beforeOutput }, halted := true }

private theorem eval_bit (beforeInput beforeOutput : List (Option Bool))
    (bit : Bool) (rest : List Bool) :
    evalConfigWithin program (state beforeInput beforeOutput (bit :: rest)) 11 =
      PMF.pure (state (some bit :: beforeInput)
        ([false, false, bit].reverse.map some ++ beforeOutput) rest) := by
  cases bit <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, state,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write,
      PMF.pure_bind]

private theorem eval_end (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program (state beforeInput beforeOutput []) 2 =
      PMF.pure (finish beforeInput beforeOutput) := by
  simp [evalConfigWithin, stepPMF, next, program, state, finish,
    Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

/-- The same physical input and output tapes are threaded through every
column. No list of columns is installed as a fresh machine tape. -/
theorem eval_context (beforeInput beforeOutput : List (Option Bool))
    (modulus : List Bool) :
    evalConfigWithin program (state beforeInput beforeOutput modulus)
      (11 * modulus.length + 2) =
      PMF.pure (finish (modulus.reverse.map some ++ beforeInput)
        ((columns modulus).reverse.map some ++ beforeOutput)) := by
  induction modulus generalizing beforeInput beforeOutput with
  | nil => simpa [columns, BinaryModularAddition.interleave] using
      eval_end beforeInput beforeOutput
  | cons bit rest ih =>
      have hTime : 11 * (bit :: rest).length + 2 =
          11 + (11 * rest.length + 2) := by simp; omega
      rw [hTime, evalConfigWithin_add, eval_bit, PMF.pure_bind]
      simpa [columns, BinaryModularAddition.interleave,
        List.reverse_cons, List.reverse_append, List.map_append,
        List.append_assoc] using
        ih (some bit :: beforeInput)
          ([false, false, bit].reverse.map some ++ beforeOutput)

/-- All finite contiguous inputs are processed within a linear number of
native bit-machine transitions. -/
theorem eval (modulus : List Bool) :
    evalWithin program modulus (11 * modulus.length + 2) =
      PMF.pure (some (columns modulus)) := by
  have hInitial : Configuration.initial modulus = state [] [] modulus := by
    cases modulus <;> rfl
  rw [evalWithin, hInitial, eval_context, PMF.pure_map]
  simp [finish, Configuration.outputBits, Tape.bits]

theorem haltsWithin (modulus : List Bool) :
    HaltsWithin program modulus (11 * modulus.length + 2) := by
  apply haltsWithin_of_no_timeout_support program modulus _
  rw [eval]
  simp

theorem polynomialTime : PolynomialTime program := by
  refine ⟨fun length => 11 * length + 2, ?_, haltsWithin⟩
  exact ((PolynomiallyBounded.const 11).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 2)

end Machine.BinaryThirdColumnTemplate
