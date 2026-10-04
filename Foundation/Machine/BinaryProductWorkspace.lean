import Foundation.Machine.BinaryProductSelection

namespace Machine.BinaryProductWorkspace

open BinaryProductSelection

/-- Overwrite only the accumulator track of the matrix, reading one result
bit from the other tape per column. Other tracks and the result tape's bits
are preserved. Tape heads move by five and one actual cells respectively. -/
def scatterProgram : Program :=
  [.branch .input 15 1 1, .branch .output 16 2 5,
   .write .input false, .moveRight .output, .jump 8,
   .write .input true, .moveRight .output, .jump 8,
   .moveRight .input, .moveRight .input, .moveRight .input,
   .moveRight .input, .moveRight .input, .jump 0,
   .halt, .halt, .halt]

def replaceAccumulator (columns : List Column) (bits : List Bool) : List Column :=
  List.zipWith (fun column bit => { column with accumulator := bit }) columns bits

def scatterStart (beforeInput beforeOutput : List (Option Bool))
    (input output : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits input with left := beforeInput },
    outputTape := { Tape.ofBits output with left := beforeOutput } }

private def scatterFinish (beforeInput beforeOutput : List (Option Bool)) : Configuration :=
  { pc := 15, inputTape := { left := beforeInput }, outputTape := { left := beforeOutput }, halted := true }

private theorem eval_scatter_column (column : Column) (bit : Bool)
    (beforeInput beforeOutput : List (Option Bool)) (restInput restOutput : List Bool) :
    evalConfigWithin scatterProgram
      (scatterStart beforeInput beforeOutput (row column ++ restInput) (bit :: restOutput)) 11 =
      PMF.pure (scatterStart
        ((row { column with accumulator := bit }).reverse.map some ++ beforeInput)
        (some bit :: beforeOutput) restInput restOutput) := by
  cases hAccumulator : column.accumulator <;> cases bit <;> cases restInput <;> cases restOutput <;>
    simp [evalConfigWithin, stepPMF, next, scatterProgram, scatterStart, row, hAccumulator,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_scatter_end (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin scatterProgram (scatterStart beforeInput beforeOutput [] []) 2 =
      PMF.pure (scatterFinish beforeInput beforeOutput) := by
  simp [evalConfigWithin, stepPMF, next, scatterProgram, scatterStart, scatterFinish,
    Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

private theorem eval_scatter_columns (columns : List Column) (bits : List Bool)
    (hLength : bits.length = columns.length) (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin scatterProgram (scatterStart beforeInput beforeOutput (matrix columns) bits)
      (11 * columns.length + 2) =
      PMF.pure (scatterFinish
        ((matrix (replaceAccumulator columns bits)).reverse.map some ++ beforeInput)
        (bits.reverse.map some ++ beforeOutput)) := by
  induction columns generalizing bits beforeInput beforeOutput with
  | nil =>
      have hBits : bits = [] := by simpa using hLength
      subst bits
      simpa [matrix, replaceAccumulator] using eval_scatter_end beforeInput beforeOutput
  | cons column rest ih =>
      cases bits with
      | nil => simp at hLength
      | cons bit remaining =>
          have hRest : remaining.length = rest.length := by simpa using hLength
          have hBudget : 11 * (column :: rest).length + 2 = 11 + (11 * rest.length + 2) := by simp; omega
          rw [hBudget, evalConfigWithin_add]
          simp only [matrix, List.flatMap_cons, eval_scatter_column, PMF.pure_bind]
          simpa [matrix, replaceAccumulator, List.reverse_cons, List.reverse_append,
            List.map_append, List.append_assoc] using
            (ih remaining hRest
              ((row { column with accumulator := bit }).reverse.map some ++ beforeInput)
              (some bit :: beforeOutput))

/-- Every write to the accumulator and every head movement is part of this
execution. The result bits on the second tape are preserved, and the matrix's
operand, modulus, multiplier, and pending flags are unchanged. -/
theorem eval_scatter_context (columns : List Column) (bits : List Bool)
    (hLength : bits.length = columns.length) (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin scatterProgram (scatterStart beforeInput beforeOutput (matrix columns) bits)
      (11 * columns.length + 2) =
      PMF.pure {
        pc := 15,
        inputTape := { left := (matrix (replaceAccumulator columns bits)).reverse.map some ++ beforeInput },
        outputTape := { left := bits.reverse.map some ++ beforeOutput },
        halted := true } :=
  eval_scatter_columns columns bits hLength beforeInput beforeOutput

theorem eval_scatter (columns : List Column) (bits : List Bool)
    (hLength : bits.length = columns.length) :
    (evalConfigWithin scatterProgram (scatterStart [] [] (matrix columns) bits)
      (11 * columns.length + 2)).map
      (fun c => (c.halted, c.inputTape.bits, c.outputBits)) =
      PMF.pure (true, matrix (replaceAccumulator columns bits), bits) := by
  rw [eval_scatter_columns columns bits hLength, PMF.pure_map]
  simp [scatterFinish, Configuration.outputBits, Tape.bits]

theorem replaceAccumulator_pendingCount (columns : List Column) (bits : List Bool)
    (hLength : bits.length = columns.length) :
    pendingCount (replaceAccumulator columns bits) = pendingCount columns := by
  induction columns generalizing bits with
  | nil =>
      have hBits : bits = [] := by simpa using hLength
      subst bits
      rfl
  | cons column rest ih =>
      cases bits with
      | nil => simp at hLength
      | cons bit remaining =>
          have hRest : remaining.length = rest.length := by simpa using hLength
          have h := ih remaining hRest
          cases hPending : column.pending
          · simpa [replaceAccumulator, pendingCount, hPending] using h
          · simpa [replaceAccumulator, pendingCount, hPending] using h

private def noInputFinish (beforeInput beforeOutput : List (Option Bool)) (output : List Bool) :
    Configuration :=
  { pc := 15, inputTape := { left := beforeInput },
    outputTape := { Tape.ofBits output with left := beforeOutput }, halted := true }

private theorem eval_no_input (beforeInput beforeOutput : List (Option Bool)) (output : List Bool) :
    evalConfigWithin scatterProgram (scatterStart beforeInput beforeOutput [] output) 2 =
      PMF.pure (noInputFinish beforeInput beforeOutput output) := by
  simp [evalConfigWithin, stepPMF, next, scatterProgram, scatterStart, noInputFinish,
    Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

private def noOutputFinish (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    Configuration :=
  { pc := 16, inputTape := { Tape.ofBits input with left := beforeInput },
    outputTape := { left := beforeOutput }, halted := true }

private theorem eval_no_output (beforeInput beforeOutput : List (Option Bool))
    (first : Bool) (rest : List Bool) :
    evalConfigWithin scatterProgram (scatterStart beforeInput beforeOutput (first :: rest) []) 3 =
      PMF.pure (noOutputFinish beforeInput beforeOutput (first :: rest)) := by
  cases first <;>
    simp [evalConfigWithin, stepPMF, next, scatterProgram, scatterStart, noOutputFinish,
      Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

private def shortFinish (beforeInput beforeOutput : List (Option Bool))
    (input : List Bool) (bit : Bool) (output : List Bool) : Configuration :=
  { pc := 15,
    inputTape := (({ Tape.ofBits input with left := beforeInput } : Tape).write (some bit)).moveRight.moveRight.moveRight.moveRight.moveRight,
    outputTape := { Tape.ofBits output with left := some bit :: beforeOutput }, halted := true }

private theorem eval_short (beforeInput beforeOutput : List (Option Bool)) (first : Bool)
    (rest : List Bool) (hLength : rest.length < 4) (bit : Bool) (output : List Bool) :
    evalConfigWithin scatterProgram (scatterStart beforeInput beforeOutput (first :: rest) (bit :: output)) 13 =
      PMF.pure (shortFinish beforeInput beforeOutput (first :: rest) bit output) := by
  match rest with
  | [] | [_] | [_, _] | [_, _, _] =>
      cases first <;> cases bit <;> cases output <;>
        simp [evalConfigWithin, stepPMF, next, scatterProgram, scatterStart, shortFinish,
          Instruction.next, Configuration.advance, Configuration.tape,
          Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]
  | _ :: _ :: _ :: _ :: _ => simp only [List.length_cons] at hLength; omega

private theorem eval_halted (c : Configuration) (steps : Nat) (h : c.halted = true) :
    evalConfigWithin scatterProgram c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private theorem eval_raw (input output : List Bool) (beforeInput beforeOutput : List (Option Bool)) :
    ∃ result : Configuration, result.halted = true ∧
      evalConfigWithin scatterProgram (scatterStart beforeInput beforeOutput input output)
        (11 * (input.length + 1)) = PMF.pure result := by
  match input with
  | [] =>
      refine ⟨noInputFinish beforeInput beforeOutput output, rfl, ?_⟩
      change evalConfigWithin scatterProgram (scatterStart beforeInput beforeOutput [] output) (2 + 9) = _
      rw [evalConfigWithin_add, eval_no_input, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | first :: rest =>
      cases output with
      | nil =>
          refine ⟨noOutputFinish beforeInput beforeOutput (first :: rest), rfl, ?_⟩
          have hBudget : 11 * ((first :: rest).length + 1) = 3 + (11 * rest.length + 19) := by simp; omega
          rw [hBudget, evalConfigWithin_add, eval_no_output, PMF.pure_bind]
          exact eval_halted _ _ rfl
      | cons bit output =>
          by_cases hLength : rest.length < 4
          · refine ⟨shortFinish beforeInput beforeOutput (first :: rest) bit output, rfl, ?_⟩
            have hBudget : 11 * ((first :: rest).length + 1) = 13 + (11 * rest.length + 9) := by simp; omega
            rw [hBudget, evalConfigWithin_add, eval_short beforeInput beforeOutput first rest hLength,
              PMF.pure_bind]
            exact eval_halted _ _ rfl
          · match rest with
            | operand :: modulus :: multiplier :: pending :: remaining =>
                let column : Column := ⟨first, operand, modulus, multiplier, pending⟩
                obtain ⟨result, hHalted, hEval⟩ := eval_raw remaining output
                  ((row { column with accumulator := bit }).reverse.map some ++ beforeInput)
                  (some bit :: beforeOutput)
                refine ⟨result, hHalted, ?_⟩
                have hBudget : 11 * ((first :: operand :: modulus :: multiplier :: pending :: remaining).length + 1) =
                    11 + (11 * (remaining.length + 1) + 44) := by simp; omega
                rw [hBudget, evalConfigWithin_add]
                change ((evalConfigWithin scatterProgram
                  (scatterStart beforeInput beforeOutput (row column ++ remaining) (bit :: output)) 11).bind
                  fun c => evalConfigWithin scatterProgram c (11 * (remaining.length + 1) + 44)) = _
                rw [eval_scatter_column, PMF.pure_bind, evalConfigWithin_add, hEval, PMF.pure_bind]
                exact eval_halted _ _ hHalted
            | [] | [_] | [_, _] | [_, _, _] => simp at hLength
termination_by input.length

/-- Termination with both finite tapes loaded is required by the product
loop. Truncated rows and missing result bits also terminate. The saved left
prefixes are arbitrary; the bound depends only on the unvisited input suffix. -/
theorem scatter_haltsFrom (input output : List Bool) (beforeInput beforeOutput : List (Option Bool))
    (finish : Configuration)
    (run : PaddedRunsFor scatterProgram (scatterStart beforeInput beforeOutput input output)
      finish (11 * (input.length + 1))) : finish.halted = true := by
  obtain ⟨result, hHalted, hEval⟩ := eval_raw input output beforeInput beforeOutput
  have hSupport := (mem_support_evalConfigWithin_iff scatterProgram _ finish _).mpr run
  rw [hEval, PMF.mem_support_pure_iff] at hSupport
  exact hSupport ▸ hHalted

end Machine.BinaryProductWorkspace
