import Foundation.Crypto.Semantics.Machine.SecurityWidthTemplate

namespace Machine.MoveInputLeftByColumns

/-- Use each populated three-cell output column as a counter while moving
the input head across one fixed-width field. The
output bits are only read; malformed input bits have no effect on control. -/
def program : Program :=
  [.branch .output 6 1 1,
   .moveLeft .input,
   .moveRight .output, .moveRight .output, .moveRight .output,
   .jump 0, .halt]

private def state (input output : Tape) : Configuration :=
  { inputTape := input, outputTape := output }

private def finish (input output : Tape) : Configuration :=
  { pc := 6, inputTape := input, outputTape := output, halted := true }

private theorem eval_step (input output : Tape)
    (hCurrent : output.current ≠ none) :
    evalConfigWithin program (state input output) 6 =
      PMF.pure (state input.moveLeft
        output.moveRight.moveRight.moveRight) := by
  cases output with
  | mk left current right =>
    cases current with
    | none => contradiction
    | some bit =>
        cases bit <;>
          simp [evalConfigWithin, stepPMF, next, program, state,
            Instruction.next, Configuration.advance, Configuration.tape,
            Configuration.updateTape, Tape.moveRight, PMF.pure_bind]

private theorem eval_end (input output : Tape)
    (hCurrent : output.current = none) :
    evalConfigWithin program (state input output) 2 =
      PMF.pure (finish input output) := by
  cases output with
  | mk left current right =>
    cases current with
    | none =>
        simp [evalConfigWithin, stepPMF, next, program, state, finish,
          Instruction.next, Configuration.tape, PMF.pure_bind]
    | some bit => contradiction

/-- Each complete output column causes exactly one actual input-head move.
All output cells and all input cells are preserved. -/
theorem eval_columns (columns : List BinaryModularAddition.Column) (input : Tape)
    (beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (state input {Tape.ofBits (BinaryModularAddition.interleave columns) with left := beforeOutput})
      (6*columns.length+2) =
    PMF.pure (finish ((Tape.moveLeft^[columns.length]) input)
      {left := (BinaryModularAddition.interleave columns).reverse.map some ++ beforeOutput}) := by
  induction columns generalizing input beforeOutput with
  | nil =>
    simpa [BinaryModularAddition.interleave,Tape.ofBits] using eval_end input {left := beforeOutput} rfl
  | cons column rest ih =>
    rcases column with ⟨⟨a,b⟩,p⟩
    have current : ({Tape.ofBits (BinaryModularAddition.interleave (((a,b),p)::rest)) with left := beforeOutput} : Tape).current ≠ none := by
      simp [BinaryModularAddition.interleave,Tape.ofBits]
    have outStep : ((({Tape.ofBits (BinaryModularAddition.interleave (((a,b),p)::rest)) with left := beforeOutput} : Tape).moveRight).moveRight).moveRight =
        {Tape.ofBits (BinaryModularAddition.interleave rest) with left := [some p,some b,some a]++beforeOutput} := by
      cases rest <;> simp [BinaryModularAddition.interleave,Tape.ofBits,Tape.moveRight]
    have time : 6*(((a,b),p)::rest).length+2 = 6+(6*rest.length+2) := by simp; omega
    rw [time,evalConfigWithin_add]
    simp only [eval_step _ _ current,PMF.pure_bind,outStep]
    convert ih input.moveLeft ([some p,some b,some a]++beforeOutput) using 1 <;>
      simp [BinaryModularAddition.interleave,List.reverse_cons,List.map_append,List.append_assoc,Function.iterate_succ_apply]

theorem runs (columns : List BinaryModularAddition.Column) (input : Tape) :
    ∃ used, used ≤ 6*columns.length+2 ∧
      RunsFor program
        ({inputTape := input,outputTape := Tape.ofBits (BinaryModularAddition.interleave columns)} : Configuration)
        ({pc := 6,inputTape := (Tape.moveLeft^[columns.length]) input,outputTape := {left := (BinaryModularAddition.interleave columns).reverse.map some},halted := true} : Configuration) used := by
  have ev := eval_columns columns input []
  have empty (bits : List Bool) : ({Tape.ofBits bits with left := []} : Tape) = Tape.ofBits bits := by
    cases bits <;> rfl
  rw [empty,List.append_nil] at ev
  dsimp only [state,finish] at ev
  have member : ({pc := 6,inputTape := (Tape.moveLeft^[columns.length]) input,outputTape := {left := (BinaryModularAddition.interleave columns).reverse.map some},halted := true} : Configuration) ∈
      (evalConfigWithin program ({inputTape := input,outputTape := Tape.ofBits (BinaryModularAddition.interleave columns)} : Configuration) (6*columns.length+2)).support := by
    rw [ev]; simp
  exact ((mem_support_evalConfigWithin_iff _ _ _ _).mp member).toRunsFor_le

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

end Machine.MoveInputLeftByColumns
