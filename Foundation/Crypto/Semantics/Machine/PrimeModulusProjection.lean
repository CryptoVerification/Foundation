import Foundation.Crypto.Semantics.Machine.FramedInstanceCopy
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine.PrimeModulusProjection

/-- Project the first of three equal-width fields on the output tape.
The input tape carries the instance's unary frame header to count the width.
The first bit of the following element frame is temporarily erased and then
restored. This finite code has no arithmetic or whole-string instruction. -/
def program : Program :=
  [.erase .input, .moveLeft .input, .moveLeft .output,
   .branch .output 7 4 4,
   .moveLeft .input, .moveLeft .output, .jump 3,
   .moveLeft .input,
   .branch .input 16 16 9, .moveLeft .input,
   .branch .input 16 16 11, .moveLeft .input,
   .branch .input 16 16 13, .moveLeft .input,
   .moveRight .output, .jump 8,
   .moveRight .output,
   .branch .output 21 18 18, .erase .output,
   .moveRight .output, .jump 17,
   .branch .input 24 22 22, .moveRight .input, .jump 21,
   .write .input true, .halt]

private def rewindState (input output : Tape) : Configuration :=
  { pc := 3, inputTape := input, outputTape := output }

private theorem mark_steps (input output : Tape) :
    RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
      (rewindState (input.write none).moveLeft output.moveLeft) 3 := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let marked : Configuration :=
    { start with pc := 1, inputTape := input.write none }
  let movedInput : Configuration :=
    { marked with pc := 2, inputTape := (input.write none).moveLeft }
  have hMark : Step program start marked := by
    simp [Step, successors, next, program, start, marked,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hInput : Step program marked movedInput := by
    simp [Step, successors, next, program, start, marked, movedInput,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hOutput : Step program movedInput
      (rewindState (input.write none).moveLeft output.moveLeft) := by
    simp [Step, successors, next, program, start, marked, movedInput,
      rewindState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.zero _) hMark) hInput) hOutput

private def rewindTape : Tape → Nat → Tape
  | tape, 0 => tape
  | tape, count + 1 => rewindTape tape.moveLeft count

private theorem rewindTape_prefix (prefixCells : List (Option Bool))
    (marker : Option Bool) (before right : List (Option Bool))
    (current : Option Bool) :
    rewindTape
      { left := prefixCells ++ marker :: before, current := current, right := right }
      (prefixCells.length + 1) =
      { left := before, current := marker,
        right := prefixCells.reverse ++ current :: right } := by
  induction prefixCells generalizing current right with
  | nil => simp [rewindTape, Tape.moveLeft]
  | cons cell prefixCells ih =>
      simpa [rewindTape, Tape.moveLeft, List.reverse_cons, List.append_assoc]
        using ih (current :: right) cell

private theorem rewind_one (input output : Tape) (bit : Bool)
    (hCurrent : output.current = some bit) :
    RunsFor program (rewindState input output)
      (rewindState input.moveLeft output.moveLeft) 4 := by
  let start := rewindState input output
  let selected : Configuration := { start with pc := 4 }
  let movedInput : Configuration :=
    { selected with pc := 5, inputTape := input.moveLeft }
  let movedOutput : Configuration :=
    { movedInput with pc := 6, outputTape := output.moveLeft }
  have hBranch : Step program start selected := by
    cases bit <;>
      simp [Step, successors, next, program, start, selected,
        rewindState, hCurrent, Instruction.next, Configuration.tape]
  have hInput : Step program selected movedInput := by
    simp [Step, successors, next, program, start, selected, movedInput,
      rewindState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hOutput : Step program movedInput movedOutput := by
    simp [Step, successors, next, program, start, selected, movedInput,
      movedOutput, rewindState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hJump : Step program movedOutput
      (rewindState input.moveLeft output.moveLeft) := by
    simp [Step, successors, next, program, start, selected, movedInput,
      movedOutput, rewindState, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.zero _) hBranch) hInput) hOutput) hJump

private theorem rewind_end (input output : Tape)
    (hBlank : output.current = none) :
    RunsFor program (rewindState input output)
      { rewindState input output with pc := 7 } 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  simp [Step, successors, next, program, rewindState,
    hBlank, Instruction.next, Configuration.tape]

/-- The first backward scan terminates even when the copied tape has no
expected delimiter. The head reaches a blank after the finite stored prefix. -/
private theorem rewind_any (input output : Tape) :
    ∃ finalInput finalOutput used,
      used ≤ 4 * (output.left.length + 2) + 1 ∧
      RunsFor program (rewindState input output)
        { pc := 7, inputTape := finalInput, outputTape := finalOutput } used := by
  cases hCurrent : output.current with
  | none =>
      refine ⟨input, output, 1, ?_, ?_⟩
      · omega
      · exact rewind_end input output hCurrent
  | some bit =>
      have first := rewind_one input output bit hCurrent
      cases hLeft : output.left with
      | nil =>
          have hBlank : output.moveLeft.current = none := by
            simp [Tape.moveLeft, hLeft]
          have second := rewind_end input.moveLeft output.moveLeft hBlank
          refine ⟨input.moveLeft, output.moveLeft, 5, ?_, first.trans second⟩
          simp
      | cons cell rest =>
          obtain ⟨finalInput, finalOutput, used, hUsed, run⟩ :=
            rewind_any input.moveLeft output.moveLeft
          refine ⟨finalInput, finalOutput, 4 + used, ?_, first.trans run⟩
          simp [Tape.moveLeft, hLeft] at hUsed
          simp
          omega
termination_by output.left.length
decreasing_by simp [Tape.moveLeft, hLeft]

private theorem rewind_run (input output : Tape) (remaining : List Bool)
    (before : List (Option Bool))
    (hCurrent : output.current = remaining.head?)
    (hLeft : remaining ≠ [] →
      output.left = remaining.tail.map some ++ none :: before) :
    RunsFor program (rewindState input output)
      { rewindState (rewindTape input remaining.length)
          (rewindTape output remaining.length) with pc := 7 }
      (4 * remaining.length + 1) := by
  induction remaining generalizing input output with
  | nil =>
      simpa [rewindTape] using rewind_end input output (by simpa using hCurrent)
  | cons bit remaining ih =>
      have first : RunsFor program (rewindState input output)
          (rewindState input.moveLeft output.moveLeft) 4 :=
        rewind_one input output bit (by simpa using hCurrent)
      have hNextCurrent : output.moveLeft.current =
          remaining.head? := by
        cases remaining <;>
          simp [Tape.moveLeft, hLeft (by simp)]
      have hNextLeft : remaining ≠ [] → output.moveLeft.left =
          remaining.tail.map some ++ none :: before := by
        intro hNe
        cases remaining <;>
          simp_all [Tape.moveLeft, hLeft (by simp)]
      have tail := ih input.moveLeft output.moveLeft hNextCurrent hNextLeft
      simpa [rewindTape, List.length_cons, Nat.mul_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first.trans tail

private theorem rewind_from_copy (input : Tape) (bits : List Bool) :
    let output : Tape := { left := bits.reverse.map some ++ [none] }
    RunsFor program (rewindState input output.moveLeft)
      { rewindState (rewindTape input bits.length)
          (rewindTape output.moveLeft bits.length) with pc := 7 }
      (4 * bits.length + 1) := by
  dsimp only
  let output : Tape := { left := bits.reverse.map some ++ [none] }
  have hCurrent : output.moveLeft.current = bits.reverse.head? := by
    cases h : bits.reverse <;> simp [output, Tape.moveLeft, h]
  have hLeft : bits.reverse ≠ [] →
      output.moveLeft.left = bits.reverse.tail.map some ++ [none] := by
    intro hNe
    cases h : bits.reverse with
    | nil => exact (hNe h).elim
    | cons bit rest => simp [output, Tape.moveLeft, h]
  simpa only [List.length_reverse] using
    rewind_run input output.moveLeft bits.reverse [] hCurrent hLeft

private theorem rewind_output_layout (bits : List Bool) :
    rewindTape
      ({ left := bits.reverse.map some ++ [none] } : Tape).moveLeft
      bits.length =
      { right := bits.map some ++ [none] } := by
  cases h : bits.reverse with
  | nil =>
      have hBits : bits = [] := by
        have := congrArg List.reverse h
        simpa using this.symm
      subst bits
      rfl
  | cons bit rest =>
      have hBits : bits = rest.reverse ++ [bit] := by
        have := congrArg List.reverse h
        simpa using this
      have hRewind := rewindTape_prefix (rest.map some) none [] [none] (some bit)
      simpa [h, hBits, Tape.moveLeft, List.map_reverse,
        List.append_assoc] using hRewind

private theorem rewind_input_layout (input : Tape) (bits : List Bool)
    (before : List (Option Bool))
    (hLeft : input.left = bits.reverse.map some ++ some false :: before) :
    rewindTape (input.write none).moveLeft bits.length =
      { left := before, current := some false,
        right := bits.map some ++ none :: input.right } := by
  cases h : bits.reverse with
  | nil =>
      have hBits : bits = [] := by
        have := congrArg List.reverse h
        simpa using this.symm
      subst bits
      simp [rewindTape, Tape.moveLeft, Tape.write, hLeft]
  | cons bit rest =>
      have hBits : bits = rest.reverse ++ [bit] := by
        have := congrArg List.reverse h
        simpa using this
      have hRewind := rewindTape_prefix (rest.map some) (some false)
        before (none :: input.right) (some bit)
      simpa [h, hBits, Tape.moveLeft, Tape.write, hLeft,
        List.map_reverse, List.append_assoc] using hRewind

private def validRewindInput (input : Tape) (bits : List Bool)
    (before : List (Option Bool)) : Tape :=
  { left := before, current := some false,
    right := bits.map some ++ none :: input.right }

private def validRewindOutput (bits : List Bool) : Tape :=
  { right := bits.map some ++ [none] }

private def validRewindFinish (input : Tape) (bits : List Bool)
    (before : List (Option Bool)) : Configuration :=
  { pc := 7, inputTape := validRewindInput input bits before,
    outputTape := validRewindOutput bits }

/-- The native marker and rewind recover the instance's leading delimiter
and expose the copied payload on the output tape, without a tape reset. -/
theorem rewinds_valid (input : Tape) (bits : List Bool)
    (before : List (Option Bool))
    (hLeft : input.left = bits.reverse.map some ++ some false :: before) :
    RunsFor program
      ({ inputTape := input,
         outputTape := { left := bits.reverse.map some ++ [none] } } : Configuration)
      (validRewindFinish input bits before)
      (3 + (4 * bits.length + 1)) := by
  let output : Tape := { left := bits.reverse.map some ++ [none] }
  have first := mark_steps input output
  have tail := rewind_from_copy (input.write none).moveLeft bits
  have hInput := rewind_input_layout input bits before hLeft
  have hOutput := rewind_output_layout bits
  change RunsFor program (rewindState (input.write none).moveLeft output.moveLeft)
    { pc := 7,
      inputTape := rewindTape (input.write none).moveLeft bits.length,
      outputTape := rewindTape output.moveLeft bits.length }
    (4 * bits.length + 1) at tail
  rw [hInput] at tail
  have hOutput' : rewindTape output.moveLeft bits.length =
      validRewindOutput bits := hOutput
  rw [hOutput'] at tail
  simpa [output, rewindState, validRewindFinish, validRewindInput] using first.trans tail

private def headerTape (remaining passed : Nat)
    (before payload : List (Option Bool)) : Tape :=
  match remaining with
  | 0 =>
      { left := before, current := some false,
        right := List.replicate (3 * passed) (some true) ++ payload }
  | count + 1 =>
      { left := List.replicate (3 * count + 2) (some true) ++ some false :: before,
        current := some true,
        right := List.replicate (3 * passed) (some true) ++ payload }

private def headerState (remaining passed : Nat)
    (before payload : List (Option Bool)) (output : Tape) : Configuration :=
  { pc := 8, inputTape := headerTape remaining passed before payload,
    outputTape := output }

private theorem headerTape_three_left (remaining passed : Nat)
    (before payload : List (Option Bool)) :
    ((headerTape (remaining + 1) passed before payload).moveLeft.moveLeft.moveLeft) =
      headerTape remaining (passed + 1) before payload := by
  cases remaining with
  | zero =>
      simp [headerTape, Tape.moveLeft, List.replicate_succ,
        Nat.mul_succ]
  | succ remaining =>
      simp [headerTape, Tape.moveLeft, List.replicate_succ,
        Nat.mul_succ, List.replicate_add, Nat.add_comm]

private theorem header_one (remaining passed : Nat)
    (before payload : List (Option Bool)) (output : Tape) :
    RunsFor program (headerState (remaining + 1) passed before payload output)
      (headerState remaining (passed + 1) before payload output.moveRight) 8 := by
  let input := headerTape (remaining + 1) passed before payload
  let start := headerState (remaining + 1) passed before payload output
  let c9 : Configuration := { start with pc := 9 }
  let c10 : Configuration := { c9 with pc := 10, inputTape := input.moveLeft }
  let c11 : Configuration := { c10 with pc := 11 }
  let c12 : Configuration :=
    { c11 with pc := 12, inputTape := input.moveLeft.moveLeft }
  let c13 : Configuration := { c12 with pc := 13 }
  let c14 : Configuration :=
    { c13 with pc := 14, inputTape := input.moveLeft.moveLeft.moveLeft }
  let c15 : Configuration :=
    { c14 with pc := 15, outputTape := output.moveRight }
  have h8 : Step program start c9 := by
    simp [Step, successors, next, program, start, c9, headerState,
      headerTape, Instruction.next, Configuration.tape]
  have h9 : Step program c9 c10 := by
    simp [Step, successors, next, program, start, c9, c10,
      headerState, input, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have h10 : Step program c10 c11 := by
    simp [Step, successors, next, program, start, c9, c10, c11,
      headerState, headerTape, input, Tape.moveLeft, List.replicate_succ,
      Instruction.next, Configuration.tape]
  have h11 : Step program c11 c12 := by
    simp [Step, successors, next, program, start, c9, c10, c11, c12,
      headerState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h12 : Step program c12 c13 := by
    simp [Step, successors, next, program, start, c9, c10, c11, c12, c13,
      headerState, headerTape, input, Tape.moveLeft, List.replicate_succ,
      Instruction.next, Configuration.tape]
  have h13 : Step program c13 c14 := by
    simp [Step, successors, next, program, start, c9, c10, c11, c12, c13, c14,
      headerState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h14 : Step program c14 c15 := by
    simp [Step, successors, next, program, start, c9, c10, c11, c12, c13, c14, c15,
      headerState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h15 : Step program c15
      (headerState remaining (passed + 1) before payload output.moveRight) := by
    simp [Step, successors, next, program, start, c9, c10, c11, c12,
      c13, c14, c15, headerState, input, headerTape_three_left,
      Instruction.next]
  exact ((((((((RunsFor.zero _).succ h8).succ h9).succ h10).succ h11).succ h12)
    |>.succ h13).succ h14).succ h15

private def headerAnyState (input output : Tape) : Configuration :=
  { pc := 8, inputTape := input, outputTape := output }

private theorem header_begin_any (input output : Tape) :
    RunsFor program
      ({ pc := 7, inputTape := input, outputTape := output } : Configuration)
      (headerAnyState input.moveLeft output) 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  simp [Step, successors, next, program, headerAnyState,
    Instruction.next, Configuration.updateTape, Configuration.advance]

private theorem header_exit (input output : Tape)
    (h : input.current ≠ some true) :
    RunsFor program (headerAnyState input output)
      { headerAnyState input output with pc := 16 } 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  cases hc : input.current with
  | none =>
      simp [Step, successors, next, program, headerAnyState,
        hc, Instruction.next, Configuration.tape]
  | some bit =>
      cases bit <;>
        simp_all [Step, successors, next, program, headerAnyState,
          Instruction.next, Configuration.tape]

private theorem header_exit_one (input output : Tape)
    (h0 : input.current = some true)
    (h1 : input.moveLeft.current ≠ some true) :
    RunsFor program (headerAnyState input output)
      { headerAnyState input.moveLeft output with pc := 16 } 3 := by
  let start := headerAnyState input output
  let c9 : Configuration := { start with pc := 9 }
  let c10 : Configuration := { start with pc := 10, inputTape := input.moveLeft }
  have first : Step program start c9 := by
    simp [Step, successors, next, program, start, c9, headerAnyState,
      h0, Instruction.next, Configuration.tape]
  have second : Step program c9 c10 := by
    simp [Step, successors, next, program, start, c9, c10, headerAnyState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have third : Step program c10
      { headerAnyState input.moveLeft output with pc := 16 } := by
    cases hc : input.moveLeft.current with
    | none =>
        simp [Step, successors, next, program, start, c9, c10,
          headerAnyState, hc, Instruction.next, Configuration.tape]
    | some bit =>
        cases bit <;>
          simp_all [Step, successors, next, program, start, c9, c10,
            headerAnyState, Instruction.next, Configuration.tape]
  exact (((RunsFor.zero _).succ first).succ second).succ third

private theorem header_exit_two (input output : Tape)
    (h0 : input.current = some true)
    (h1 : input.moveLeft.current = some true)
    (h2 : input.moveLeft.moveLeft.current ≠ some true) :
    RunsFor program (headerAnyState input output)
      { headerAnyState input.moveLeft.moveLeft output with pc := 16 } 5 := by
  let start := headerAnyState input output
  let c9 : Configuration := { start with pc := 9 }
  let c10 : Configuration := { start with pc := 10, inputTape := input.moveLeft }
  let c11 : Configuration := { start with pc := 11, inputTape := input.moveLeft }
  let c12 : Configuration :=
    { start with pc := 12, inputTape := input.moveLeft.moveLeft }
  have s8 : Step program start c9 := by
    simp [Step, successors, next, program, start, c9, headerAnyState,
      h0, Instruction.next, Configuration.tape]
  have s9 : Step program c9 c10 := by
    simp [Step, successors, next, program, start, c9, c10, headerAnyState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have s10 : Step program c10 c11 := by
    simp [Step, successors, next, program, start, c9, c10, c11,
      headerAnyState, h1, Instruction.next, Configuration.tape]
  have s11 : Step program c11 c12 := by
    simp [Step, successors, next, program, start, c9, c10, c11, c12,
      headerAnyState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have s12 : Step program c12
      { headerAnyState input.moveLeft.moveLeft output with pc := 16 } := by
    cases hc : input.moveLeft.moveLeft.current with
    | none =>
        simp [Step, successors, next, program, start, c9, c10, c11, c12,
          headerAnyState, hc, Instruction.next, Configuration.tape]
    | some bit =>
        cases bit <;>
          simp_all [Step, successors, next, program, start, c9, c10, c11, c12,
            headerAnyState, Instruction.next, Configuration.tape]
  exact (((((RunsFor.zero _).succ s8).succ s9).succ s10).succ s11).succ s12

private theorem header_continue (input output : Tape)
    (h0 : input.current = some true)
    (h1 : input.moveLeft.current = some true)
    (h2 : input.moveLeft.moveLeft.current = some true) :
    RunsFor program (headerAnyState input output)
      (headerAnyState input.moveLeft.moveLeft.moveLeft output.moveRight) 8 := by
  let start := headerAnyState input output
  let c9 : Configuration := { start with pc := 9 }
  let c10 : Configuration := { start with pc := 10, inputTape := input.moveLeft }
  let c11 : Configuration := { start with pc := 11, inputTape := input.moveLeft }
  let c12 : Configuration :=
    { start with pc := 12, inputTape := input.moveLeft.moveLeft }
  let c13 : Configuration :=
    { start with pc := 13, inputTape := input.moveLeft.moveLeft }
  let c14 : Configuration :=
    { start with pc := 14, inputTape := input.moveLeft.moveLeft.moveLeft }
  let c15 : Configuration :=
    { c14 with pc := 15, outputTape := output.moveRight }
  have s8 : Step program start c9 := by
    simp [Step, successors, next, program, start, c9, headerAnyState,
      h0, Instruction.next, Configuration.tape]
  have s9 : Step program c9 c10 := by
    simp [Step, successors, next, program, start, c9, c10, headerAnyState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have s10 : Step program c10 c11 := by
    simp [Step, successors, next, program, start, c9, c10, c11,
      headerAnyState, h1, Instruction.next, Configuration.tape]
  have s11 : Step program c11 c12 := by
    simp [Step, successors, next, program, start, c9, c10, c11, c12,
      headerAnyState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have s12 : Step program c12 c13 := by
    simp [Step, successors, next, program, start, c9, c10, c11, c12, c13,
      headerAnyState, h2, Instruction.next, Configuration.tape]
  have s13 : Step program c13 c14 := by
    simp [Step, successors, next, program, start, c9, c10, c11, c12, c13, c14,
      headerAnyState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have s14 : Step program c14 c15 := by
    simp [Step, successors, next, program, start, c9, c10, c11, c12, c13, c14, c15,
      headerAnyState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have s15 : Step program c15
      (headerAnyState input.moveLeft.moveLeft.moveLeft output.moveRight) := by
    simp [Step, successors, next, program, start, c9, c10, c11, c12, c13, c14, c15,
      headerAnyState, Instruction.next]
  exact ((((((((RunsFor.zero _).succ s8).succ s9).succ s10).succ s11).succ s12)
    |>.succ s13).succ s14).succ s15

/-- The three-bit width counter also terminates for malformed stored tape
contents. Every full iteration moves the input head left at least two cells. -/
private theorem header_any (input output : Tape) :
    ∃ finalInput finalOutput used,
      used ≤ 8 * (input.left.length + 2) + 1 ∧
      RunsFor program (headerAnyState input output)
        { pc := 16, inputTape := finalInput, outputTape := finalOutput } used := by
  by_cases h0 : input.current = some true
  · by_cases h1 : input.moveLeft.current = some true
    · by_cases h2 : input.moveLeft.moveLeft.current = some true
      · have first := header_continue input output h0 h1 h2
        have hDecrease :
            (input.moveLeft.moveLeft.moveLeft).left.length < input.left.length := by
          cases hLeft : input.left with
          | nil => simp [Tape.moveLeft, hLeft] at h1
          | cons first rest =>
              cases hRest : rest with
              | nil => simp [Tape.moveLeft, hLeft, hRest] at h2
              | cons second tail =>
                  cases tail <;> simp [Tape.moveLeft, hLeft, hRest] <;> omega
        obtain ⟨finalInput, finalOutput, used, hUsed, run⟩ :=
          header_any input.moveLeft.moveLeft.moveLeft output.moveRight
        refine ⟨finalInput, finalOutput, 8 + used, ?_, first.trans run⟩
        omega
      · refine ⟨input.moveLeft.moveLeft, output, 5, ?_,
          header_exit_two input output h0 h1 h2⟩
        omega
    · refine ⟨input.moveLeft, output, 3, ?_, header_exit_one input output h0 h1⟩
      omega
  · refine ⟨input, output, 1, ?_, header_exit input output h0⟩
    omega
termination_by input.left.length
decreasing_by assumption

private def moveRightN : Tape → Nat → Tape
  | tape, 0 => tape
  | tape, count + 1 => moveRightN tape.moveRight count

private def movedAcross (passed : List Bool) (before right : List (Option Bool))
    (marker : Option Bool) : Tape :=
  match passed.reverse with
  | [] => { left := before, current := marker, right := right }
  | bit :: earlier =>
      { left := earlier.map some ++ marker :: before,
        current := some bit, right := right }

private theorem movedAcross_cons (bit : Bool) (passed : List Bool)
    (before right : List (Option Bool)) (marker : Option Bool) :
    movedAcross (bit :: passed) before right marker =
      movedAcross passed (marker :: before) right (some bit) := by
  cases h : passed.reverse with
  | nil => simp [movedAcross, List.reverse_cons, h]
  | cons last earlier =>
      simp [movedAcross, List.reverse_cons, h, List.map_append,
        List.append_assoc]

private theorem moveRightN_prefix (passed : List Bool)
    (before right : List (Option Bool)) (marker : Option Bool) :
    moveRightN
      { left := before, current := marker,
        right := passed.map some ++ right }
      passed.length = movedAcross passed before right marker := by
  induction passed generalizing before marker with
  | nil => rfl
  | cons bit passed ih =>
      have h := ih (marker :: before) (some bit)
      simpa [moveRightN, Tape.moveRight, movedAcross_cons] using h

private theorem header_end (passed : Nat)
    (before payload : List (Option Bool)) (output : Tape) :
    RunsFor program (headerState 0 passed before payload output)
      { headerState 0 passed before payload output with pc := 16 } 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  simp [Step, successors, next, program, headerState, headerTape,
    Instruction.next, Configuration.tape]

private theorem header_run (remaining passed : Nat)
    (before payload : List (Option Bool)) (output : Tape) :
    RunsFor program (headerState remaining passed before payload output)
      { headerState 0 (passed + remaining) before payload
          (moveRightN output remaining) with pc := 16 }
      (8 * remaining + 1) := by
  induction remaining generalizing passed output with
  | zero => simpa [moveRightN] using header_end passed before payload output
  | succ remaining ih =>
      have first := header_one remaining passed before payload output
      have tail := ih (passed + 1) output.moveRight
      have hPassed : passed + 1 + remaining = passed + (remaining + 1) := by omega
      rw [hPassed] at tail
      simpa [moveRightN, Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using first.trans tail

private theorem header_begin (input : Tape) (bits : List Bool)
    (width : Nat) (before : List (Option Bool))
    (hLength : bits.length = 3 * width) :
    RunsFor program
      (validRewindFinish input bits
        (List.replicate bits.length (some true) ++ some false :: before))
      (headerState width 0 before
        (some false :: bits.map some ++ none :: input.right)
        (validRewindOutput bits)) 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  cases width with
  | zero =>
      have hEmpty : bits = [] := List.length_eq_zero_iff.mp (by omega)
      subst bits
      simp [Step, successors, next, program, validRewindFinish,
        validRewindInput, validRewindOutput, headerState, headerTape,
        Tape.moveLeft, Instruction.next, Configuration.updateTape,
        Configuration.advance]
  | succ width =>
      simp [Step, successors, next, program, validRewindFinish,
        validRewindInput, validRewindOutput, headerState, headerTape,
        Tape.moveLeft, hLength, Nat.mul_succ, List.replicate_succ,
        Instruction.next, Configuration.updateTape, Configuration.advance]

private def eraseState (input output : Tape) : Configuration :=
  { pc := 17, inputTape := input, outputTape := output }

private def eraseTape : Tape → Nat → Tape
  | tape, 0 => tape
  | tape, count + 1 => eraseTape (tape.write none).moveRight count

private theorem erase_begin (input output : Tape) :
    RunsFor program
      ({ pc := 16, inputTape := input, outputTape := output } : Configuration)
      (eraseState input output.moveRight) 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  simp [Step, successors, next, program, eraseState,
    Instruction.next, Configuration.updateTape, Configuration.advance]

private theorem erase_one (input output : Tape) (bit : Bool)
    (hCurrent : output.current = some bit) :
    RunsFor program (eraseState input output)
      (eraseState input (output.write none).moveRight) 4 := by
  let start := eraseState input output
  let c18 : Configuration := { start with pc := 18 }
  let c19 : Configuration :=
    { c18 with pc := 19, outputTape := output.write none }
  let c20 : Configuration :=
    { c19 with pc := 20, outputTape := (output.write none).moveRight }
  have h17 : Step program start c18 := by
    cases bit <;>
      simp [Step, successors, next, program, start, c18,
        eraseState, hCurrent, Instruction.next, Configuration.tape]
  have h18 : Step program c18 c19 := by
    simp [Step, successors, next, program, start, c18, c19,
      eraseState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have h19 : Step program c19 c20 := by
    simp [Step, successors, next, program, start, c18, c19, c20,
      eraseState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have h20 : Step program c20
      (eraseState input (output.write none).moveRight) := by
    simp [Step, successors, next, program, start, c18, c19, c20,
      eraseState, Instruction.next]
  exact (((RunsFor.zero _).succ h17).succ h18).succ h19 |>.succ h20

private theorem erase_end (input output : Tape)
    (hBlank : output.current = none) :
    RunsFor program (eraseState input output)
      { eraseState input output with pc := 21 } 1 := by
  apply RunsFor.succ (RunsFor.zero _)
  simp [Step, successors, next, program, eraseState,
    hBlank, Instruction.next, Configuration.tape]

/-- The forward erasure scan stops at a blank, including one synthesized
beyond the finite represented output tape. -/
private theorem erase_any (input output : Tape) :
    ∃ finalInput finalOutput used,
      used ≤ 4 * (output.right.length + 2) + 1 ∧
      RunsFor program (eraseState input output)
        { pc := 21, inputTape := finalInput, outputTape := finalOutput } used := by
  cases hCurrent : output.current with
  | none =>
      refine ⟨input, output, 1, ?_, ?_⟩
      · omega
      · exact erase_end input output hCurrent
  | some bit =>
      have first := erase_one input output bit hCurrent
      cases hRight : output.right with
      | nil =>
          have hBlank : (output.write none).moveRight.current = none := by
            simp [Tape.moveRight, Tape.write, hRight]
          have second := erase_end input (output.write none).moveRight hBlank
          refine ⟨input, (output.write none).moveRight, 5, ?_, first.trans second⟩
          simp
      | cons cell rest =>
          obtain ⟨finalInput, finalOutput, used, hUsed, run⟩ :=
            erase_any input (output.write none).moveRight
          refine ⟨finalInput, finalOutput, 4 + used, ?_, first.trans run⟩
          simp [Tape.moveRight, Tape.write, hRight] at hUsed
          simp
          omega
termination_by output.right.length
decreasing_by simp [Tape.moveRight, Tape.write, hRight]

private theorem erase_run (input output : Tape) (remaining : List Bool)
    (hCurrent : output.current = remaining.head?)
    (hRight : remaining ≠ [] →
      output.right = remaining.tail.map some ++ [none]) :
    RunsFor program (eraseState input output)
      { eraseState input (eraseTape output remaining.length) with pc := 21 }
      (4 * remaining.length + 1) := by
  induction remaining generalizing output with
  | nil => simpa [eraseTape] using erase_end input output (by simpa using hCurrent)
  | cons bit remaining ih =>
      have first := erase_one input output bit (by simpa using hCurrent)
      have hNextCurrent : (output.write none).moveRight.current =
          remaining.head? := by
        cases remaining <;> simp [Tape.moveRight, Tape.write, hRight (by simp)]
      have hNextRight : remaining ≠ [] →
          (output.write none).moveRight.right =
            remaining.tail.map some ++ [none] := by
        intro hNe
        cases remaining <;> simp_all [Tape.moveRight, Tape.write, hRight (by simp)]
      have tail := ih (output.write none).moveRight hNextCurrent hNextRight
      simpa [eraseTape, List.length_cons, Nat.mul_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using first.trans tail

private def eraseStart (remaining : List Bool)
    (before : List (Option Bool)) : Tape :=
  match remaining with
  | [] => { left := before }
  | bit :: rest =>
      { left := before, current := some bit,
        right := rest.map some ++ [none] }

private theorem eraseStart_step (bit : Bool) (rest : List Bool)
    (before : List (Option Bool)) :
    ((eraseStart (bit :: rest) before).write none).moveRight =
      eraseStart rest (none :: before) := by
  cases rest <;> simp [eraseStart, Tape.write, Tape.moveRight]

private theorem eraseTape_layout (remaining : List Bool)
    (before : List (Option Bool)) :
    eraseTape (eraseStart remaining before) remaining.length =
      { left := List.replicate remaining.length none ++ before } := by
  induction remaining generalizing before with
  | nil => rfl
  | cons bit remaining ih =>
      calc
        eraseTape (eraseStart (bit :: remaining) before)
            (bit :: remaining).length =
            eraseTape (eraseStart remaining (none :: before)) remaining.length := by
              simp [eraseTape, eraseStart_step]
        _ = { left := List.replicate remaining.length none ++ none :: before } :=
          ih (none :: before)
        _ = { left := List.replicate (bit :: remaining).length none ++ before } := by
          simp [List.replicate_add, List.append_assoc]

private theorem movedAcross_to_eraseStart (first rest : List Bool) :
    (movedAcross first [] (rest.map some ++ [none]) none).moveRight =
      eraseStart rest (first.reverse.map some ++ [none]) := by
  cases hFirst : first.reverse with
  | nil =>
      have hEmpty : first = [] := by
        have := congrArg List.reverse hFirst
        simpa using this.symm
      subst first
      cases rest <;>
        simp [movedAcross, eraseStart, Tape.moveRight]
  | cons last earlier =>
      cases rest <;>
        simp [movedAcross, eraseStart, Tape.moveRight, hFirst]

/-- Starting at the first field of three fixed-width fields, the native
erase scan leaves precisely the first field's bits on the output tape. -/
theorem erase_trailing_fields (input : Tape) (modulus trailing : List Bool) :
    RunsFor program
      ({ pc := 16, inputTape := input,
         outputTape := moveRightN
           ({ right := (modulus ++ trailing).map some ++ [none] } : Tape)
           modulus.length } : Configuration)
      ({ pc := 21, inputTape := input,
         outputTape := { left := List.replicate trailing.length none ++
           modulus.reverse.map some ++ [none] } } : Configuration)
      (1 + (4 * trailing.length + 1)) := by
  have hPosition := moveRightN_prefix modulus [] (trailing.map some ++ [none]) none
  have hStart : moveRightN
      ({ right := (modulus ++ trailing).map some ++ [none] } : Tape)
      modulus.length = movedAcross modulus [] (trailing.map some ++ [none]) none := by
    simpa [List.map_append, List.append_assoc] using hPosition
  rw [hStart]
  have hErased := erase_begin input
    (movedAcross modulus [] (trailing.map some ++ [none]) none)
  rw [movedAcross_to_eraseStart] at hErased
  have hCurrent : (eraseStart trailing (modulus.reverse.map some ++ [none])).current =
      trailing.head? := by cases trailing <;> rfl
  have hRight : trailing ≠ [] →
      (eraseStart trailing (modulus.reverse.map some ++ [none])).right =
        trailing.tail.map some ++ [none] := by
    intro hNe
    cases trailing with
    | nil => exact (hNe rfl).elim
    | cons _ _ => rfl
  have hRun := erase_run input
    (eraseStart trailing (modulus.reverse.map some ++ [none])) trailing
    hCurrent hRight
  rw [eraseTape_layout] at hRun
  simpa [eraseState] using hErased.trans hRun

theorem erased_output_bits (modulus trailing : List Bool) :
    ({ left := List.replicate trailing.length none ++
        modulus.reverse.map some ++ [none] } : Tape).bits = modulus := by
  simp [Tape.bits, List.reverse_append, List.map_reverse,
    List.append_assoc]

private def forwardState (input output : Tape) : Configuration :=
  { pc := 21, inputTape := input, outputTape := output }

private def forwardTape : Tape → Nat → Tape
  | tape, 0 => tape
  | tape, count + 1 => forwardTape tape.moveRight count

private theorem forward_one (input output : Tape) (bit : Bool)
    (hCurrent : input.current = some bit) :
    RunsFor program (forwardState input output)
      (forwardState input.moveRight output) 3 := by
  let start := forwardState input output
  let c22 : Configuration := { start with pc := 22 }
  let c23 : Configuration :=
    { c22 with pc := 23, inputTape := input.moveRight }
  have h21 : Step program start c22 := by
    cases bit <;> simp [Step, successors, next, program, start, c22,
      forwardState, hCurrent, Instruction.next, Configuration.tape]
  have h22 : Step program c22 c23 := by
    simp [Step, successors, next, program, start, c22, c23,
      forwardState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have h23 : Step program c23 (forwardState input.moveRight output) := by
    simp [Step, successors, next, program, start, c22, c23,
      forwardState, Instruction.next]
  exact (((RunsFor.zero _).succ h21).succ h22).succ h23

private theorem forward_end (input output : Tape)
    (hBlank : input.current = none) :
    RunsFor program (forwardState input output)
      ({ pc := 25, halted := true,
         inputTape := input.write (some true), outputTape := output } : Configuration) 3 := by
  let start := forwardState input output
  let c24 : Configuration := { start with pc := 24 }
  let c25 : Configuration :=
    { c24 with pc := 25, inputTape := input.write (some true) }
  have h21 : Step program start c24 := by
    simp [Step, successors, next, program, start, c24, forwardState,
      hBlank, Instruction.next, Configuration.tape]
  have h24 : Step program c24 c25 := by
    simp [Step, successors, next, program, start, c24, c25,
      forwardState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have h25 : Step program c25 { c25 with halted := true } := by
    simp [Step, successors, next, program, start, c24, c25,
      forwardState, Instruction.next]
  exact (((RunsFor.zero _).succ h21).succ h24).succ h25

/-- Restoring the next input marker always reaches a blank after finitely
many stored cells, even if the copied instance frame was malformed. -/
private theorem forward_any (input output : Tape) :
    ∃ finish used, used ≤ 3 * (input.right.length + 2) + 3 ∧
      RunsFor program (forwardState input output) finish used ∧
      finish.halted = true := by
  cases hCurrent : input.current with
  | none =>
      refine ⟨_, 3, ?_, forward_end input output hCurrent, rfl⟩
      omega
  | some bit =>
      have first := forward_one input output bit hCurrent
      cases hRight : input.right with
      | nil =>
          have hBlank : input.moveRight.current = none := by
            simp [Tape.moveRight, hRight]
          have second := forward_end input.moveRight output hBlank
          refine ⟨_, 6, ?_, first.trans second, rfl⟩
          simp
      | cons cell rest =>
          obtain ⟨finish, used, hUsed, run, hHalt⟩ :=
            forward_any input.moveRight output
          refine ⟨finish, 3 + used, ?_, first.trans run, hHalt⟩
          simp [Tape.moveRight, hRight] at hUsed
          simp
          omega
termination_by input.right.length
decreasing_by simp [Tape.moveRight, hRight]

/-- Every finite two-tape configuration stops in the projector. This covers
malformed headers and absent separators as well as canonical frames. -/
theorem runs_any (input output : Tape) :
    ∃ finish used,
      used ≤ 10000 * (input.cells + output.cells + 1) ∧
      RunsFor program
        ({ inputTape := input, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let marked := rewindState (input.write none).moveLeft output.moveLeft
  have rMark : RunsFor program start marked 3 := mark_steps input output
  obtain ⟨in1, out1, u1, hu1, rRewind⟩ :=
    rewind_any (input.write none).moveLeft output.moveLeft
  let c1 : Configuration := { pc := 7, inputTape := in1, outputTape := out1 }
  have r1 : RunsFor program start c1 (3 + u1) := rMark.trans rRewind
  have rBegin := header_begin_any in1 out1
  obtain ⟨in2, out2, u2, hu2, rHeader⟩ :=
    header_any in1.moveLeft out1
  let c2 : Configuration := { pc := 16, inputTape := in2, outputTape := out2 }
  have r2 : RunsFor program start c2 (3 + u1 + 1 + u2) :=
    (r1.trans rBegin).trans rHeader
  have rEraseBegin := erase_begin in2 out2
  obtain ⟨in3, out3, u3, hu3, rErase⟩ :=
    erase_any in2 out2.moveRight
  let c3 : Configuration := { pc := 21, inputTape := in3, outputTape := out3 }
  have r3 : RunsFor program start c3 (3 + u1 + 1 + u2 + 1 + u3) :=
    (r2.trans rEraseBegin).trans rErase
  obtain ⟨finish, u4, hu4, rForward, hHalt⟩ := forward_any in3 out3
  have r4 : RunsFor program start finish
      (3 + u1 + 1 + u2 + 1 + u3 + u4) := r3.trans rForward
  have s1 := GuardedCompiler.sourceStorage_le_of_run r1
  have s2 := GuardedCompiler.sourceStorage_le_of_run r2
  have s3 := GuardedCompiler.sourceStorage_le_of_run r3
  refine ⟨finish, 3 + u1 + 1 + u2 + 1 + u3 + u4, ?_, r4, hHalt⟩
  change 3 + u1 + 1 + u2 + 1 + u3 + u4 ≤
    10000 * (input.cells + output.cells + 1)
  have hRewind : output.moveLeft.left.length ≤ output.cells + 1 := by
    have ho := Tape.cells_moveLeft_le output
    simp [Tape.cells] at *
    omega
  have hHeader : in1.moveLeft.left.length ≤ in1.cells + out1.cells + 1 := by
    have hi := Tape.cells_moveLeft_le in1
    simp [Tape.cells] at *
    omega
  have hErase : out2.moveRight.right.length ≤ in2.cells + out2.cells + 1 := by
    have ho := Tape.cells_moveRight_le out2
    simp [Tape.cells] at *
    omega
  have hForward : in3.right.length ≤ in3.cells + out3.cells := by
    simp [Tape.cells]
    omega
  change in1.cells + out1.cells ≤ input.cells + output.cells + (3 + u1) at s1
  change in2.cells + out2.cells ≤ input.cells + output.cells +
    (3 + u1 + 1 + u2) at s2
  change in3.cells + out3.cells ≤ input.cells + output.cells +
    (3 + u1 + 1 + u2 + 1 + u3) at s3
  omega

private theorem forward_run (input output : Tape) (remaining : List Bool)
    (after : List (Option Bool))
    (hCurrent : input.current = remaining.head?)
    (hRight : remaining ≠ [] →
      input.right = remaining.tail.map some ++ none :: after) :
    RunsFor program (forwardState input output)
      ({ pc := 25, halted := true,
         inputTape := (forwardTape input remaining.length).write (some true),
         outputTape := output } : Configuration)
      (3 * remaining.length + 3) := by
  induction remaining generalizing input with
  | nil => simpa [forwardTape] using
      forward_end input output (by simpa using hCurrent)
  | cons bit remaining ih =>
      have first := forward_one input output bit (by simpa using hCurrent)
      have hNextCurrent : input.moveRight.current = remaining.head? := by
        cases remaining <;> simp [Tape.moveRight, hRight (by simp)]
      have hNextRight : remaining ≠ [] →
          input.moveRight.right = remaining.tail.map some ++ none :: after := by
        intro hNe
        cases remaining <;> simp_all [Tape.moveRight, hRight (by simp)]
      have tail := ih input.moveRight hNextCurrent hNextRight
      simpa [forwardTape, List.length_cons, Nat.mul_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first.trans tail

private def forwardStart (remaining : List Bool) (before after : List (Option Bool)) :
    Tape :=
  match remaining with
  | [] => { left := before, right := after }
  | bit :: rest =>
      { left := before, current := some bit,
        right := rest.map some ++ none :: after }

private theorem forwardStart_step (bit : Bool) (rest : List Bool)
    (before after : List (Option Bool)) :
    (forwardStart (bit :: rest) before after).moveRight =
      forwardStart rest (some bit :: before) after := by
  cases rest <;> simp [forwardStart, Tape.moveRight]

private theorem forwardTape_layout (remaining : List Bool)
    (before after : List (Option Bool)) :
    forwardTape (forwardStart remaining before after) remaining.length =
      { left := remaining.reverse.map some ++ before,
        right := after } := by
  induction remaining generalizing before with
  | nil => rfl
  | cons bit remaining ih =>
      simpa [forwardTape, forwardStart_step, List.reverse_cons,
        List.map_append, List.append_assoc] using ih (some bit :: before)

private def forwardFinishTape (remaining : List Bool)
    (before after : List (Option Bool)) : Tape :=
  { left := remaining.reverse.map some ++ before,
    current := some true, right := after }

private def forwardFinish (remaining : List Bool)
    (before after : List (Option Bool)) (output : Tape) : Configuration :=
  { pc := 25, halted := true,
    inputTape := forwardFinishTape remaining before after,
    outputTape := output }

private theorem forward_from_start (remaining : List Bool)
    (before after : List (Option Bool)) (output : Tape) :
    RunsFor program
      (forwardState (forwardStart remaining before after) output)
      (forwardFinish remaining before after output)
      (3 * remaining.length + 3) := by
  have hCurrent : (forwardStart remaining before after).current =
      remaining.head? := by cases remaining <;> rfl
  have hRight : remaining ≠ [] →
      (forwardStart remaining before after).right =
        remaining.tail.map some ++ none :: after := by
    intro hNe
    cases remaining with
    | nil => exact (hNe rfl).elim
    | cons _ _ => rfl
  have run := forward_run (forwardStart remaining before after) output
    remaining after hCurrent hRight
  rw [forwardTape_layout] at run
  simpa [Tape.write, forwardFinish, forwardFinishTape] using run

private def forwardBits (width : Nat) (bits : List Bool) : List Bool :=
  false :: List.replicate (3 * width) true ++ false :: bits

private theorem header_end_is_forward_start (width : Nat) (bits : List Bool)
    (before after : List (Option Bool)) :
    headerTape 0 width before
      (some false :: bits.map some ++ none :: after) =
      forwardStart (forwardBits width bits) before after := by
  simp [headerTape, forwardStart, forwardBits,
    List.map_append, List.append_assoc]

/-- On a well-formed three-field instance code, the fixed finite projector
retains precisely the modulus field and restores the following frame head. -/
def budget (length : Nat) : Nat := 100 * (length + 1)

theorem runs_valid (input : Tape) (modulus second third : List Bool)
    (width : Nat) (before : List (Option Bool))
    (hModulus : modulus.length = width)
    (hSecond : second.length = width)
    (hThird : third.length = width)
    (hLeft : input.left =
      (modulus ++ second ++ third).reverse.map some ++ some false ::
        List.replicate (modulus ++ second ++ third).length (some true) ++
          some false :: before) :
    ∃ target used, used ≤ budget (modulus ++ second ++ third).length ∧
      RunsFor program
        ({ inputTape := input,
           outputTape := { left := (modulus ++ second ++ third).reverse.map some ++
             [none] } } : Configuration)
        target used ∧
      target.halted = true ∧
      target.inputTape =
        { left := (false :: List.replicate (3 * width) true ++
            false :: modulus ++ second ++ third).reverse.map some ++ before,
          current := some true, right := input.right } ∧
      target.outputTape =
        { left := List.replicate (second ++ third).length none ++
            modulus.reverse.map some ++ [none] } ∧
      target.outputBits = modulus ∧
      target.inputTape.current = some true := by
  let bits := modulus ++ second ++ third
  let tail := second ++ third
  let output : Tape :=
    { left := List.replicate tail.length none ++ modulus.reverse.map some ++ [none] }
  have hLength : bits.length = 3 * width := by
    simp [bits, List.length_append, hModulus, hSecond, hThird]
    omega
  have hLeft' : input.left = bits.reverse.map some ++ some false ::
      (List.replicate bits.length (some true) ++ some false :: before) := by
    simpa [bits, List.append_assoc] using hLeft
  have hRewind := rewinds_valid input bits
    (List.replicate bits.length (some true) ++ some false :: before) hLeft'
  have hHeaderStart := header_begin input bits width before hLength
  have hHeader := header_run width 0 before
    (some false :: bits.map some ++ none :: input.right)
    (validRewindOutput bits)
  have hErase := erase_trailing_fields
    (headerTape 0 width before
      (some false :: bits.map some ++ none :: input.right)) modulus tail
  have hOutput : validRewindOutput bits =
      { right := (modulus ++ tail).map some ++ [none] } := by
    simp [validRewindOutput, bits, tail, List.append_assoc]
  rw [hOutput] at hHeaderStart
  rw [hOutput] at hHeader
  simp only [Nat.zero_add] at hHeader
  rw [hModulus] at hErase
  -- The two stages share the same physical output head and program counter.
  have hJoined : RunsFor program
      (validRewindFinish input bits
        (List.replicate bits.length (some true) ++ some false :: before))
      ({ pc := 21,
         inputTape := headerTape 0 width before
           (some false :: bits.map some ++ none :: input.right),
         outputTape := output } : Configuration)
      (1 + (8 * width + 1) + (1 + (4 * tail.length + 1))) := by
    have stage := hHeaderStart.trans hHeader
    simpa [output, headerState, hModulus, Nat.zero_add] using stage.trans hErase
  have hForward := forward_from_start (forwardBits width bits) before
    input.right output
  have hForwardStart :
      forwardState
        (forwardStart (forwardBits width bits) before input.right) output =
      ({ pc := 21,
         inputTape := headerTape 0 width before
           (some false :: bits.map some ++ none :: input.right),
         outputTape := output } : Configuration) := by
    rw [header_end_is_forward_start]
    rfl
  rw [hForwardStart] at hForward
  let target := forwardFinish (forwardBits width bits) before input.right output
  refine ⟨target, 3 + (4 * bits.length + 1) +
    (1 + (8 * width + 1) + (1 + (4 * tail.length + 1))) +
    (3 * (forwardBits width bits).length + 3), ?_, ?_, rfl, ?_, rfl,
    ?_, rfl⟩
  · have hTail : tail.length = 2 * width := by
      simp [tail, List.length_append, hSecond, hThird]
      omega
    have hForwardLength : (forwardBits width bits).length =
        2 + 3 * width + bits.length := by
      simp [forwardBits]
      omega
    change 3 + (4 * bits.length + 1) +
      (1 + (8 * width + 1) + (1 + (4 * tail.length + 1))) +
      (3 * (forwardBits width bits).length + 3) ≤
        100 * (bits.length + 1)
    omega
  · simpa [target, bits] using (hRewind.trans hJoined).trans hForward
  · simp [target, forwardFinish, forwardFinishTape, forwardBits, bits,
      List.append_assoc]
  · simpa [target, forwardFinish, Configuration.outputBits, output, tail]
      using erased_output_bits modulus tail

private theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

/-- The evaluator of the same fixed code returns the modulus on a valid
three-field copied instance tape. All-input stopping is `runs_any`. -/
theorem eval_valid (input : Tape) (modulus second third : List Bool)
    (width : Nat) (before : List (Option Bool))
    (hModulus : modulus.length = width)
    (hSecond : second.length = width)
    (hThird : third.length = width)
    (hLeft : input.left =
      (modulus ++ second ++ third).reverse.map some ++ some false ::
        List.replicate (modulus ++ second ++ third).length (some true) ++
          some false :: before) :
    let start : Configuration :=
      { inputTape := input,
        outputTape := { left := (modulus ++ second ++ third).reverse.map some ++
          [none] } }
    (evalConfigWithin program start
      (budget (modulus ++ second ++ third).length)).map
        (fun c => if c.halted then some c.outputBits else none) =
      PMF.pure (some modulus) := by
  dsimp only
  obtain ⟨target, used, hUsed, run, hHalt, _, _, hOutput, _⟩ :=
    runs_valid input modulus second third width before
      hModulus hSecond hThird hLeft
  have hAll := run.haltsFrom_of_no_randomBit hHalt no_randomBit
    (Nat.le_refl used)
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hHalt, hOutput]

end Machine.PrimeModulusProjection
