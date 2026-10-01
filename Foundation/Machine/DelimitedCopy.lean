import Foundation.Machine.DelimitedOutput

namespace Machine

/-- Copy one already delimited field, including its terminating false bit.
Only native reads, writes, moves and jumps are used. The valid-field theorem
below retains all cells following the field, including arbitrary blanks. -/
def copyDelimited : Program :=
  [.branch .input 14 11 1,
   .write .output true, .moveRight .output, .moveRight .input,
   .branch .input 14 5 7,
   .write .output false, .jump 8, .write .output true,
   .moveRight .input, .moveRight .output, .jump 0,
   .write .output false, .moveRight .input, .moveRight .output, .halt]

/-- Copying a possibly malformed escaped field preserves the exact suffix
of retained input cells. Output writes do not alter those input cells. -/
theorem copyDelimited_input_right_suffix {start finish : Configuration} {used : Nat}
    (run : RunsFor copyDelimited start finish used) :
    ∃ count, finish.inputTape.right = start.inputTape.right.drop count := by
  apply run.input_right_suffix_of_step
  intro c d step
  have hActive : c.halted = false := by
    cases h : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted h) step)
  by_cases hPc : c.pc < 15
  · interval_cases hIndex : c.pc
    all_goals simp [Step, successors, next, hActive, hIndex, copyDelimited,
      Instruction.next, Configuration.tape] at step
    all_goals try (split at step)
    all_goals subst d
    all_goals first
      | exact Or.inl rfl
      | apply Or.inr; cases hRight : c.inputTape.right <;>
          simp [Configuration.updateTape, Configuration.advance, Tape.moveRight, hRight]
  · have hNone : copyDelimited[c.pc]? = none := by
      apply List.getElem?_eq_none
      change 15 ≤ c.pc
      omega
    simp [Step, successors, next, hActive, hNone] at step
    subst d
    exact Or.inl rfl

private def fieldCells (before cells : List (Option Bool)) : Tape :=
  { ({ right := cells } : Tape).moveRight with left := before }

def copyDelimitedStart (beforeInput beforeOutput tail : List (Option Bool))
    (field : List Bool) (blanks : Nat) : Configuration :=
  { inputTape := fieldCells beforeInput ((FiniteBitEncoding.delimit field).map some ++ tail),
    outputTape := { left := beforeOutput, right := List.replicate blanks none } }

def copyDelimitedFinish (beforeInput beforeOutput tail : List (Option Bool))
    (field : List Bool) (blanks : Nat) : Configuration :=
  { pc := 14,
    inputTape := fieldCells ((FiniteBitEncoding.delimit field).reverse.map some ++ beforeInput) tail,
    outputTape := {
      left := (FiniteBitEncoding.delimit field).reverse.map some ++ beforeOutput
      right := List.replicate (blanks - (2*field.length + 1)) none },
    halted := true }

def copyDelimitedSteps : List Bool → Nat
  | [] => 5
  | bit :: rest => (if bit then 9 else 10) + copyDelimitedSteps rest

private theorem copyDelimited_cell_run (input output : Tape) (bit : Bool)
    (hMarkerCell : input.current = some true) (hPayloadCell : input.moveRight.current = some bit) :
    RunsFor copyDelimited ({ inputTape := input, outputTape := output } : Configuration)
      ({ inputTape := input.moveRight.moveRight, outputTape := ((output.write (some true)).moveRight.write (some bit)).moveRight } : Configuration)
      (if bit then 9 else 10) := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let marked : Configuration := { start with pc := 1 }
  let writtenMarker : Configuration := { marked with pc := 2, outputTape := marked.outputTape.write (some true) }
  let payloadOut : Configuration := { writtenMarker with pc := 3, outputTape := writtenMarker.outputTape.moveRight }
  let payloadIn : Configuration := { payloadOut with pc := 4, inputTape := payloadOut.inputTape.moveRight }
  let selected : Configuration := { payloadIn with pc := if bit then 7 else 5 }
  let written : Configuration := { selected with pc := if bit then 8 else 6, outputTape := selected.outputTape.write (some bit) }
  let ready : Configuration := { written with pc := 8 }
  let movedInput : Configuration := { ready with pc := 9, inputTape := ready.inputTape.moveRight }
  let movedOutput : Configuration := { movedInput with pc := 10, outputTape := movedInput.outputTape.moveRight }
  have hMarker : Step copyDelimited start marked := by
    simp [Step, successors, next, copyDelimited, start, marked, Instruction.next, Configuration.tape, hMarkerCell]
  have hWriteMarker : Step copyDelimited marked writtenMarker := by
    simp [Step, successors, next, copyDelimited, start, marked, writtenMarker,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hPayloadOut : Step copyDelimited writtenMarker payloadOut := by
    simp [Step, successors, next, copyDelimited, start, marked, writtenMarker, payloadOut,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hPayloadIn : Step copyDelimited payloadOut payloadIn := by
    simp [Step, successors, next, copyDelimited, start, marked, writtenMarker, payloadOut, payloadIn,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hSelect : Step copyDelimited payloadIn selected := by
    cases bit <;> simp [Step, successors, next, copyDelimited, start, marked, writtenMarker,
      payloadOut, payloadIn, selected, Instruction.next, Configuration.tape, hPayloadCell]
  have hWrite : Step copyDelimited selected written := by
    cases bit <;> simp [Step, successors, next, copyDelimited, start, marked, writtenMarker,
      payloadOut, payloadIn, selected, written, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hInput : Step copyDelimited ready movedInput := by
    simp [Step, successors, next, copyDelimited, start, marked, writtenMarker, payloadOut,
      payloadIn, selected, written, ready, movedInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput : Step copyDelimited movedInput movedOutput := by
    simp [Step, successors, next, copyDelimited, start, marked, writtenMarker, payloadOut,
      payloadIn, selected, written, ready, movedInput, movedOutput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step copyDelimited movedOutput
      ({ inputTape := input.moveRight.moveRight, outputTape := ((output.write (some true)).moveRight.write (some bit)).moveRight } : Configuration) := by
    simp [Step, successors, next, copyDelimited, start, marked, writtenMarker,
      payloadOut, payloadIn, selected, written, ready, movedInput, movedOutput, Instruction.next]
  have prior := RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hMarker) hWriteMarker) hPayloadOut) hPayloadIn) hSelect) hWrite
  cases bit with
  | false =>
      have hJump : Step copyDelimited written ready := by
        simp [Step, successors, next, copyDelimited, written, ready, start, marked, writtenMarker,
          payloadOut, payloadIn, selected, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ prior hJump) hInput) hOutput) hBack
  | true =>
      have hReady : ready = written := by simp [ready, written]
      rw [hReady] at hInput
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ prior hInput) hOutput) hBack

private theorem copyDelimited_one (beforeInput beforeOutput tail : List (Option Bool))
    (bit : Bool) (rest : List Bool) (blanks : Nat) :
    RunsFor copyDelimited (copyDelimitedStart beforeInput beforeOutput tail (bit :: rest) blanks)
      (copyDelimitedStart (some bit :: some true :: beforeInput)
        (some bit :: some true :: beforeOutput) tail rest (blanks - 2)) (if bit then 9 else 10) := by
  have run := copyDelimited_cell_run
    (fieldCells beforeInput ((FiniteBitEncoding.delimit (bit :: rest)).map some ++ tail))
    ({ left := beforeOutput, right := List.replicate blanks none } : Tape) bit rfl rfl
  cases blanks with
  | zero =>
      cases rest <;> simpa [copyDelimitedStart, fieldCells, FiniteBitEncoding.delimit, Tape.moveRight, Tape.write] using run
  | succ count =>
      cases count <;> cases rest <;> simpa [copyDelimitedStart, fieldCells, FiniteBitEncoding.delimit,
        Tape.moveRight, Tape.write, List.replicate_succ] using run

theorem copyDelimited_runs (beforeInput beforeOutput tail : List (Option Bool))
    (field : List Bool) (blanks : Nat) :
    RunsFor copyDelimited (copyDelimitedStart beforeInput beforeOutput tail field blanks)
      (copyDelimitedFinish beforeInput beforeOutput tail field blanks) (copyDelimitedSteps field) := by
  induction field generalizing beforeInput beforeOutput blanks with
  | nil =>
      let start := copyDelimitedStart beforeInput beforeOutput tail [] blanks
      let selected : Configuration := { start with pc := 11 }
      let written : Configuration := { selected with pc := 12, outputTape := selected.outputTape.write (some false) }
      let movedInput : Configuration := { written with pc := 13, inputTape := written.inputTape.moveRight }
      let movedOutput : Configuration := { movedInput with pc := 14, outputTape := movedInput.outputTape.moveRight }
      have hSelect : Step copyDelimited start selected := by
        simp [Step, successors, next, copyDelimited, start, selected, copyDelimitedStart,
          fieldCells, FiniteBitEncoding.delimit, Tape.moveRight, Instruction.next, Configuration.tape]
      have hWrite : Step copyDelimited selected written := by
        simp [Step, successors, next, copyDelimited, start, selected, written, copyDelimitedStart,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have hInput : Step copyDelimited written movedInput := by
        simp [Step, successors, next, copyDelimited, start, selected, written, movedInput, copyDelimitedStart,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have hOutput : Step copyDelimited movedInput movedOutput := by
        simp [Step, successors, next, copyDelimited, start, selected, written, movedInput, movedOutput, copyDelimitedStart,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have hHalt : Step copyDelimited movedOutput (copyDelimitedFinish beforeInput beforeOutput tail [] blanks) := by
        cases blanks <;> cases tail <;> simp [Step, successors, next, copyDelimited, start, selected, written,
          movedInput, movedOutput, copyDelimitedStart, copyDelimitedFinish, fieldCells,
          FiniteBitEncoding.delimit, Instruction.next, Tape.moveRight, Tape.write, List.replicate_succ]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) hSelect) hWrite) hInput) hOutput) hHalt
  | cons bit rest ih =>
      have tailRun := ih (some bit :: some true :: beforeInput) (some bit :: some true :: beforeOutput) (blanks - 2)
      have hFinish : copyDelimitedFinish (some bit :: some true :: beforeInput)
          (some bit :: some true :: beforeOutput) tail rest (blanks - 2) =
          copyDelimitedFinish beforeInput beforeOutput tail (bit :: rest) blanks := by
        simp [copyDelimitedFinish, FiniteBitEncoding.delimit, List.reverse_cons, List.map_append, List.append_assoc]
        omega
      rw [hFinish] at tailRun
      exact (copyDelimited_one beforeInput beforeOutput tail bit rest blanks).trans tailRun

theorem copyDelimited_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ copyDelimited := by simp [copyDelimited]

theorem copyDelimited_eval (beforeInput beforeOutput tail : List (Option Bool))
    (field : List Bool) (blanks : Nat) :
    evalConfigWithin copyDelimited (copyDelimitedStart beforeInput beforeOutput tail field blanks)
      (copyDelimitedSteps field) = PMF.pure (copyDelimitedFinish beforeInput beforeOutput tail field blanks) :=
  (copyDelimited_runs _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit copyDelimited_no_randomBit

theorem copyDelimited_steps_le (field : List Bool) :
    copyDelimitedSteps field ≤ 10*field.length + 5 := by
  induction field with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [copyDelimitedSteps, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

theorem copyDelimitedStart_layout (beforeInput beforeOutput tail : List (Option Bool))
    (field : List Bool) (blanks : Nat) :
    copyDelimitedStart beforeInput beforeOutput tail field blanks =
      { inputTape := { ({ right := (FiniteBitEncoding.delimit field).map some ++ tail } : Tape).moveRight with left := beforeInput },
        outputTape := { left := beforeOutput, right := List.replicate blanks none } } := rfl

theorem copyDelimitedFinish_layout (beforeInput beforeOutput tail : List (Option Bool))
    (field : List Bool) (blanks : Nat) :
    copyDelimitedFinish beforeInput beforeOutput tail field blanks =
      { pc := 14,
        inputTape := { ({ right := tail } : Tape).moveRight with
          left := (FiniteBitEncoding.delimit field).reverse.map some ++ beforeInput },
        outputTape := {
          left := (FiniteBitEncoding.delimit field).reverse.map some ++ beforeOutput
          right := List.replicate (blanks - (2*field.length + 1)) none }, halted := true } := rfl

theorem copyDelimited_control_closed (c d : Configuration)
    (hPc : c.pc < copyDelimited.length) (step : Step copyDelimited c d)
    (_hRunning : d.halted = false) : d.pc < copyDelimited.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 15 at hPc
  change d.pc < 15
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, copyDelimited, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]


private theorem copyDelimited_blank_run (input output : Tape) (hBlank : input.current = none) :
    RunsFor copyDelimited ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 14, inputTape := input, outputTape := output, halted := true } : Configuration) 2 := by
  have a : Step copyDelimited ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 14, inputTape := input, outputTape := output } : Configuration) := by
    simp [Step, successors, next, copyDelimited, Instruction.next, Configuration.tape, hBlank]
  have b : Step copyDelimited ({ pc := 14, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 14, inputTape := input, outputTape := output, halted := true } : Configuration) := by
    simp [Step, successors, next, copyDelimited, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) a) b

private theorem copyDelimited_false_run (input output : Tape) (hCell : input.current = some false) :
    RunsFor copyDelimited ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 14, inputTape := input.moveRight, outputTape := (output.write (some false)).moveRight, halted := true } : Configuration) 5 := by
  let selected : Configuration := { pc := 11, inputTape := input, outputTape := output }
  let written : Configuration := { selected with pc := 12, outputTape := output.write (some false) }
  let movedInput : Configuration := { written with pc := 13, inputTape := input.moveRight }
  let movedOutput : Configuration := { movedInput with pc := 14, outputTape := movedInput.outputTape.moveRight }
  have a : Step copyDelimited ({ inputTape := input, outputTape := output } : Configuration) selected := by
    simp [Step, successors, next, copyDelimited, selected, Instruction.next, Configuration.tape, hCell]
  have b : Step copyDelimited selected written := by
    simp [Step, successors, next, copyDelimited, selected, written, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have c : Step copyDelimited written movedInput := by
    simp [Step, successors, next, copyDelimited, selected, written, movedInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have d : Step copyDelimited movedInput movedOutput := by
    simp [Step, successors, next, copyDelimited, selected, written, movedInput, movedOutput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have e : Step copyDelimited movedOutput
      ({ pc := 14, inputTape := input.moveRight, outputTape := (output.write (some false)).moveRight, halted := true } : Configuration) := by
    simp [Step, successors, next, copyDelimited, selected, written, movedInput, movedOutput, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) a) b) c) d) e

private theorem copyDelimited_dangling_run (input output : Tape)
    (hMarker : input.current = some true) (hBlank : input.moveRight.current = none) :
    RunsFor copyDelimited ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 14, inputTape := input.moveRight, outputTape := (output.write (some true)).moveRight, halted := true } : Configuration) 6 := by
  let selected : Configuration := { pc := 1, inputTape := input, outputTape := output }
  let written : Configuration := { selected with pc := 2, outputTape := output.write (some true) }
  let movedOutput : Configuration := { written with pc := 3, outputTape := written.outputTape.moveRight }
  let movedInput : Configuration := { movedOutput with pc := 4, inputTape := input.moveRight }
  let stopped : Configuration := { movedInput with pc := 14 }
  have a : Step copyDelimited ({ inputTape := input, outputTape := output } : Configuration) selected := by
    simp [Step, successors, next, copyDelimited, selected, Instruction.next, Configuration.tape, hMarker]
  have b : Step copyDelimited selected written := by
    simp [Step, successors, next, copyDelimited, selected, written, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have c : Step copyDelimited written movedOutput := by
    simp [Step, successors, next, copyDelimited, selected, written, movedOutput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have d : Step copyDelimited movedOutput movedInput := by
    simp [Step, successors, next, copyDelimited, selected, written, movedOutput, movedInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have e : Step copyDelimited movedInput stopped := by
    simp [Step, successors, next, copyDelimited, selected, written, movedOutput, movedInput, stopped,
      Instruction.next, Configuration.tape, hBlank]
  have f : Step copyDelimited stopped
      ({ pc := 14, inputTape := input.moveRight, outputTape := (output.write (some true)).moveRight, halted := true } : Configuration) := by
    simp [Step, successors, next, copyDelimited, selected, written, movedOutput, movedInput, stopped, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) a) b) c) d) e) f

private theorem copyDelimited_fresh_move (before : List (Option Bool)) (blanks : Nat) (bit : Bool) :
    (({ left := before, right := List.replicate blanks none } : Tape).write (some bit)).moveRight =
      { left := some bit :: before, right := List.replicate (blanks - 1) none } := by
  cases blanks <;> simp [Tape.write, Tape.moveRight, List.replicate_succ]

private theorem copyDelimited_finite_cells (input output : Tape) :
    ∃ finish used, used ≤ 10 * input.right.length + 12 ∧
      RunsFor copyDelimited ({ inputTape := input, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true ∧
      ∀ before blanks, output = ({ left := before, right := List.replicate blanks none } : Tape) →
        ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none } := by
  cases hCurrent : input.current with
  | none =>
      refine ⟨_, 2, by omega, copyDelimited_blank_run input output hCurrent, rfl, ?_⟩
      intro before blanks hOutput
      exact ⟨before, blanks, hOutput⟩
  | some marker =>
      cases marker with
      | false =>
          refine ⟨_, 5, by omega, copyDelimited_false_run input output hCurrent, rfl, ?_⟩
          intro before blanks hOutput
          exact ⟨some false :: before, blanks - 1, by
            change (output.write (some false)).moveRight = _
            rw [hOutput, copyDelimited_fresh_move]⟩
      | true =>
          cases hRight : input.right with
          | nil =>
              refine ⟨_, 6, by omega, copyDelimited_dangling_run input output hCurrent
                (by simp [Tape.moveRight, hRight]), rfl, ?_⟩
              intro before blanks hOutput
              exact ⟨some true :: before, blanks - 1, by
                change (output.write (some true)).moveRight = _
                rw [hOutput, copyDelimited_fresh_move]⟩
          | cons payload rest =>
              cases payload with
              | none =>
                  refine ⟨_, 6, by omega, copyDelimited_dangling_run input output hCurrent
                    (by simp [Tape.moveRight, hRight]), rfl, ?_⟩
                  intro before blanks hOutput
                  exact ⟨some true :: before, blanks - 1, by
                    change (output.write (some true)).moveRight = _
                    rw [hOutput, copyDelimited_fresh_move]⟩
              | some bit =>
                  have first := copyDelimited_cell_run input output bit hCurrent
                    (by simp [Tape.moveRight, hRight])
                  let nextOutput := ((output.write (some true)).moveRight.write (some bit)).moveRight
                  obtain ⟨finish, used, hUsed, tailRun, hHalt, hLayout⟩ :=
                    copyDelimited_finite_cells input.moveRight.moveRight nextOutput
                  refine ⟨finish, (if bit then 9 else 10) + used, ?_, first.trans tailRun, hHalt, ?_⟩
                  · cases rest <;> cases bit <;>
                      simp only [Tape.moveRight, hRight, List.length_cons, List.length_nil, Bool.false_eq_true, ↓reduceIte] at hUsed ⊢ <;> omega
                  · intro before blanks hOutput
                    apply hLayout (some bit :: some true :: before) (blanks - 1 - 1)
                    dsimp only [nextOutput]
                    rw [hOutput, copyDelimited_fresh_move, copyDelimited_fresh_move]
termination_by input.right.length
decreasing_by
  cases input
  cases rest <;> simp_all [Tape.moveRight]

/-- Escaped-field copying stops on any finite caller tapes. Missing payload
bits, missing delimiters, and dirty output storage do not invalidate the
native transition bound; no valid-field decoding claim is made here. -/
theorem copyDelimited_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 10 * input.cells + 12 ∧
      RunsFor copyDelimited ({ inputTape := input, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true := by
  obtain ⟨finish, used, hUsed, run, hHalt, _hLayout⟩ := copyDelimited_finite_cells input output
  refine ⟨finish, used, ?_, run, hHalt⟩
  dsimp only [Tape.cells]
  omega

/-- Escaped-field copying preserves a fresh output frontier on arbitrary
finite inputs. A dangling marker is copied before stopping, but the head
still ends on a blank output cell. Protected caller cells remain to its left. -/
theorem copyDelimited_terminates_with_output_layout (input : Tape)
    (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining, used ≤ 10 * input.cells + 12 ∧
      RunsFor copyDelimited
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, hUsed, run, hHalt, hLayout⟩ :=
    copyDelimited_finite_cells input { left := before, right := List.replicate blanks none }
  obtain ⟨after, remaining, hOutput⟩ := hLayout before blanks rfl
  refine ⟨finish, used, after, remaining, ?_, run, hHalt, hOutput⟩
  dsimp only [Tape.cells]
  omega

theorem copyDelimited_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor copyDelimited
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (10 * input.cells + 12)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ := copyDelimited_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted copyDelimited_no_randomBit hBound finish trace

end Machine
