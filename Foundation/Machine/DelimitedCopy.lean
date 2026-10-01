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

private theorem copyDelimited_one (beforeInput beforeOutput tail : List (Option Bool))
    (bit : Bool) (rest : List Bool) (blanks : Nat) :
    RunsFor copyDelimited (copyDelimitedStart beforeInput beforeOutput tail (bit :: rest) blanks)
      (copyDelimitedStart (some bit :: some true :: beforeInput)
        (some bit :: some true :: beforeOutput) tail rest (blanks - 2)) (if bit then 9 else 10) := by
  let start := copyDelimitedStart beforeInput beforeOutput tail (bit :: rest) blanks
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
    simp [Step, successors, next, copyDelimited, start, marked, copyDelimitedStart, fieldCells,
      FiniteBitEncoding.delimit, Tape.moveRight, Instruction.next, Configuration.tape]
  have hWriteMarker : Step copyDelimited marked writtenMarker := by
    simp [Step, successors, next, copyDelimited, start, marked, writtenMarker,
      copyDelimitedStart, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hPayloadOut : Step copyDelimited writtenMarker payloadOut := by
    simp [Step, successors, next, copyDelimited, start, marked, writtenMarker, payloadOut,
      copyDelimitedStart, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hPayloadIn : Step copyDelimited payloadOut payloadIn := by
    simp [Step, successors, next, copyDelimited, start, marked, writtenMarker, payloadOut, payloadIn,
      copyDelimitedStart, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hSelect : Step copyDelimited payloadIn selected := by
    cases bit <;> simp [Step, successors, next, copyDelimited, start, marked, writtenMarker,
      payloadOut, payloadIn, selected, copyDelimitedStart, fieldCells, FiniteBitEncoding.delimit,
      Tape.moveRight, Instruction.next, Configuration.tape]
  have hWrite : Step copyDelimited selected written := by
    cases bit <;> simp [Step, successors, next, copyDelimited, start, marked, writtenMarker,
      payloadOut, payloadIn, selected, written, copyDelimitedStart, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hInput : Step copyDelimited ready movedInput := by
    simp [Step, successors, next, copyDelimited, start, marked, writtenMarker, payloadOut,
      payloadIn, selected, written, ready, movedInput, copyDelimitedStart, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput : Step copyDelimited movedInput movedOutput := by
    simp [Step, successors, next, copyDelimited, start, marked, writtenMarker, payloadOut,
      payloadIn, selected, written, ready, movedInput, movedOutput, copyDelimitedStart, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step copyDelimited movedOutput
      (copyDelimitedStart (some bit :: some true :: beforeInput)
        (some bit :: some true :: beforeOutput) tail rest (blanks - 2)) := by
    cases blanks with
    | zero =>
        cases rest <;> simp [Step, successors, next, copyDelimited, start, marked, writtenMarker,
          payloadOut, payloadIn, selected, written, ready, movedInput, movedOutput,
          copyDelimitedStart, fieldCells, FiniteBitEncoding.delimit, Instruction.next, Tape.moveRight, Tape.write]
    | succ b =>
        cases b <;> cases rest <;> simp [Step, successors, next, copyDelimited, start, marked, writtenMarker,
          payloadOut, payloadIn, selected, written, ready, movedInput, movedOutput,
          copyDelimitedStart, fieldCells, FiniteBitEncoding.delimit, Instruction.next, Tape.moveRight, Tape.write,
          List.replicate_succ]
  have prior := RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hMarker) hWriteMarker) hPayloadOut) hPayloadIn) hSelect) hWrite
  cases bit with
  | false =>
      have hJump : Step copyDelimited written ready := by
        simp [Step, successors, next, copyDelimited, written, ready, start, marked, writtenMarker,
          payloadOut, payloadIn, selected, copyDelimitedStart, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ prior hJump) hInput) hOutput) hBack
  | true =>
      have hReady : ready = written := by simp [ready, written]
      rw [hReady] at hInput
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ prior hInput) hOutput) hBack

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

end Machine
