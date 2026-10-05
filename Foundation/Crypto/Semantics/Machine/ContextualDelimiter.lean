import Foundation.Crypto.Semantics.Machine.DelimitedOutput

namespace Machine

private def delimitedContextSegment (bits : List Bool) (tail : List (Option Bool)) : Tape :=
  ({ right := bits.map some ++ none :: tail } : Tape).moveRight

/-- Run the existing native delimiter writer on a retained segment. Cells
beyond its terminating blank and both saved prefixes are preserved. -/
def writeDelimitedContextStart (beforeInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  { inputTape := { delimitedContextSegment bits tail with left := beforeInput },
    outputTape := { left := beforeOutput, right := List.replicate blanks none } }

def writeDelimitedContextFinish (beforeInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  { pc := 13,
    inputTape := { left := bits.reverse.map some ++ beforeInput, right := tail },
    outputTape := {
      left := (FiniteBitEncoding.delimit bits).reverse.map some ++ beforeOutput
      right := List.replicate (blanks - (2 * bits.length + 1)) none },
    halted := true }

theorem writeDelimitedContextStart_layout (beforeInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    writeDelimitedContextStart beforeInput beforeOutput tail bits blanks =
      ({ inputTape := { ({ right := bits.map some ++ none :: tail } : Tape).moveRight with left := beforeInput },
         outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration) := rfl

private theorem writeDelimitedContext_one (beforeInput beforeOutput tail : List (Option Bool))
    (bit : Bool) (rest : List Bool) (blanks : Nat) :
    RunsFor writeDelimited (writeDelimitedContextStart beforeInput beforeOutput tail (bit :: rest) blanks)
      (writeDelimitedContextStart (some bit :: beforeInput)
        (some bit :: some true :: beforeOutput) tail rest (blanks - 2)) (if bit then 7 else 8) := by
  let start := writeDelimitedContextStart beforeInput beforeOutput tail (bit :: rest) blanks
  let selected : Configuration := { start with pc := if bit then 5 else 1 }
  let marked : Configuration :=
    { selected with
      pc := if bit then 6 else 2,
      outputTape := selected.outputTape.write (some true) }
  let payload : Configuration :=
    { marked with
      pc := if bit then 7 else 3,
      outputTape := marked.outputTape.moveRight }
  let written : Configuration :=
    { payload with
      pc := if bit then 8 else 4,
      outputTape := payload.outputTape.write (some bit) }
  let ready : Configuration := { written with pc := 8 }
  let movedInput : Configuration :=
    { ready with pc := 9, inputTape := ready.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 10, outputTape := movedInput.outputTape.moveRight }
  have hSelect : Step writeDelimited start selected := by
    cases bit <;> simp [Step, successors, next, writeDelimited, start, selected,
      writeDelimitedContextStart, delimitedContextSegment, Tape.moveRight, Instruction.next, Configuration.tape]
  have hMark : Step writeDelimited selected marked := by
    cases bit <;> simp [Step, successors, next, writeDelimited, start, selected, marked,
      writeDelimitedContextStart, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hPayload : Step writeDelimited marked payload := by
    cases bit <;> simp [Step, successors, next, writeDelimited, start, selected, marked,
      payload, writeDelimitedContextStart, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hWrite : Step writeDelimited payload written := by
    cases bit <;> simp [Step, successors, next, writeDelimited, start, selected, marked,
      payload, written, writeDelimitedContextStart, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hInput : Step writeDelimited ready movedInput := by
    simp [Step, successors, next, writeDelimited, start, selected, marked, payload,
      written, ready, movedInput, writeDelimitedContextStart, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hOutput : Step writeDelimited movedInput movedOutput := by
    simp [Step, successors, next, writeDelimited, start, selected, marked, payload,
      written, ready, movedInput, movedOutput, writeDelimitedContextStart, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step writeDelimited movedOutput
      (writeDelimitedContextStart (some bit :: beforeInput)
        (some bit :: some true :: beforeOutput) tail rest (blanks - 2)) := by
    cases blanks with
    | zero =>
        cases rest <;> simp [Step, successors, next, writeDelimited, start, selected, marked,
          payload, written, ready, movedInput, movedOutput, writeDelimitedContextStart,
          delimitedContextSegment, Instruction.next, Tape.moveRight, Tape.write]
    | succ b =>
        cases b <;> cases rest <;> simp [Step, successors, next, writeDelimited, start, selected, marked,
          payload, written, ready, movedInput, movedOutput, writeDelimitedContextStart,
          delimitedContextSegment, Instruction.next, Tape.moveRight, Tape.write, List.replicate_succ]
  have prior := RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hSelect) hMark) hPayload) hWrite
  cases bit with
  | false =>
      have hJump : Step writeDelimited written ready := by
        simp [Step, successors, next, writeDelimited, written, ready,
          start, selected, marked, payload, writeDelimitedContextStart, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ prior hJump) hInput) hOutput) hBack
  | true =>
      have hReady : ready = written := by simp [ready, written]
      rw [hReady] at hInput
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ prior hInput) hOutput) hBack

theorem writeDelimitedContext_runs (beforeInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    RunsFor writeDelimited (writeDelimitedContextStart beforeInput beforeOutput tail bits blanks)
      (writeDelimitedContextFinish beforeInput beforeOutput tail bits blanks) (writeDelimitedSteps bits) := by
  induction bits generalizing beforeInput beforeOutput blanks with
  | nil =>
      let start := writeDelimitedContextStart beforeInput beforeOutput tail [] blanks
      let selected : Configuration := { start with pc := 11 }
      let written : Configuration :=
        { selected with pc := 12, outputTape := selected.outputTape.write (some false) }
      let moved : Configuration :=
        { written with pc := 13, outputTape := written.outputTape.moveRight }
      have hSelect : Step writeDelimited start selected := by
        simp [Step, successors, next, writeDelimited, start, selected,
          writeDelimitedContextStart, delimitedContextSegment, Tape.moveRight, Instruction.next, Configuration.tape]
      have hWrite : Step writeDelimited selected written := by
        simp [Step, successors, next, writeDelimited, start, selected, written,
          writeDelimitedContextStart, Instruction.next, Configuration.updateTape, Configuration.advance]
      have hMove : Step writeDelimited written moved := by
        simp [Step, successors, next, writeDelimited, start, selected, written, moved,
          writeDelimitedContextStart, Instruction.next, Configuration.updateTape, Configuration.advance]
      have hHalt : Step writeDelimited moved
          (writeDelimitedContextFinish beforeInput beforeOutput tail [] blanks) := by
        cases blanks <;> simp [Step, successors, next, writeDelimited, start, selected, written, moved,
          writeDelimitedContextStart, writeDelimitedContextFinish, FiniteBitEncoding.delimit, List.replicate_succ,
          Instruction.next, delimitedContextSegment, Tape.moveRight, Tape.write, Tape.moveRight]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) hSelect) hWrite) hMove) hHalt
  | cons bit rest ih =>
      have tailRun := ih (some bit :: beforeInput) (some bit :: some true :: beforeOutput) (blanks - 2)
      have hFinish : writeDelimitedContextFinish (some bit :: beforeInput)
          (some bit :: some true :: beforeOutput) tail rest (blanks - 2) =
          writeDelimitedContextFinish beforeInput beforeOutput tail (bit :: rest) blanks := by
        simp [writeDelimitedContextFinish, FiniteBitEncoding.delimit, List.reverse_cons,
          List.map_append, List.append_assoc]
        omega
      rw [hFinish] at tailRun
      change RunsFor _ _ _ ((if bit then 7 else 8) + writeDelimitedSteps rest)
      exact (writeDelimitedContext_one beforeInput beforeOutput tail bit rest blanks).trans tailRun


theorem writeDelimitedContext_eval (beforeInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    evalConfigWithin writeDelimited (writeDelimitedContextStart beforeInput beforeOutput tail bits blanks)
      (writeDelimitedSteps bits) =
      PMF.pure (writeDelimitedContextFinish beforeInput beforeOutput tail bits blanks) :=
  (writeDelimitedContext_runs _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit
    writeDelimited_no_randomBit

end Machine
