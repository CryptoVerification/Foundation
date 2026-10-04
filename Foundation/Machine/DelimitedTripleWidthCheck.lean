import Foundation.Machine.DelimitedWidthCheck

namespace Machine.DelimitedTripleWidthCheck

/-- Compare one delimited element field with one third of a contiguous
three-field instance code. Each element payload bit consumes three instance
cells. Their values are ignored; only their physical presence is tested.
This lets the encoded `p ++ q ++ g` serve as a width counter without
separating the three mathematical parameters. -/
def program : Program :=
  [.branch .input 13 9 1,
   .branch .output 13 2 2,
   .moveRight .input,
   .branch .input 13 4 4,
   .moveRight .input,
   .moveRight .output,
   .moveRight .output,
   .moveRight .output,
   .jump 0,
   .branch .output 10 13 13,
   .moveRight .input,
   .write .output true,
   .halt,
   .write .output false,
   .halt]

theorem length : program.length = 15 := by decide

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

def start (beforeInput beforeOutput : List (Option Bool))
    (counter field tail : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits (FiniteBitEncoding.delimit field ++ tail) with
      left := beforeInput },
    outputTape := { Tape.ofBits counter with left := beforeOutput } }

def finish (beforeInput beforeOutput : List (Option Bool))
    (counter field tail : List Bool) : Configuration :=
  { pc := 12,
    inputTape := { Tape.ofBits tail with
      left := (FiniteBitEncoding.delimit field).reverse.map some ++ beforeInput },
    outputTape := ⟨counter.reverse.map some ++ beforeOutput, some true, []⟩,
    halted := true }

private theorem one (beforeInput beforeOutput : List (Option Bool))
    (a b c : Bool) (counter : List Bool) (bit : Bool)
    (rest tail : List Bool) :
    RunsFor program
      (start beforeInput beforeOutput (a :: b :: c :: counter)
        (bit :: rest) tail)
      (start (some bit :: some true :: beforeInput)
        (some c :: some b :: some a :: beforeOutput) counter rest tail) 9 := by
  let source := start beforeInput beforeOutput (a :: b :: c :: counter)
    (bit :: rest) tail
  let selected : Configuration := { source with pc := 1 }
  let checked : Configuration := { selected with pc := 2 }
  let payload : Configuration :=
    { checked with pc := 3, inputTape := checked.inputTape.moveRight }
  let present : Configuration := { payload with pc := 4 }
  let inputDone : Configuration :=
    { present with pc := 5, inputTape := present.inputTape.moveRight }
  let first : Configuration :=
    { inputDone with pc := 6, outputTape := inputDone.outputTape.moveRight }
  let second : Configuration :=
    { first with pc := 7, outputTape := first.outputTape.moveRight }
  let third : Configuration :=
    { second with pc := 8, outputTape := second.outputTape.moveRight }
  have h0 : Step program source selected := by
    simp [Step, successors, next, program, source, selected, start,
      FiniteBitEncoding.delimit, Tape.ofBits,
      Instruction.next, Configuration.tape]
  have h1 : Step program selected checked := by
    cases a <;>
      simp [Step, successors, next, program, source, selected, checked,
        start, Tape.ofBits, Instruction.next, Configuration.tape]
  have h2 : Step program checked payload := by
    simp [Step, successors, next, program, source, selected, checked,
      payload, start, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have h3 : Step program payload present := by
    cases bit <;>
      simp [Step, successors, next, program, source, selected, checked,
        payload, present, start, FiniteBitEncoding.delimit,
        Tape.ofBits, Tape.moveRight, Instruction.next, Configuration.tape]
  have h4 : Step program present inputDone := by
    simp [Step, successors, next, program, source, selected, checked,
      payload, present, inputDone, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h5 : Step program inputDone first := by
    simp [Step, successors, next, program, source, selected, checked,
      payload, present, inputDone, first, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h6 : Step program first second := by
    simp [Step, successors, next, program, source, selected, checked,
      payload, present, inputDone, first, second, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h7 : Step program second third := by
    simp [Step, successors, next, program, source, selected, checked,
      payload, present, inputDone, first, second, third, start,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h8 : Step program third
      (start (some bit :: some true :: beforeInput)
        (some c :: some b :: some a :: beforeOutput) counter rest tail) := by
    cases counter <;> cases rest <;> cases tail <;>
      simp [Step, successors, next, program, source, selected, checked,
        payload, present, inputDone, first, second, third, start,
        FiniteBitEncoding.delimit, Tape.ofBits, Tape.moveRight,
        Instruction.next]
  exact (((((((((RunsFor.zero _).succ h0).succ h1).succ h2).succ h3).succ h4).succ h5).succ h6).succ h7).succ h8

private theorem done (beforeInput beforeOutput : List (Option Bool))
    (tail : List Bool) :
    RunsFor program (start beforeInput beforeOutput [] [] tail)
      (finish beforeInput beforeOutput [] [] tail) 5 := by
  let source := start beforeInput beforeOutput [] [] tail
  let selected : Configuration := { source with pc := 9 }
  let accepted : Configuration := { selected with pc := 10 }
  let advanced : Configuration :=
    { accepted with pc := 11, inputTape := accepted.inputTape.moveRight }
  let written : Configuration :=
    { advanced with pc := 12, outputTape := advanced.outputTape.write (some true) }
  have h0 : Step program source selected := by
    simp [Step, successors, next, program, source, selected, start,
      FiniteBitEncoding.delimit, Tape.ofBits, Instruction.next,
      Configuration.tape]
  have h1 : Step program selected accepted := by
    simp [Step, successors, next, program, source, selected, accepted,
      start, Tape.ofBits, Instruction.next, Configuration.tape]
  have h2 : Step program accepted advanced := by
    simp [Step, successors, next, program, source, selected, accepted,
      advanced, start, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have h3 : Step program advanced written := by
    simp [Step, successors, next, program, source, selected, accepted,
      advanced, written, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h4 : Step program written (finish beforeInput beforeOutput [] [] tail) := by
    cases tail <;>
      simp [Step, successors, next, program, source, selected, accepted,
        advanced, written, start, finish, FiniteBitEncoding.delimit,
        Tape.ofBits, Tape.moveRight, Tape.write, Instruction.next]
  exact (((((RunsFor.zero _).succ h0).succ h1).succ h2).succ h3).succ h4

/-- Exact accepting trace for an instance code with three equally wide
fields. The delimiter is consumed, and the input head reaches the next
response field while the instance bits remain on the output tape. -/
theorem runs_matching (beforeInput beforeOutput : List (Option Bool))
    (field tail : List Bool) (columns : List (Bool × Bool × Bool))
    (hLength : columns.length = field.length) :
    let counter := columns.flatMap fun (a, b, c) => [a, b, c]
    RunsFor program (start beforeInput beforeOutput counter field tail)
      (finish beforeInput beforeOutput counter field tail)
      (9 * field.length + 5) := by
  induction field generalizing columns beforeInput beforeOutput with
  | nil =>
      cases columns with
      | nil => simpa [start, finish] using done beforeInput beforeOutput tail
      | cons col rest => simp at hLength
  | cons bit rest ih =>
      cases columns with
      | nil => simp at hLength
      | cons col remaining =>
          rcases col with ⟨a, b, c⟩
          have hRest : remaining.length = rest.length := by
            simpa using hLength
          have hRun := (one beforeInput beforeOutput a b c
            (remaining.flatMap fun (a, b, c) => [a, b, c]) bit rest tail).trans
              (ih (some bit :: some true :: beforeInput)
                (some c :: some b :: some a :: beforeOutput) remaining hRest)
          have hFinish : finish
              (some bit :: some true :: beforeInput)
              (some c :: some b :: some a :: beforeOutput)
              (remaining.flatMap fun (a, b, c) => [a, b, c]) rest tail =
              finish beforeInput beforeOutput
                (((a, b, c) :: remaining).flatMap (fun (x, y, z) => [x, y, z]))
                (bit :: rest) tail := by
            simp [finish, FiniteBitEncoding.delimit,
              List.reverse_cons, List.map_append, List.append_assoc]
          rw [hFinish] at hRun
          simpa [List.length_cons, Nat.mul_add, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hRun

/-- A concatenated three-field instance code also works: only its total
length, not an interleaved layout, matters to the native checker. -/
theorem runs_matching_length (beforeInput beforeOutput : List (Option Bool))
    (counter field tail : List Bool)
    (hLength : counter.length = 3 * field.length) :
    RunsFor program (start beforeInput beforeOutput counter field tail)
      (finish beforeInput beforeOutput counter field tail)
      (9 * field.length + 5) := by
  induction field generalizing counter beforeInput beforeOutput with
  | nil =>
      cases counter with
      | nil => simpa [start, finish] using done beforeInput beforeOutput tail
      | cons head rest => simp at hLength
  | cons bit rest ih =>
      cases counter with
      | nil => simp at hLength
      | cons a next =>
          cases next with
          | nil => simp at hLength; omega
          | cons b next =>
              cases next with
              | nil => simp at hLength; omega
              | cons c remaining =>
                  have hRest : remaining.length = 3 * rest.length := by
                    simp only [List.length_cons] at hLength
                    omega
                  have hRun := (one beforeInput beforeOutput a b c
                    remaining bit rest tail).trans
                      (ih (some bit :: some true :: beforeInput)
                        (some c :: some b :: some a :: beforeOutput)
                        remaining hRest)
                  have hFinish : finish
                      (some bit :: some true :: beforeInput)
                      (some c :: some b :: some a :: beforeOutput)
                      remaining rest tail =
                      finish beforeInput beforeOutput (a :: b :: c :: remaining)
                        (bit :: rest) tail := by
                    simp [finish, FiniteBitEncoding.delimit,
                      List.reverse_cons, List.map_append, List.append_assoc]
                  rw [hFinish] at hRun
                  simpa [List.length_cons, Nat.mul_add, Nat.add_assoc,
                    Nat.add_comm, Nat.add_left_comm] using hRun

private def atStart (input output : Tape) : Configuration :=
  { inputTape := input, outputTape := output }

private def rejectFinish (c : Configuration) : Configuration :=
  { c with pc := 14, outputTape := c.outputTape.write (some false), halted := true }

private def acceptFinish (c : Configuration) : Configuration :=
  { pc := 12, inputTape := c.inputTape.moveRight,
    outputTape := c.outputTape.write (some true), halted := true }

private theorem reject_run (c : Configuration)
    (hPc : c.pc = 13) (hActive : c.halted = false) :
    RunsFor program c (rejectFinish c) 2 := by
  let written : Configuration :=
    { c with pc := 14, outputTape := c.outputTape.write (some false) }
  have hWrite : Step program c written := by
    simp [Step, successors, next, program, hPc, hActive, written,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step program written (rejectFinish c) := by
    simp [Step, successors, next, program, written, rejectFinish, hActive,
      Instruction.next]
  exact ((RunsFor.zero c).succ hWrite).succ hHalt

private theorem accept_run (c : Configuration)
    (hPc : c.pc = 10) (hActive : c.halted = false) :
    RunsFor program c (acceptFinish c) 3 := by
  let moved : Configuration :=
    { c with pc := 11, inputTape := c.inputTape.moveRight }
  let written : Configuration :=
    { moved with pc := 12, outputTape := moved.outputTape.write (some true) }
  have hMove : Step program c moved := by
    simp [Step, successors, next, program, hPc, hActive, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hWrite : Step program moved written := by
    simp [Step, successors, next, program, moved, written, hActive,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step program written (acceptFinish c) := by
    simp [Step, successors, next, program, moved, written, acceptFinish,
      hActive, Instruction.next]
  exact (((RunsFor.zero c).succ hMove).succ hWrite).succ hHalt

private theorem blank_run_layout (input output : Tape)
    (hBlank : input.current = none) :
    ∃ target, RunsFor program (atStart input output) target 3 ∧
      target.halted = true ∧ target.outputTape.current = some false ∧
      target.outputTape = output.write (some false) := by
  let rejected : Configuration := { atStart input output with pc := 13 }
  have hBranch : Step program (atStart input output) rejected := by
    simp [Step, successors, next, program, atStart, rejected,
      Instruction.next, Configuration.tape, hBlank]
  exact ⟨_, ((RunsFor.zero _).succ hBranch).trans
    (reject_run rejected rfl rfl), rfl, by simp [rejectFinish, rejected, atStart, Tape.write], rfl⟩

private theorem blank_run (input output : Tape)
    (hBlank : input.current = none) :
    ∃ target, RunsFor program (atStart input output) target 3 ∧
      target.halted = true ∧ target.outputTape.current = some false  := by
  obtain ⟨target, run, hHalt, hStatus, _⟩ := blank_run_layout input output hBlank
  exact ⟨target, run, hHalt, hStatus⟩

private theorem delimiter_run_layout (input output : Tape)
    (hFalse : input.current = some false) :
    ∃ target used, used ≤ 5 ∧
      RunsFor program (atStart input output) target used ∧
      target.halted = true ∧
      target.outputTape.current = some (output.current == none) ∧
      target.outputTape = output.write (some (output.current == none)) := by
  let selected : Configuration := { atStart input output with pc := 9 }
  have hBranch : Step program (atStart input output) selected := by
    simp [Step, successors, next, program, atStart, selected,
      Instruction.next, Configuration.tape, hFalse]
  cases hOutput : output.current with
  | none =>
      let accepted : Configuration := { selected with pc := 10 }
      have hSelect : Step program selected accepted := by
        simp [Step, successors, next, program, atStart, selected, accepted,
          Instruction.next, Configuration.tape, hOutput]
      exact ⟨_, 5, by omega,
        ((RunsFor.zero _).succ hBranch |>.succ hSelect).trans
          (accept_run accepted rfl rfl), rfl,
        by simp [acceptFinish, atStart, selected, accepted, Tape.write], by simp [acceptFinish, atStart, selected, accepted]⟩
  | some bit =>
      let rejected : Configuration := { selected with pc := 13 }
      have hSelect : Step program selected rejected := by
        cases bit <;>
          simp [Step, successors, next, program, atStart, selected,
            rejected, Instruction.next, Configuration.tape, hOutput]
      exact ⟨_, 4, by omega,
        ((RunsFor.zero _).succ hBranch |>.succ hSelect).trans
          (reject_run rejected rfl rfl), rfl,
        by simp [rejectFinish, atStart, selected, rejected, Tape.write], by simp [rejectFinish, atStart, selected, rejected]⟩

private theorem delimiter_run (input output : Tape)
    (hFalse : input.current = some false) :
    ∃ target used, used ≤ 5 ∧
      RunsFor program (atStart input output) target used ∧
      target.halted = true ∧
      target.outputTape.current = some (output.current == none)  := by
  obtain ⟨target, used, hUsed, run, hHalt, hStatus, _⟩ := delimiter_run_layout input output hFalse
  exact ⟨target, used, hUsed, run, hHalt, hStatus⟩

private theorem marker_without_counter_layout (input output : Tape)
    (hTrue : input.current = some true)
    (hBlank : output.current = none) :
    ∃ target, RunsFor program (atStart input output) target 4 ∧
      target.halted = true ∧ target.outputTape.current = some false ∧
      target.outputTape = output.write (some false) := by
  let selected : Configuration := { atStart input output with pc := 1 }
  let rejected : Configuration := { selected with pc := 13 }
  have h0 : Step program (atStart input output) selected := by
    simp [Step, successors, next, program, atStart, selected,
      Instruction.next, Configuration.tape, hTrue]
  have h1 : Step program selected rejected := by
    simp [Step, successors, next, program, atStart, selected, rejected,
      Instruction.next, Configuration.tape, hBlank]
  exact ⟨_, ((RunsFor.zero _).succ h0 |>.succ h1).trans
    (reject_run rejected rfl rfl), rfl,
    by simp [rejectFinish, rejected, selected, atStart, Tape.write], rfl⟩

private theorem marker_without_counter (input output : Tape)
    (hTrue : input.current = some true)
    (hBlank : output.current = none) :
    ∃ target, RunsFor program (atStart input output) target 4 ∧
      target.halted = true ∧ target.outputTape.current = some false  := by
  obtain ⟨target, run, hHalt, hStatus, _⟩ := marker_without_counter_layout input output hTrue hBlank
  exact ⟨target, run, hHalt, hStatus⟩

private theorem marker_without_payload_layout (input output : Tape)
    (hTrue : input.current = some true)
    (hCounter : output.current ≠ none)
    (hBlank : input.moveRight.current = none) :
    ∃ target, RunsFor program (atStart input output) target 6 ∧
      target.halted = true ∧ target.outputTape.current = some false ∧
      target.outputTape = output.write (some false) := by
  let source := atStart input output
  let selected : Configuration := { source with pc := 1 }
  let checked : Configuration := { selected with pc := 2 }
  let moved : Configuration :=
    { checked with pc := 3, inputTape := checked.inputTape.moveRight }
  let rejected : Configuration := { moved with pc := 13 }
  have h0 : Step program source selected := by
    simp [Step, successors, next, program, source, atStart, selected,
      Instruction.next, Configuration.tape, hTrue]
  have h1 : Step program selected checked := by
    cases h : output.current with
    | none => exact False.elim (hCounter h)
    | some bit =>
        cases bit <;>
          simp [Step, successors, next, program, source, atStart,
            selected, checked, Instruction.next, Configuration.tape, h]
  have h2 : Step program checked moved := by
    simp [Step, successors, next, program, source, atStart, selected,
      checked, moved, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have h3 : Step program moved rejected := by
    simp [Step, successors, next, program, source, atStart, selected,
      checked, moved, rejected, Instruction.next, Configuration.tape, hBlank]
  exact ⟨_, ((((RunsFor.zero _).succ h0).succ h1).succ h2 |>.succ h3).trans
    (reject_run rejected rfl rfl), rfl, by simp [rejectFinish, rejected, moved, checked, selected, source, atStart, Tape.write], rfl⟩

private theorem marker_without_payload (input output : Tape)
    (hTrue : input.current = some true)
    (hCounter : output.current ≠ none)
    (hBlank : input.moveRight.current = none) :
    ∃ target, RunsFor program (atStart input output) target 6 ∧
      target.halted = true ∧ target.outputTape.current = some false  := by
  obtain ⟨target, run, hHalt, hStatus, _⟩ := marker_without_payload_layout input output hTrue hCounter hBlank
  exact ⟨target, run, hHalt, hStatus⟩

private theorem marker_payload (input output : Tape)
    (hTrue : input.current = some true)
    (hCounter : output.current ≠ none)
    (hPayload : input.moveRight.current ≠ none) :
    RunsFor program (atStart input output)
      (atStart input.moveRight.moveRight
        output.moveRight.moveRight.moveRight) 9 := by
  let source := atStart input output
  let selected : Configuration := { source with pc := 1 }
  let checked : Configuration := { selected with pc := 2 }
  let payload : Configuration :=
    { checked with pc := 3, inputTape := checked.inputTape.moveRight }
  let present : Configuration := { payload with pc := 4 }
  let movedInput : Configuration :=
    { present with pc := 5, inputTape := present.inputTape.moveRight }
  let first : Configuration :=
    { movedInput with pc := 6, outputTape := movedInput.outputTape.moveRight }
  let second : Configuration :=
    { first with pc := 7, outputTape := first.outputTape.moveRight }
  let third : Configuration :=
    { second with pc := 8, outputTape := second.outputTape.moveRight }
  have h0 : Step program source selected := by
    simp [Step, successors, next, program, source, atStart, selected,
      Instruction.next, Configuration.tape, hTrue]
  have h1 : Step program selected checked := by
    cases h : output.current with
    | none => exact False.elim (hCounter h)
    | some bit =>
        cases bit <;>
          simp [Step, successors, next, program, source, atStart,
            selected, checked, Instruction.next, Configuration.tape, h]
  have h2 : Step program checked payload := by
    simp [Step, successors, next, program, source, atStart, selected,
      checked, payload, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have h3 : Step program payload present := by
    cases h : input.moveRight.current with
    | none => exact False.elim (hPayload h)
    | some bit =>
        cases bit <;>
          simp [Step, successors, next, program, source, atStart,
            selected, checked, payload, present, Instruction.next,
            Configuration.tape, h]
  have h4 : Step program present movedInput := by
    simp [Step, successors, next, program, source, atStart, selected,
      checked, payload, present, movedInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h5 : Step program movedInput first := by
    simp [Step, successors, next, program, source, atStart, selected,
      checked, payload, present, movedInput, first, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h6 : Step program first second := by
    simp [Step, successors, next, program, source, atStart, selected,
      checked, payload, present, movedInput, first, second, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h7 : Step program second third := by
    simp [Step, successors, next, program, source, atStart, selected,
      checked, payload, present, movedInput, first, second, third,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h8 : Step program third
      (atStart input.moveRight.moveRight
        output.moveRight.moveRight.moveRight) := by
    simp [Step, successors, next, program, source, atStart, selected,
      checked, payload, present, movedInput, first, second, third,
      Instruction.next]
  exact (((((((((RunsFor.zero _).succ h0).succ h1).succ h2).succ h3).succ h4).succ h5).succ h6).succ h7).succ h8

theorem rejects_long (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter field tail : List Bool)
    (hCounter : counter.length = 3 * width)
    (hLong : width < field.length) :
    ∃ target used, used ≤ 9 * width + 4 ∧
      RunsFor program (start beforeInput beforeOutput counter field tail)
        target used ∧
      target.halted = true ∧ target.outputTape.current = some false := by
  induction width generalizing beforeInput beforeOutput counter field with
  | zero =>
      cases counter with
      | cons head rest => simp at hCounter
      | nil =>
          cases field with
          | nil => simp at hLong
          | cons bit rest =>
              have hTrue : (start beforeInput beforeOutput []
                  (bit :: rest) tail).inputTape.current = some true := by
                simp [start, FiniteBitEncoding.delimit, Tape.ofBits]
              have hEmpty : (start beforeInput beforeOutput []
                  (bit :: rest) tail).outputTape.current = none := by
                simp [start, Tape.ofBits]
              obtain ⟨target, hRun, hHalt, hStatus⟩ :=
                marker_without_counter _ _ hTrue hEmpty
              exact ⟨target, 4, by omega, hRun, hHalt, hStatus⟩
  | succ width ih =>
      cases field with
      | nil => simp at hLong
      | cons bit rest =>
          cases counter with
          | nil => simp at hCounter
          | cons a next =>
              cases next with
              | nil => simp at hCounter; omega
              | cons b next =>
                  cases next with
                  | nil => simp at hCounter; omega
                  | cons c remaining =>
                      have hRemaining : remaining.length = 3 * width := by
                        simp only [List.length_cons] at hCounter
                        omega
                      have hRest : width < rest.length := by
                        simp only [List.length_cons] at hLong
                        omega
                      obtain ⟨target, used, hUsed, hRun, hHalt, hStatus⟩ :=
                        ih (some bit :: some true :: beforeInput)
                          (some c :: some b :: some a :: beforeOutput)
                          remaining rest hRemaining hRest
                      exact ⟨target, 9 + used, by omega,
                        (one beforeInput beforeOutput a b c remaining bit rest tail).trans hRun,
                        hHalt, hStatus⟩

theorem rejects_short (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter field tail : List Bool)
    (hCounter : counter.length = 3 * width)
    (hShort : field.length < width) :
    ∃ target used, used ≤ 9 * field.length + 5 ∧
      RunsFor program (start beforeInput beforeOutput counter field tail)
        target used ∧
      target.halted = true ∧ target.outputTape.current = some false := by
  induction field generalizing beforeInput beforeOutput width counter with
  | nil =>
      cases width with
      | zero => simp at hShort
      | succ width =>
          cases counter with
          | nil => simp at hCounter
          | cons head remaining =>
              have hFalse : (start beforeInput beforeOutput
                  (head :: remaining) [] tail).inputTape.current = some false := by
                simp [start, FiniteBitEncoding.delimit, Tape.ofBits]
              obtain ⟨target, used, hUsed, hRun, hHalt, hStatus⟩ :=
                delimiter_run _ _ hFalse
              refine ⟨target, used, by simpa using hUsed, hRun, hHalt, ?_⟩
              cases head <;> simpa [start, Tape.ofBits] using hStatus
  | cons bit rest ih =>
      cases width with
      | zero => simp at hShort
      | succ width =>
          cases counter with
          | nil => simp at hCounter
          | cons a next =>
              cases next with
              | nil => simp at hCounter; omega
              | cons b next =>
                  cases next with
                  | nil => simp at hCounter; omega
                  | cons c remaining =>
                      have hRemaining : remaining.length = 3 * width := by
                        simp only [List.length_cons] at hCounter
                        omega
                      have hRest : rest.length < width := by
                        simp only [List.length_cons] at hShort
                        omega
                      obtain ⟨target, used, hUsed, hRun, hHalt, hStatus⟩ :=
                        ih (some bit :: some true :: beforeInput)
                          (some c :: some b :: some a :: beforeOutput)
                          width remaining hRemaining hRest
                      exact ⟨target, 9 + used, by simp; omega,
                        (one beforeInput beforeOutput a b c remaining bit rest tail).trans hRun,
                        hHalt, hStatus⟩

private instance rawWidthDecidable (raw : List Bool) (width : Nat) :
    Decidable (∃ field tail, FiniteBitEncoding.undelimit raw = some (field, tail) ∧ field.length = width) := by
  cases hParse : FiniteBitEncoding.undelimit raw with
  | none => exact isFalse (by simp [hParse])
  | some pair =>
      rcases pair with ⟨field, tail⟩
      exact decidable_of_iff (field.length = width) (by simp [hParse])

private def matchesWidth (raw : List Bool) (width : Nat) : Prop :=
  ∃ field tail, FiniteBitEncoding.undelimit raw = some (field, tail) ∧ field.length = width

private instance matchesWidthDecidable (raw : List Bool) (width : Nat) :
    Decidable (matchesWidth raw width) := by
  unfold matchesWidth
  infer_instance

private theorem matches_marker (bit : Bool) (rest : List Bool) (width : Nat) :
    matchesWidth (true :: bit :: rest) (width + 1) ↔ matchesWidth rest width := by
  cases h : FiniteBitEncoding.undelimit rest with
  | none => simp [matchesWidth, FiniteBitEncoding.undelimit, h]
  | some pair =>
      rcases pair with ⟨field, tail⟩
      simp [matchesWidth, FiniteBitEncoding.undelimit, h]

private theorem matches_marker_zero (bit : Bool) (rest : List Bool) :
    ¬ matchesWidth (true :: bit :: rest) 0 := by
  cases h : FiniteBitEncoding.undelimit rest with
  | none => simp [matchesWidth, FiniteBitEncoding.undelimit, h]
  | some pair =>
      rcases pair with ⟨field, tail⟩
      simp [matchesWidth, FiniteBitEncoding.undelimit, h]

/-- On every finite raw field, including missing delimiters and dangling
payload markers, the native status is true exactly for a complete field of
the advertised width. The bound charges the actual scanning transitions;
`undelimit` describes correctness and is not an executed machine opcode. -/
theorem runs_raw_layout (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter raw : List Bool)
    (hCounter : counter.length = 3 * width) :
    ∃ target used, used ≤ 9 * width + 6 ∧
      RunsFor program
        ({ inputTape := { Tape.ofBits raw with left := beforeInput },
           outputTape := { Tape.ofBits counter with left := beforeOutput } } : Configuration)
        target used ∧ target.halted = true ∧
      target.outputTape.current = some (decide
        (∃ field tail, FiniteBitEncoding.undelimit raw = some (field, tail) ∧ field.length = width)) ∧
      ∃ consumed suffix, counter = consumed ++ suffix ∧
        target.outputTape =
          { left := consumed.reverse.map some ++ beforeOutput,
            current := target.outputTape.current, right := (Tape.ofBits suffix).right } := by
  change ∃ target used, used ≤ 9 * width + 6 ∧
    RunsFor program (atStart { Tape.ofBits raw with left := beforeInput }
      { Tape.ofBits counter with left := beforeOutput }) target used ∧
      target.halted = true ∧ target.outputTape.current = some (decide (matchesWidth raw width)) ∧
      ∃ consumed suffix, counter = consumed ++ suffix ∧
        target.outputTape =
          { left := consumed.reverse.map some ++ beforeOutput,
            current := target.outputTape.current, right := (Tape.ofBits suffix).right }
  induction width generalizing beforeInput beforeOutput counter raw with
  | zero =>
      have hEmpty : counter = [] := List.length_eq_zero_iff.mp (by omega)
      subst counter
      cases raw with
      | nil =>
          obtain ⟨target, run, hHalt, hStatus, hLayout⟩ := blank_run_layout
            ({ Tape.ofBits [] with left := beforeInput })
            ({ Tape.ofBits [] with left := beforeOutput }) rfl
          refine ⟨target, 3, by omega, run, hHalt, by simpa [matchesWidth, FiniteBitEncoding.undelimit] using hStatus, ?_⟩
          refine ⟨[], [], rfl, ?_⟩
          rw [hLayout]
          simp [Tape.write, Tape.ofBits]
      | cons tag rest =>
          cases tag with
          | false =>
              obtain ⟨target, used, hUsed, run, hHalt, hStatus, hLayout⟩ := delimiter_run_layout
                ({ Tape.ofBits (false :: rest) with left := beforeInput })
                ({ Tape.ofBits [] with left := beforeOutput }) rfl
              refine ⟨target, used, by omega, run, hHalt, by simpa [matchesWidth, FiniteBitEncoding.undelimit, Tape.ofBits] using hStatus, ?_⟩
              refine ⟨[], [], rfl, ?_⟩
              rw [hLayout]
              simp [Tape.write, Tape.ofBits]
          | true =>
              obtain ⟨target, run, hHalt, hStatus, hLayout⟩ := marker_without_counter_layout
                ({ Tape.ofBits (true :: rest) with left := beforeInput })
                ({ Tape.ofBits [] with left := beforeOutput }) rfl rfl
              have hInvalid : ¬ matchesWidth (true :: rest) 0 := by
                cases rest with
                | nil => simp [matchesWidth, FiniteBitEncoding.undelimit]
                | cons bit remaining => exact matches_marker_zero bit remaining
              refine ⟨target, 4, by omega, run, hHalt, by simpa [hInvalid] using hStatus, ?_⟩
              refine ⟨[], [], rfl, ?_⟩
              rw [hLayout]
              simp [Tape.write, Tape.ofBits]
  | succ width ih =>
      cases counter with
      | nil => simp at hCounter
      | cons a next =>
          cases next with
          | nil => simp at hCounter; omega
          | cons b next =>
              cases next with
              | nil => simp at hCounter; omega
              | cons c remaining =>
                  have hRemaining : remaining.length = 3 * width := by
                    simp only [List.length_cons] at hCounter; omega
                  let input : Tape := { Tape.ofBits raw with left := beforeInput }
                  let output : Tape := { Tape.ofBits (a :: b :: c :: remaining) with left := beforeOutput }
                  cases raw with
                  | nil =>
                      obtain ⟨target, run, hHalt, hStatus, hLayout⟩ := blank_run_layout input output rfl
                      refine ⟨target, 3, by omega, run, hHalt,
                        by simpa [matchesWidth, FiniteBitEncoding.undelimit] using hStatus, ?_⟩
                      refine ⟨[], (a :: b :: c :: remaining), rfl, ?_⟩
                      rw [hLayout]
                      simp [output, Tape.write, Tape.ofBits]
                  | cons tag rest =>
                      cases tag with
                      | false =>
                          obtain ⟨target, used, hUsed, run, hHalt, hStatus, hLayout⟩ := delimiter_run_layout input output rfl
                          refine ⟨target, used, by omega, run, hHalt,
                            by cases a <;> simpa [matchesWidth, FiniteBitEncoding.undelimit, output, Tape.ofBits] using hStatus, ?_⟩
                          refine ⟨[], (a :: b :: c :: remaining), rfl, ?_⟩
                          rw [hLayout]
                          simp [output, Tape.write, Tape.ofBits]
                      | true =>
                          cases rest with
                          | nil =>
                              obtain ⟨target, run, hHalt, hStatus, hLayout⟩ := marker_without_payload_layout input output rfl
                                (by simp [output, Tape.ofBits]) (by simp [input, Tape.ofBits, Tape.moveRight])
                              refine ⟨target, 6, by omega, run, hHalt,
                                by simpa [matchesWidth, FiniteBitEncoding.undelimit] using hStatus, ?_⟩
                              refine ⟨[], (a :: b :: c :: remaining), rfl, ?_⟩
                              rw [hLayout]
                              simp [output, Tape.write, Tape.ofBits]
                          | cons bit rest =>
                              obtain ⟨target, used, hUsed, run, hHalt, hStatus, hLayout⟩ :=
                                ih (some bit :: some true :: beforeInput)
                                  (some c :: some b :: some a :: beforeOutput) remaining rest hRemaining
                              have step := marker_payload input output rfl
                                (by simp [output, Tape.ofBits])
                                (by simp [input, Tape.ofBits, Tape.moveRight])
                              have hJoin : atStart input.moveRight.moveRight output.moveRight.moveRight.moveRight =
                                  atStart { Tape.ofBits rest with left := some bit :: some true :: beforeInput }
                                    { Tape.ofBits remaining with left := some c :: some b :: some a :: beforeOutput } := by
                                cases rest <;> cases remaining <;>
                                  simp [atStart, input, output, Tape.ofBits, Tape.moveRight]
                              rw [hJoin] at step
                              refine ⟨target, 9 + used, by omega, step.trans run, hHalt,
                                by simpa only [matches_marker bit rest width] using hStatus, ?_⟩
                              obtain ⟨consumed, suffix, hParts, hTape⟩ := hLayout
                              refine ⟨a :: b :: c :: consumed, suffix, by simp [hParts], ?_⟩
                              simpa [List.reverse_cons, List.map_append, List.append_assoc] using hTape


-- Status-only API retained for existing callers.
theorem runs_raw_status (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter raw : List Bool)
    (hCounter : counter.length = 3 * width) :
    ∃ target used, used ≤ 9 * width + 6 ∧
      RunsFor program
        ({ inputTape := { Tape.ofBits raw with left := beforeInput },
           outputTape := { Tape.ofBits counter with left := beforeOutput } } : Configuration)
        target used ∧ target.halted = true ∧
      target.outputTape.current = some (decide
        (∃ field tail, FiniteBitEncoding.undelimit raw = some (field, tail) ∧ field.length = width)) := by
  obtain ⟨target, used, hUsed, run, hHalt, hStatus, _⟩ :=
    runs_raw_layout beforeInput beforeOutput width counter raw hCounter
  exact ⟨target, used, hUsed, run, hHalt, hStatus⟩

/-- Computable option-valued spelling of the same status specification.
This API can be used by outer parsers without a new existential-decidability
instance; the actual program and execution bound are unchanged. -/
theorem runs_raw_decision_layout (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter raw : List Bool) (hCounter : counter.length = 3 * width) :
    ∃ target used, used ≤ 9 * width + 6 ∧
      RunsFor program
        ({ inputTape := { Tape.ofBits raw with left := beforeInput },
           outputTape := { Tape.ofBits counter with left := beforeOutput } } : Configuration)
        target used ∧ target.halted = true ∧ target.outputTape.current = some
          ((FiniteBitEncoding.undelimit raw).any (fun pair => decide (pair.1.length = width))) ∧
      ∃ consumed suffix, counter = consumed ++ suffix ∧
        target.outputTape =
          { left := consumed.reverse.map some ++ beforeOutput,
            current := target.outputTape.current, right := (Tape.ofBits suffix).right } := by
  obtain ⟨target, used, hUsed, run, hHalt, hStatus, hLayout⟩ :=
    runs_raw_layout beforeInput beforeOutput width counter raw hCounter
  refine ⟨target, used, hUsed, run, hHalt, ?_, hLayout⟩
  cases hParse : FiniteBitEncoding.undelimit raw with
  | none => simpa [hParse] using hStatus
  | some pair =>
      rcases pair with ⟨field, tail⟩
      simpa [hParse] using hStatus

theorem runs_raw_decision (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter raw : List Bool) (hCounter : counter.length = 3 * width) :
    ∃ target used, used ≤ 9 * width + 6 ∧
      RunsFor program
        ({ inputTape := { Tape.ofBits raw with left := beforeInput },
           outputTape := { Tape.ofBits counter with left := beforeOutput } } : Configuration)
        target used ∧ target.halted = true ∧ target.outputTape.current = some
          ((FiniteBitEncoding.undelimit raw).any (fun pair => decide (pair.1.length = width))) := by
  obtain ⟨target, used, hUsed, run, hHalt, hStatus, _⟩ :=
    runs_raw_decision_layout beforeInput beforeOutput width counter raw hCounter
  exact ⟨target, used, hUsed, run, hHalt, hStatus⟩

/-- A successful halted operational run therefore exposes an actual
complete fixed-width field and its exact unconsumed suffix. No malformed
field can be accepted merely because a prefix has the expected length. -/
theorem field_of_accepted_run (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter raw : List Bool) (hCounter : counter.length = 3 * width)
    {target : Configuration} {used : Nat}
    (run : RunsFor program
      ({ inputTape := { Tape.ofBits raw with left := beforeInput },
         outputTape := { Tape.ofBits counter with left := beforeOutput } } : Configuration)
      target used)
    (hHalt : target.halted = true) (hAccept : target.outputTape.current = some true) :
    ∃ field tail, FiniteBitEncoding.delimit field ++ tail = raw ∧ field.length = width := by
  obtain ⟨checked, steps, _, checkRun, checkHalt, hStatus⟩ :=
    runs_raw_status beforeInput beforeOutput width counter raw hCounter
  have hSame := run.halted_finish_eq_of_no_randomBit checkRun hHalt checkHalt no_randomBit
  rw [← hSame, hAccept] at hStatus
  have hExists : ∃ field tail, FiniteBitEncoding.undelimit raw = some (field, tail) ∧ field.length = width := by
    simpa using hStatus.symm
  obtain ⟨field, tail, hParse, hLength⟩ := hExists
  exact ⟨field, tail, FiniteBitEncoding.delimit_append_of_undelimit hParse, hLength⟩

/-- A missing terminator or dangling payload marker always produces the
rejecting status, even when its already read prefix has the expected width. -/
theorem rejects_incomplete_field (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter raw : List Bool) (hCounter : counter.length = 3 * width)
    (hIncomplete : FiniteBitEncoding.undelimit raw = none) :
    ∃ target used, used ≤ 9 * width + 6 ∧
      RunsFor program
        ({ inputTape := { Tape.ofBits raw with left := beforeInput },
           outputTape := { Tape.ofBits counter with left := beforeOutput } } : Configuration)
        target used ∧ target.halted = true ∧ target.outputTape.current = some false := by
  obtain ⟨target, used, hUsed, run, hHalt, hStatus⟩ :=
    runs_raw_status beforeInput beforeOutput width counter raw hCounter
  exact ⟨target, used, hUsed, run, hHalt, by simpa [hIncomplete] using hStatus⟩

/-- Successful raw runs also retain the exact next-field position and
instance counter. This uses uniqueness of deterministic halted executions
of the same finite code; it does not install a reconstructed tape. -/
theorem layout_of_accepted_run (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter raw : List Bool) (hCounter : counter.length = 3 * width)
    {target : Configuration} {used : Nat}
    (run : RunsFor program
      ({ inputTape := { Tape.ofBits raw with left := beforeInput },
         outputTape := { Tape.ofBits counter with left := beforeOutput } } : Configuration)
      target used)
    (hHalt : target.halted = true) (hAccept : target.outputTape.current = some true) :
    ∃ field tail, FiniteBitEncoding.delimit field ++ tail = raw ∧ field.length = width ∧
      target.inputTape = (finish beforeInput beforeOutput counter field tail).inputTape ∧
      target.outputTape = (finish beforeInput beforeOutput counter field tail).outputTape := by
  obtain ⟨field, tail, hRaw, hWidth⟩ :=
    field_of_accepted_run beforeInput beforeOutput width counter raw hCounter run hHalt hAccept
  have matching := runs_matching_length beforeInput beforeOutput counter field tail (by omega)
  have hActual : RunsFor program (start beforeInput beforeOutput counter field tail) target used := by
    simpa only [← hRaw, start] using run
  have hSame := hActual.halted_finish_eq_of_no_randomBit matching hHalt rfl no_randomBit
  exact ⟨field, tail, hRaw, hWidth, congrArg Configuration.inputTape hSame,
    congrArg Configuration.outputTape hSame⟩

/-- If the instance block has exactly three cells per expected element bit,
the native status distinguishes exactly the fixed-width candidates. -/
theorem runs_width_status (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter field tail : List Bool)
    (hCounter : counter.length = 3 * width) :
    ∃ target used,
      used ≤ 9 * (width + field.length + 1) + 6 ∧
      RunsFor program (start beforeInput beforeOutput counter field tail)
        target used ∧
      target.halted = true ∧
      target.outputTape.current = some (decide (field.length = width)) := by
  obtain ⟨target, used, hUsed, run, hHalt, hStatus⟩ :=
    runs_raw_status beforeInput beforeOutput width counter
      (FiniteBitEncoding.delimit field ++ tail) hCounter
  exact ⟨target, used, by omega, run, hHalt, by simpa using hStatus⟩

theorem eval_width_status (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (counter field tail : List Bool)
    (hCounter : counter.length = 3 * width) :
    (evalConfigWithin program
      (start beforeInput beforeOutput counter field tail)
      (9 * (width + field.length + 1) + 6)).map
        (fun c => c.outputTape.current) =
      PMF.pure (some (decide (field.length = width))) := by
  obtain ⟨target, used, hUsed, hRun, hHalt, hStatus⟩ :=
    runs_width_status beforeInput beforeOutput width counter field tail hCounter
  have hAll := hRun.haltsFrom_of_no_randomBit hHalt no_randomBit (Nat.le_refl used)
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    hRun.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hStatus]

/-- The three-cell checker halts from every finite retained tape, including
truncated delimiters and malformed instance-code counters. The bound uses
the actual number of input tape cells; no validity premise is hidden. -/
theorem terminates_from_anyTape (input output : Tape) :
    ∃ target used, used ≤ 9 * (input.right.length + 1) + 6 ∧
      RunsFor program (atStart input output) target used ∧
      target.halted = true := by
  cases hCurrent : input.current with
  | none =>
      obtain ⟨target, hRun, hHalt, _⟩ := blank_run input output hCurrent
      exact ⟨target, 3, by omega, hRun, hHalt⟩
  | some bit =>
      cases bit with
      | false =>
          obtain ⟨target, used, hUsed, hRun, hHalt, _⟩ :=
            delimiter_run input output hCurrent
          exact ⟨target, used, by omega, hRun, hHalt⟩
      | true =>
          cases hOutput : output.current with
          | none =>
              obtain ⟨target, hRun, hHalt, _⟩ :=
                marker_without_counter input output hCurrent hOutput
              exact ⟨target, 4, by omega, hRun, hHalt⟩
          | some outputBit =>
              cases hRight : input.right with
              | nil =>
                  have hPayload : input.moveRight.current = none := by
                    simp [Tape.moveRight, hRight]
                  obtain ⟨target, hRun, hHalt, _⟩ :=
                    marker_without_payload input output hCurrent
                      (by simp [hOutput]) hPayload
                  exact ⟨target, 6, by omega, hRun, hHalt⟩
              | cons cell rest =>
                  cases cell with
                  | none =>
                      have hPayload : input.moveRight.current = none := by
                        simp [Tape.moveRight, hRight]
                      obtain ⟨target, hRun, hHalt, _⟩ :=
                        marker_without_payload input output hCurrent
                          (by simp [hOutput]) hPayload
                      exact ⟨target, 6, by omega, hRun, hHalt⟩
                  | some payload =>
                      have hPayload : input.moveRight.current ≠ none := by
                        simp [Tape.moveRight, hRight]
                      obtain ⟨target, used, hUsed, hRun, hHalt⟩ :=
                        terminates_from_anyTape input.moveRight.moveRight
                          output.moveRight.moveRight.moveRight
                      refine ⟨target, 9 + used, ?_,
                        (marker_payload input output hCurrent
                          (by simp [hOutput]) hPayload).trans hRun, hHalt⟩
                      cases rest <;> simp [Tape.moveRight, hRight] at hUsed ⊢ <;> omega
termination_by input.right.length
decreasing_by
  cases input
  cases rest <;> simp_all [Tape.moveRight]

end Machine.DelimitedTripleWidthCheck
