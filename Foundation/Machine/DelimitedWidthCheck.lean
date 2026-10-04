import Foundation.Machine.DelimitedInput

namespace Machine.DelimitedWidthCheck

/-- Compare the length of one self-delimiting field against an ordinary
counter already present on the output tape. A `true` marker consumes one
counter cell and one following payload bit. The terminating `false` is
accepted exactly when the counter is exhausted. Every read and movement is
a native one-cell instruction. -/
def program : Program :=
  [.branch .input 11 7 1,
   .branch .output 11 2 2,
   .moveRight .input,
   .branch .input 11 4 4,
   .moveRight .input,
   .moveRight .output,
   .jump 0,
   .branch .output 8 11 11,
   .moveRight .input,
   .write .output true,
   .halt,
   .write .output false,
   .halt]

theorem length : program.length = 13 := by decide

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

def start (beforeInput beforeOutput : List (Option Bool))
    (count : Nat) (field tail : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits (FiniteBitEncoding.delimit field ++ tail) with
      left := beforeInput },
    outputTape := { Tape.ofBits (List.replicate count false) with
      left := beforeOutput } }

def finish (beforeInput beforeOutput : List (Option Bool))
    (field tail : List Bool) : Configuration :=
  { pc := 10,
    inputTape := { Tape.ofBits tail with
      left := (FiniteBitEncoding.delimit field).reverse.map some ++ beforeInput },
    outputTape := ⟨(List.replicate field.length (some false)) ++ beforeOutput,
      some true, []⟩,
    halted := true }

private theorem one (beforeInput beforeOutput : List (Option Bool))
    (count : Nat) (bit : Bool) (rest tail : List Bool) :
    RunsFor program (start beforeInput beforeOutput (count + 1) (bit :: rest) tail)
      (start (some bit :: some true :: beforeInput)
        (some false :: beforeOutput) count rest tail) 7 := by
  let c := start beforeInput beforeOutput (count + 1) (bit :: rest) tail
  let marked : Configuration := { c with pc := 1 }
  let counted : Configuration := { marked with pc := 2 }
  let payload : Configuration :=
    { counted with pc := 3, inputTape := counted.inputTape.moveRight }
  let present : Configuration := { payload with pc := 4 }
  let nextInput : Configuration :=
    { present with pc := 5, inputTape := present.inputTape.moveRight }
  let nextOutput : Configuration :=
    { nextInput with pc := 6, outputTape := nextInput.outputTape.moveRight }
  have h0 : Step program c marked := by
    simp [Step, successors, next, program, start, c, marked,
      FiniteBitEncoding.delimit, Instruction.next, Configuration.tape,
      Tape.ofBits]
  have h1 : Step program marked counted := by
    simp [Step, successors, next, program, start, c, marked, counted,
      List.replicate_succ, Instruction.next, Configuration.tape, Tape.ofBits]
  have h2 : Step program counted payload := by
    simp [Step, successors, next, program, start, c, marked, counted, payload,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step program payload present := by
    cases bit <;>
      simp [Step, successors, next, program, start, c, marked, counted,
        payload, present, FiniteBitEncoding.delimit, Instruction.next,
        Configuration.tape, Tape.ofBits, Tape.moveRight]
  have h4 : Step program present nextInput := by
    simp [Step, successors, next, program, start, c, marked, counted,
      payload, present, nextInput,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h5 : Step program nextInput nextOutput := by
    simp [Step, successors, next, program, start, c, marked, counted,
      payload, present, nextInput, nextOutput,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h6 : Step program nextOutput
      (start (some bit :: some true :: beforeInput)
        (some false :: beforeOutput) count rest tail) := by
    cases count <;> cases rest <;> cases tail <;>
      simp [Step, successors, next, program, start, c, marked, counted,
        payload, present, nextInput, nextOutput,
        FiniteBitEncoding.delimit, List.replicate_succ,
        Instruction.next, Tape.ofBits, Tape.moveRight]
  exact (((((((RunsFor.zero _).succ h0).succ h1).succ h2).succ h3).succ h4).succ h5).succ h6

private theorem done (beforeInput beforeOutput : List (Option Bool))
    (tail : List Bool) :
    RunsFor program (start beforeInput beforeOutput 0 [] tail)
      (finish beforeInput beforeOutput [] tail) 5 := by
  let c := start beforeInput beforeOutput 0 [] tail
  let terminator : Configuration := { c with pc := 7 }
  let accepted : Configuration := { terminator with pc := 8 }
  let advanced : Configuration :=
    { accepted with pc := 9, inputTape := accepted.inputTape.moveRight }
  let written : Configuration :=
    { advanced with pc := 10, outputTape := advanced.outputTape.write (some true) }
  have h0 : Step program c terminator := by
    simp [Step, successors, next, program, start, c, terminator,
      FiniteBitEncoding.delimit, Instruction.next, Configuration.tape,
      Tape.ofBits]
  have h1 : Step program terminator accepted := by
    simp [Step, successors, next, program, start, c, terminator, accepted,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have h2 : Step program accepted advanced := by
    simp [Step, successors, next, program, start, c, terminator,
      accepted, advanced,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step program advanced written := by
    simp [Step, successors, next, program, start, c, terminator,
      accepted, advanced, written,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step program written (finish beforeInput beforeOutput [] tail) := by
    cases tail <;>
      simp [Step, successors, next, program, start, finish, c, terminator,
        accepted, advanced, written, FiniteBitEncoding.delimit,
        Instruction.next, Tape.ofBits, Tape.moveRight, Tape.write]
  exact (((((RunsFor.zero _).succ h0).succ h1).succ h2).succ h3).succ h4

/-- On a well-formed field, the finite width checker accepts exactly one
counter cell per payload bit. It consumes the delimiter and leaves the tail
at the input head. -/
theorem runs_valid (beforeInput beforeOutput : List (Option Bool))
    (field tail : List Bool) :
    RunsFor program (start beforeInput beforeOutput field.length field tail)
      (finish beforeInput beforeOutput field tail)
      (7 * field.length + 5) := by
  induction field generalizing beforeInput beforeOutput with
  | nil => simpa using done beforeInput beforeOutput tail
  | cons bit rest ih =>
      have hRun := (one beforeInput beforeOutput rest.length bit rest tail).trans
        (ih (some bit :: some true :: beforeInput)
          (some false :: beforeOutput))
      have hFinish : finish (some bit :: some true :: beforeInput)
          (some false :: beforeOutput) rest tail =
          finish beforeInput beforeOutput (bit :: rest) tail := by
        simp [finish, FiniteBitEncoding.delimit, List.replicate_succ',
          List.reverse_cons, List.map_append, List.append_assoc]
      rw [hFinish] at hRun
      simpa [List.length_cons, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hRun

private def atStart (input output : Tape) : Configuration :=
  { inputTape := input, outputTape := output }

private def rejectFinish (c : Configuration) : Configuration :=
  { c with pc := 12, outputTape := c.outputTape.write (some false), halted := true }

private def acceptFinish (c : Configuration) : Configuration :=
  { pc := 10, inputTape := c.inputTape.moveRight,
    outputTape := c.outputTape.write (some true), halted := true }

private theorem reject_run (c : Configuration)
    (hPc : c.pc = 11) (hActive : c.halted = false) :
    RunsFor program c (rejectFinish c) 2 := by
  let written : Configuration :=
    { c with pc := 12, outputTape := c.outputTape.write (some false) }
  have hWrite : Step program c written := by
    simp [Step, successors, next, program, hPc, hActive, written,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step program written (rejectFinish c) := by
    simp [Step, successors, next, program, written, rejectFinish, hActive,
      Instruction.next]
  exact ((RunsFor.zero c).succ hWrite).succ hHalt

private theorem accept_run (c : Configuration)
    (hPc : c.pc = 8) (hActive : c.halted = false) :
    RunsFor program c (acceptFinish c) 3 := by
  let moved : Configuration :=
    { c with pc := 9, inputTape := c.inputTape.moveRight }
  let written : Configuration :=
    { moved with pc := 10, outputTape := moved.outputTape.write (some true) }
  have hMove : Step program c moved := by
    simp [Step, successors, next, program, hPc, hActive, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hWrite : Step program moved written := by
    simp [Step, successors, next, program, moved, written, hActive,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hHalt : Step program written (acceptFinish c) := by
    simp [Step, successors, next, program, moved, written, acceptFinish, hActive,
      Instruction.next]
  exact (((RunsFor.zero c).succ hMove).succ hWrite).succ hHalt

private theorem blank_run (input output : Tape)
    (hBlank : input.current = none) :
    ∃ finish, RunsFor program (atStart input output) finish 3 ∧
      finish.halted = true := by
  let selected : Configuration := { atStart input output with pc := 11 }
  have hStep : Step program (atStart input output) selected := by
    simp [Step, successors, next, program, atStart, selected,
      Instruction.next, Configuration.tape, hBlank]
  exact ⟨_, ((RunsFor.zero _).succ hStep).trans
    (reject_run selected rfl rfl), rfl⟩

private theorem false_run (input output : Tape)
    (hFalse : input.current = some false) :
    ∃ finish used, used ≤ 5 ∧
      RunsFor program (atStart input output) finish used ∧
      finish.halted = true ∧
      finish.outputTape.current = some (output.current == none) := by
  let selected : Configuration := { atStart input output with pc := 7 }
  have hStep : Step program (atStart input output) selected := by
    simp [Step, successors, next, program, atStart, selected,
      Instruction.next, Configuration.tape, hFalse]
  cases hOutput : output.current with
  | none =>
      let accepted : Configuration := { selected with pc := 8 }
      have hBranch : Step program selected accepted := by
        simp [Step, successors, next, program, atStart, selected, accepted,
          Instruction.next, Configuration.tape, hOutput]
      exact ⟨_, 5, by omega, ((RunsFor.zero _).succ hStep |>.succ hBranch).trans
        (accept_run accepted rfl rfl), rfl,
        by simp [acceptFinish, atStart, selected, accepted, Tape.write]⟩
  | some bit =>
      let rejected : Configuration := { selected with pc := 11 }
      have hBranch : Step program selected rejected := by
        cases bit <;>
          simp [Step, successors, next, program, atStart, selected, rejected,
            Instruction.next, Configuration.tape, hOutput]
      exact ⟨_, 4, by omega, ((RunsFor.zero _).succ hStep |>.succ hBranch).trans
        (reject_run rejected rfl rfl), rfl,
        by simp [rejectFinish, atStart, selected, rejected, Tape.write]⟩

private theorem true_reject (input output : Tape)
    (hTrue : input.current = some true)
    (hOutput : output.current = none) :
    ∃ finish, RunsFor program (atStart input output) finish 4 ∧
      finish.halted = true ∧ finish.outputTape.current = some false := by
  let selected : Configuration := { atStart input output with pc := 1 }
  let rejected : Configuration := { selected with pc := 11 }
  have h0 : Step program (atStart input output) selected := by
    simp [Step, successors, next, program, atStart, selected,
      Instruction.next, Configuration.tape, hTrue]
  have h1 : Step program selected rejected := by
    simp [Step, successors, next, program, atStart, selected, rejected,
      Instruction.next, Configuration.tape, hOutput]
  exact ⟨_, ((RunsFor.zero _).succ h0 |>.succ h1).trans
    (reject_run rejected rfl rfl), rfl,
    by simp [rejectFinish, rejected, selected, atStart, Tape.write]⟩

private theorem true_dangling (input output : Tape)
    (hTrue : input.current = some true)
    (hOutput : output.current ≠ none)
    (hPayload : input.moveRight.current = none) :
    ∃ finish, RunsFor program (atStart input output) finish 6 ∧
      finish.halted = true := by
  let selected : Configuration := { atStart input output with pc := 1 }
  let checked : Configuration := { selected with pc := 2 }
  let moved : Configuration :=
    { checked with pc := 3, inputTape := checked.inputTape.moveRight }
  let rejected : Configuration := { moved with pc := 11 }
  have h0 : Step program (atStart input output) selected := by
    simp [Step, successors, next, program, atStart, selected,
      Instruction.next, Configuration.tape, hTrue]
  have h1 : Step program selected checked := by
    cases h : output.current with
    | none => exact False.elim (hOutput h)
    | some bit =>
        cases bit <;>
          simp [Step, successors, next, program, atStart, selected,
            checked, Instruction.next, Configuration.tape, h]
  have h2 : Step program checked moved := by
    simp [Step, successors, next, program, atStart, selected, checked, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step program moved rejected := by
    simp [Step, successors, next, program, atStart, selected, checked, moved,
      rejected, Instruction.next, Configuration.tape, hPayload]
  exact ⟨_, ((((RunsFor.zero _).succ h0).succ h1).succ h2 |>.succ h3).trans
    (reject_run rejected rfl rfl), rfl⟩

private theorem true_payload (input output : Tape)
    (hTrue : input.current = some true)
    (hOutput : output.current ≠ none)
    (hPayload : input.moveRight.current ≠ none) :
    RunsFor program (atStart input output)
      (atStart (input.moveRight.moveRight) output.moveRight) 7 := by
  let c := atStart input output
  let selected : Configuration := { c with pc := 1 }
  let checked : Configuration := { selected with pc := 2 }
  let moved : Configuration :=
    { checked with pc := 3, inputTape := checked.inputTape.moveRight }
  let present : Configuration := { moved with pc := 4 }
  let nextInput : Configuration :=
    { present with pc := 5, inputTape := present.inputTape.moveRight }
  let nextOutput : Configuration :=
    { nextInput with pc := 6, outputTape := nextInput.outputTape.moveRight }
  have h0 : Step program c selected := by
    simp [Step, successors, next, program, atStart, c, selected,
      Instruction.next, Configuration.tape, hTrue]
  have h1 : Step program selected checked := by
    cases h : output.current with
    | none => exact False.elim (hOutput h)
    | some bit =>
        cases bit <;>
          simp [Step, successors, next, program, atStart, c, selected,
            checked, Instruction.next, Configuration.tape, h]
  have h2 : Step program checked moved := by
    simp [Step, successors, next, program, atStart, c, selected, checked, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step program moved present := by
    cases h : input.moveRight.current with
    | none => exact False.elim (hPayload h)
    | some bit =>
        cases bit <;>
          simp [Step, successors, next, program, atStart, c, selected,
            checked, moved, present, Instruction.next, Configuration.tape, h]
  have h4 : Step program present nextInput := by
    simp [Step, successors, next, program, atStart, c, selected, checked,
      moved, present, nextInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h5 : Step program nextInput nextOutput := by
    simp [Step, successors, next, program, atStart, c, selected, checked,
      moved, present, nextInput, nextOutput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h6 : Step program nextOutput
      (atStart (input.moveRight.moveRight) output.moveRight) := by
    simp [Step, successors, next, program, atStart, c, selected, checked,
      moved, present, nextInput, nextOutput, Instruction.next]
  exact (((((((RunsFor.zero _).succ h0).succ h1).succ h2).succ h3).succ h4).succ h5).succ h6

/-- An overlong delimited payload is rejected by the counter before its
extra payload bits are accepted. The counter is part of the physical tape. -/
theorem rejects_too_long (beforeInput beforeOutput : List (Option Bool))
    (count : Nat) (field tail : List Bool) (hLength : count < field.length) :
    ∃ finish used, used ≤ 7 * count + 4 ∧
      RunsFor program (start beforeInput beforeOutput count field tail)
        finish used ∧
      finish.halted = true ∧ finish.outputTape.current = some false := by
  induction count generalizing beforeInput beforeOutput field with
  | zero =>
      cases field with
      | nil => simp at hLength
      | cons bit rest =>
          have hTrue : (start beforeInput beforeOutput 0
              (bit :: rest) tail).inputTape.current = some true := by
            simp [start, FiniteBitEncoding.delimit, Tape.ofBits]
          have hEmpty : (start beforeInput beforeOutput 0
              (bit :: rest) tail).outputTape.current = none := by
            simp [start, Tape.ofBits]
          obtain ⟨finish, hRun, hHalt, hRejected⟩ :=
            true_reject _ _ hTrue hEmpty
          exact ⟨finish, 4, by omega, hRun, hHalt, hRejected⟩
  | succ count ih =>
      cases field with
      | nil => simp at hLength
      | cons bit rest =>
          have hRest : count < rest.length := by
            simp only [List.length_cons] at hLength
            omega
          obtain ⟨finish, used, hUsed, hRun, hHalt, hRejected⟩ :=
            ih (some bit :: some true :: beforeInput)
              (some false :: beforeOutput) rest hRest
          exact ⟨finish, 7 + used, by omega,
            (one beforeInput beforeOutput count bit rest tail).trans hRun,
            hHalt, hRejected⟩

/-- An early delimiter is rejected while an unconsumed width cell remains. -/
theorem rejects_too_short (beforeInput beforeOutput : List (Option Bool))
    (count : Nat) (field tail : List Bool) (hLength : field.length < count) :
    ∃ finish used, used ≤ 7 * field.length + 5 ∧
      RunsFor program (start beforeInput beforeOutput count field tail)
        finish used ∧
      finish.halted = true ∧ finish.outputTape.current = some false := by
  induction field generalizing count beforeInput beforeOutput with
  | nil =>
      cases count with
      | zero => simp at hLength
      | succ count =>
          have hFalse : (start beforeInput beforeOutput (count + 1) [] tail).inputTape.current =
              some false := by
            simp [start, FiniteBitEncoding.delimit, Tape.ofBits]
          obtain ⟨finish, used, hUsed, hRun, hHalt, hStatus⟩ :=
            false_run _ _ hFalse
          refine ⟨finish, used, by simpa using hUsed, hRun, hHalt, ?_⟩
          simpa [start, Tape.ofBits, List.replicate_succ] using hStatus
  | cons bit rest ih =>
      cases count with
      | zero => simp at hLength
      | succ count =>
          have hRest : rest.length < count := by
            simp only [List.length_cons] at hLength
            omega
          obtain ⟨finish, used, hUsed, hRun, hHalt, hRejected⟩ :=
            ih (some bit :: some true :: beforeInput)
              (some false :: beforeOutput) count hRest
          exact ⟨finish, 7 + used, by simp; omega,
            (one beforeInput beforeOutput count bit rest tail).trans hRun,
            hHalt, hRejected⟩

/-- The native marker is true exactly when the physical counter has the
same width as a well-formed delimited field. This statement combines the
accepting and both rejecting traces without treating list length as an
instruction. -/
theorem runs_canonical (beforeInput beforeOutput : List (Option Bool))
    (count : Nat) (field tail : List Bool) :
    ∃ finish used,
      used ≤ 7 * (count + field.length + 1) + 6 ∧
      RunsFor program (start beforeInput beforeOutput count field tail)
        finish used ∧
      finish.halted = true ∧
      finish.outputTape.current = some (decide (count = field.length)) := by
  rcases lt_trichotomy count field.length with hShort | hEqual | hLong
  · obtain ⟨finish, used, hUsed, hRun, hHalt, hStatus⟩ :=
      rejects_too_long beforeInput beforeOutput count field tail hShort
    refine ⟨finish, used, by omega, hRun, hHalt, ?_⟩
    simpa [hShort.ne] using hStatus
  · subst count
    refine ⟨finish beforeInput beforeOutput field tail,
      7 * field.length + 5, by omega,
      runs_valid beforeInput beforeOutput field tail, rfl, ?_⟩
    simp [finish]
  · obtain ⟨finish, used, hUsed, hRun, hHalt, hStatus⟩ :=
      rejects_too_short beforeInput beforeOutput count field tail hLong
    refine ⟨finish, used, by omega, hRun, hHalt, ?_⟩
    simpa [hLong.ne'] using hStatus

/-- At one common budget the machine evaluator's status bit is exactly the
width comparison. This uses the halted native trace, not a list-length
oracle inside the instruction set. -/
theorem eval_canonical_status (beforeInput beforeOutput : List (Option Bool))
    (count : Nat) (field tail : List Bool) :
    (evalConfigWithin program
      (start beforeInput beforeOutput count field tail)
      (7 * (count + field.length + 1) + 6)).map
        (fun c => c.outputTape.current) =
      PMF.pure (some (decide (count = field.length))) := by
  obtain ⟨target, used, hUsed, hRun, hHalt, hStatus⟩ :=
    runs_canonical beforeInput beforeOutput count field tail
  have hAll := hRun.haltsFrom_of_no_randomBit hHalt no_randomBit (Nat.le_refl used)
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    hRun.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hStatus]

/-- The counter can contain arbitrary bits. The width checker observes only
whether each counter cell is blank, so a previously copied fixed-width
modulus code can serve directly as its counter. -/
def startCounter (beforeInput beforeOutput : List (Option Bool))
    (counter field tail : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits (FiniteBitEncoding.delimit field ++ tail) with
      left := beforeInput },
    outputTape := { Tape.ofBits counter with left := beforeOutput } }

def finishCounter (beforeInput beforeOutput : List (Option Bool))
    (counter field tail : List Bool) : Configuration :=
  { pc := 10,
    inputTape := { Tape.ofBits tail with
      left := (FiniteBitEncoding.delimit field).reverse.map some ++ beforeInput },
    outputTape := ⟨counter.reverse.map some ++ beforeOutput, some true, []⟩,
    halted := true }

private theorem oneCounter (beforeInput beforeOutput : List (Option Bool))
    (head : Bool) (counter : List Bool) (bit : Bool)
    (rest tail : List Bool) :
    RunsFor program
      (startCounter beforeInput beforeOutput (head :: counter)
        (bit :: rest) tail)
      (startCounter (some bit :: some true :: beforeInput)
        (some head :: beforeOutput) counter rest tail) 7 := by
  let c := startCounter beforeInput beforeOutput (head :: counter)
    (bit :: rest) tail
  let marked : Configuration := { c with pc := 1 }
  let counted : Configuration := { marked with pc := 2 }
  let payload : Configuration :=
    { counted with pc := 3, inputTape := counted.inputTape.moveRight }
  let present : Configuration := { payload with pc := 4 }
  let nextInput : Configuration :=
    { present with pc := 5, inputTape := present.inputTape.moveRight }
  let nextOutput : Configuration :=
    { nextInput with pc := 6, outputTape := nextInput.outputTape.moveRight }
  have h0 : Step program c marked := by
    simp [Step, successors, next, program, startCounter, c, marked,
      FiniteBitEncoding.delimit, Instruction.next, Configuration.tape,
      Tape.ofBits]
  have h1 : Step program marked counted := by
    cases head <;>
      simp [Step, successors, next, program, startCounter, c, marked,
        counted, Instruction.next, Configuration.tape, Tape.ofBits]
  have h2 : Step program counted payload := by
    simp [Step, successors, next, program, startCounter, c, marked,
      counted, payload, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have h3 : Step program payload present := by
    cases bit <;>
      simp [Step, successors, next, program, startCounter, c, marked,
        counted, payload, present, FiniteBitEncoding.delimit,
        Instruction.next, Configuration.tape, Tape.ofBits, Tape.moveRight]
  have h4 : Step program present nextInput := by
    simp [Step, successors, next, program, startCounter, c, marked,
      counted, payload, present, nextInput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h5 : Step program nextInput nextOutput := by
    simp [Step, successors, next, program, startCounter, c, marked,
      counted, payload, present, nextInput, nextOutput, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h6 : Step program nextOutput
      (startCounter (some bit :: some true :: beforeInput)
        (some head :: beforeOutput) counter rest tail) := by
    cases counter <;> cases rest <;> cases tail <;>
      simp [Step, successors, next, program, startCounter, c, marked,
        counted, payload, present, nextInput, nextOutput,
        FiniteBitEncoding.delimit, Instruction.next,
        Tape.ofBits, Tape.moveRight]
  exact (((((((RunsFor.zero _).succ h0).succ h1).succ h2).succ h3).succ h4).succ h5).succ h6

/-- A modulus bitstring may be used directly as the width counter. Its
numeric value is irrelevant; exactly its number of written cells matters. -/
theorem runs_matching_counter (beforeInput beforeOutput : List (Option Bool))
    (counter field tail : List Bool)
    (hLength : counter.length = field.length) :
    RunsFor program (startCounter beforeInput beforeOutput counter field tail)
      (finishCounter beforeInput beforeOutput counter field tail)
      (7 * field.length + 5) := by
  induction field generalizing counter beforeInput beforeOutput with
  | nil =>
      cases counter with
      | nil =>
          simpa [startCounter, start, finishCounter, finish] using
            done beforeInput beforeOutput tail
      | cons head rest => simp at hLength
  | cons bit rest ih =>
      cases counter with
      | nil => simp at hLength
      | cons head remaining =>
          have hRest : remaining.length = rest.length := by
            simpa using hLength
          have hRun := (oneCounter beforeInput beforeOutput head remaining
            bit rest tail).trans
              (ih (some bit :: some true :: beforeInput)
                (some head :: beforeOutput) remaining hRest)
          have hFinish : finishCounter (some bit :: some true :: beforeInput)
              (some head :: beforeOutput) remaining rest tail =
              finishCounter beforeInput beforeOutput (head :: remaining)
                (bit :: rest) tail := by
            simp [finishCounter, FiniteBitEncoding.delimit,
              List.reverse_cons, List.map_append, List.append_assoc]
          rw [hFinish] at hRun
          simpa [List.length_cons, Nat.mul_add, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hRun

theorem rejects_long_counter (beforeInput beforeOutput : List (Option Bool))
    (counter field tail : List Bool)
    (hLength : counter.length < field.length) :
    ∃ finish used, used ≤ 7 * counter.length + 4 ∧
      RunsFor program (startCounter beforeInput beforeOutput counter field tail)
        finish used ∧
      finish.halted = true ∧ finish.outputTape.current = some false := by
  induction counter generalizing beforeInput beforeOutput field with
  | nil =>
      cases field with
      | nil => simp at hLength
      | cons bit rest =>
          have hTrue : (startCounter beforeInput beforeOutput []
              (bit :: rest) tail).inputTape.current = some true := by
            simp [startCounter, FiniteBitEncoding.delimit, Tape.ofBits]
          have hEmpty : (startCounter beforeInput beforeOutput []
              (bit :: rest) tail).outputTape.current = none := by
            simp [startCounter, Tape.ofBits]
          obtain ⟨finish, hRun, hHalt, hRejected⟩ :=
            true_reject _ _ hTrue hEmpty
          exact ⟨finish, 4, by omega, hRun, hHalt, hRejected⟩
  | cons head remaining ih =>
      cases field with
      | nil => simp at hLength
      | cons bit rest =>
          have hRest : remaining.length < rest.length := by
            simp only [List.length_cons] at hLength
            omega
          obtain ⟨finish, used, hUsed, hRun, hHalt, hRejected⟩ :=
            ih (some bit :: some true :: beforeInput)
              (some head :: beforeOutput) rest hRest
          exact ⟨finish, 7 + used, by simp; omega,
            (oneCounter beforeInput beforeOutput head remaining bit rest tail).trans hRun,
            hHalt, hRejected⟩

theorem rejects_short_counter (beforeInput beforeOutput : List (Option Bool))
    (counter field tail : List Bool)
    (hLength : field.length < counter.length) :
    ∃ finish used, used ≤ 7 * field.length + 5 ∧
      RunsFor program (startCounter beforeInput beforeOutput counter field tail)
        finish used ∧
      finish.halted = true ∧ finish.outputTape.current = some false := by
  induction field generalizing counter beforeInput beforeOutput with
  | nil =>
      cases counter with
      | nil => simp at hLength
      | cons head rest =>
          have hFalse : (startCounter beforeInput beforeOutput
              (head :: rest) [] tail).inputTape.current = some false := by
            simp [startCounter, FiniteBitEncoding.delimit, Tape.ofBits]
          obtain ⟨finish, used, hUsed, hRun, hHalt, hStatus⟩ :=
            false_run _ _ hFalse
          refine ⟨finish, used, by simpa using hUsed, hRun, hHalt, ?_⟩
          cases head <;> simpa [startCounter, Tape.ofBits] using hStatus
  | cons bit rest ih =>
      cases counter with
      | nil => simp at hLength
      | cons head remaining =>
          have hRest : rest.length < remaining.length := by
            simp only [List.length_cons] at hLength
            omega
          obtain ⟨finish, used, hUsed, hRun, hHalt, hRejected⟩ :=
            ih (some bit :: some true :: beforeInput)
              (some head :: beforeOutput) remaining hRest
          exact ⟨finish, 7 + used, by simp; omega,
            (oneCounter beforeInput beforeOutput head remaining bit rest tail).trans hRun,
            hHalt, hRejected⟩

/-- Exact native width status when the counter contains arbitrary bits,
including a copied modulus code. -/
theorem runs_counter_status (beforeInput beforeOutput : List (Option Bool))
    (counter field tail : List Bool) :
    ∃ finish used,
      used ≤ 7 * (counter.length + field.length + 1) + 6 ∧
      RunsFor program
        (startCounter beforeInput beforeOutput counter field tail)
        finish used ∧
      finish.halted = true ∧
      finish.outputTape.current = some (decide (counter.length = field.length)) := by
  rcases lt_trichotomy counter.length field.length with hShort | hEqual | hLong
  · obtain ⟨finish, used, hUsed, hRun, hHalt, hStatus⟩ :=
      rejects_long_counter beforeInput beforeOutput counter field tail hShort
    refine ⟨finish, used, by omega, hRun, hHalt, ?_⟩
    simpa [hShort.ne] using hStatus
  · refine ⟨finishCounter beforeInput beforeOutput counter field tail,
      7 * field.length + 5, by omega,
      runs_matching_counter beforeInput beforeOutput counter field tail hEqual,
      rfl, ?_⟩
    simp [finishCounter, hEqual]
  · obtain ⟨finish, used, hUsed, hRun, hHalt, hStatus⟩ :=
      rejects_short_counter beforeInput beforeOutput counter field tail hLong
    refine ⟨finish, used, by omega, hRun, hHalt, ?_⟩
    simpa [hLong.ne'] using hStatus

theorem eval_counter_status (beforeInput beforeOutput : List (Option Bool))
    (counter field tail : List Bool) :
    (evalConfigWithin program
      (startCounter beforeInput beforeOutput counter field tail)
      (7 * (counter.length + field.length + 1) + 6)).map
        (fun c => c.outputTape.current) =
      PMF.pure (some (decide (counter.length = field.length))) := by
  obtain ⟨target, used, hUsed, hRun, hHalt, hStatus⟩ :=
    runs_counter_status beforeInput beforeOutput counter field tail
  have hAll := hRun.haltsFrom_of_no_randomBit hHalt no_randomBit (Nat.le_refl used)
  rw [evalConfigWithin_eq_of_le _ _ _ _ hUsed hAll,
    hRun.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit]
  simp [PMF.pure_map, hStatus]

/-- The same finite code terminates on arbitrary retained finite tapes.
It accepts only after the input delimiter and output width counter have both
been exhausted, and rejects malformed or mismatched fields. -/
theorem terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 7 * (input.right.length + 1) + 6 ∧
      RunsFor program (atStart input output) finish used ∧
      finish.halted = true := by
  cases hCurrent : input.current with
  | none =>
      obtain ⟨finish, hRun, hHalt⟩ := blank_run input output hCurrent
      exact ⟨finish, 3, by omega, hRun, hHalt⟩
  | some bit =>
      cases bit with
      | false =>
          obtain ⟨finish, used, hUsed, hRun, hHalt, _⟩ :=
            false_run input output hCurrent
          exact ⟨finish, used, by omega, hRun, hHalt⟩
      | true =>
          cases hOutput : output.current with
          | none =>
              obtain ⟨finish, hRun, hHalt, _⟩ :=
                true_reject input output hCurrent hOutput
              exact ⟨finish, 4, by omega, hRun, hHalt⟩
          | some outputBit =>
              cases hRight : input.right with
              | nil =>
                  have hPayload : input.moveRight.current = none := by
                    simp [Tape.moveRight, hRight]
                  obtain ⟨finish, hRun, hHalt⟩ :=
                    true_dangling input output hCurrent (by simp [hOutput]) hPayload
                  exact ⟨finish, 6, by omega, hRun, hHalt⟩
              | cons cell rest =>
                  cases cell with
                  | none =>
                      have hPayload : input.moveRight.current = none := by
                        simp [Tape.moveRight, hRight]
                      obtain ⟨finish, hRun, hHalt⟩ :=
                        true_dangling input output hCurrent (by simp [hOutput]) hPayload
                      exact ⟨finish, 6, by omega, hRun, hHalt⟩
                  | some payload =>
                      have hPayload : input.moveRight.current ≠ none := by
                        simp [Tape.moveRight, hRight]
                      obtain ⟨finish, used, hUsed, hRun, hHalt⟩ :=
                        terminates_from_anyTape input.moveRight.moveRight output.moveRight
                      refine ⟨finish, 7 + used, ?_,
                        (true_payload input output hCurrent (by simp [hOutput])
                          hPayload).trans hRun, hHalt⟩
                      cases rest <;> simp [Tape.moveRight, hRight] at hUsed ⊢ <;> omega
termination_by input.right.length
decreasing_by
  cases input
  cases rest <;> simp_all [Tape.moveRight]

end Machine.DelimitedWidthCheck
