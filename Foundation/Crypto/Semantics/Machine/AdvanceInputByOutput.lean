import Foundation.Crypto.Semantics.Machine.TapeEquivalence

namespace Machine.AdvanceInputByOutput

/-- Use the other tape's bit block as a physical width counter. Neither
block is rewritten. This positions an input head at the next fixed-width
field without treating a length computation as a machine instruction. -/
def program : Program :=
  [.branch .output 4 1 1, .moveRight .input, .moveRight .output, .jump 0, .halt]

def start (beforeInput beforeOutput : List (Option Bool))
    (field following counter : List Bool) : Configuration :=
  {inputTape := {Tape.ofBits (field++following) with left := beforeInput},
   outputTape := {Tape.ofBits counter with left := beforeOutput}}

def finish (beforeInput beforeOutput : List (Option Bool))
    (field following counter : List Bool) : Configuration :=
  {pc := 4, halted := true,
   inputTape := {Tape.ofBits following with left := field.reverse.map some ++ beforeInput},
   outputTape := {left := counter.reverse.map some ++ beforeOutput}}

theorem runs (beforeInput beforeOutput : List (Option Bool))
    (field following counter : List Bool) (hLength : field.length = counter.length) :
    RunsFor program (start beforeInput beforeOutput field following counter)
      (finish beforeInput beforeOutput field following counter) (4*counter.length+2) := by
  induction counter generalizing field beforeInput beforeOutput with
  | nil =>
    have empty : field = [] := List.length_eq_zero_iff.mp (by simpa using hLength)
    subst field
    let first := start beforeInput beforeOutput [] following []
    have one : Step program first {first with pc := 4} := by
      simp [Step, successors, next, program, first, start, Tape.ofBits, Instruction.next, Configuration.tape]
    have two : Step program {first with pc := 4} (finish beforeInput beforeOutput [] following []) := by
      simp [Step, successors, next, program, first, start, finish, Tape.ofBits, Instruction.next]
    exact ((RunsFor.zero _).succ one).succ two
  | cons bit rest ih =>
    cases field with
    | nil => simp at hLength
    | cons value tail =>
      have lengths : tail.length = rest.length := by simpa using hLength
      let first := start beforeInput beforeOutput (value::tail) following (bit::rest)
      let selected := {first with pc := 1}
      let inputMoved := {first with pc := 2, inputTape := first.inputTape.moveRight}
      let outputMoved := {inputMoved with pc := 3, outputTape := inputMoved.outputTape.moveRight}
      have one : Step program first selected := by
        cases bit <;> simp [Step, successors, next, program, first, selected, start, Tape.ofBits, Instruction.next, Configuration.tape]
      have two : Step program selected inputMoved := by
        simp [Step, successors, next, program, selected, inputMoved, first, start, Instruction.next, Configuration.updateTape, Configuration.advance]
      have three : Step program inputMoved outputMoved := by
        simp [Step, successors, next, program, inputMoved, outputMoved, first, start, Instruction.next, Configuration.updateTape, Configuration.advance]
      have four : Step program outputMoved
          (start (some value::beforeInput) (some bit::beforeOutput) tail following rest) := by
        cases tail <;> cases rest <;> cases following <;>
          simp [Step, successors, next, program, outputMoved, inputMoved, first,
            start, Tape.ofBits, Tape.moveRight, Instruction.next]
      have joined := ((((RunsFor.zero _).succ one).succ two).succ three).succ four
      have same : finish (some value::beforeInput) (some bit::beforeOutput) tail following rest =
          finish beforeInput beforeOutput (value::tail) following (bit::rest) := by
        simp [finish, List.reverse_cons, List.map_append, List.append_assoc]
      have result := joined.trans (ih _ _ _ lengths)
      rw [same] at result
      convert result using 1 <;> simp only [List.length_cons] <;> omega

def startAny (input : Tape) (before : List (Option Bool)) (counter : List Bool) : Configuration :=
  {inputTape := input, outputTape := {Tape.ofBits counter with left := before}}

def finishAny (input : Tape) (before : List (Option Bool)) (counter : List Bool) : Configuration :=
  {pc := 4, halted := true, inputTape := (Tape.moveRight^[counter.length]) input,
    outputTape := {left := counter.reverse.map some ++ before}}

theorem runs_any (input : Tape) (before : List (Option Bool)) (counter : List Bool) :
    RunsFor program (startAny input before counter) (finishAny input before counter) (4*counter.length+2) := by
  induction counter generalizing input before with
  | nil =>
    let first := startAny input before []
    have one : Step program first {first with pc := 4} := by
      simp [Step, successors, next, program, first, startAny, Tape.ofBits, Instruction.next, Configuration.tape]
    have two : Step program {first with pc := 4} (finishAny input before []) := by
      simp [Step, successors, next, program, first, startAny, finishAny, Tape.ofBits, Instruction.next]
    exact ((RunsFor.zero _).succ one).succ two
  | cons bit rest ih =>
    let first := startAny input before (bit::rest)
    let selected := {first with pc := 1}
    let moved := {first with pc := 2, inputTape := input.moveRight}
    let outputMoved := {moved with pc := 3, outputTape := moved.outputTape.moveRight}
    have one : Step program first selected := by
      cases bit <;> simp [Step, successors, next, program, first, selected, startAny, Tape.ofBits, Instruction.next, Configuration.tape]
    have two : Step program selected moved := by
      simp [Step, successors, next, program, selected, moved, first, startAny, Instruction.next, Configuration.updateTape, Configuration.advance]
    have three : Step program moved outputMoved := by
      simp [Step, successors, next, program, moved, outputMoved, first, startAny, Instruction.next, Configuration.updateTape, Configuration.advance]
    have four : Step program outputMoved (startAny input.moveRight (some bit::before) rest) := by
      cases rest <;> simp [Step, successors, next, program, outputMoved, moved, first,
        startAny, Tape.ofBits, Tape.moveRight, Instruction.next]
    have prefixRun := ((((RunsFor.zero _).succ one).succ two).succ three).succ four
    have same : finishAny input.moveRight (some bit::before) rest = finishAny input before (bit::rest) := by
      simp [finishAny, Function.iterate_succ_apply, List.reverse_cons, List.map_append, List.append_assoc]
    have result := prefixRun.trans (ih input.moveRight (some bit::before))
    rw [same] at result
    convert result using 1 <;> simp only [List.length_cons] <;> omega

private def cellsAt (before rest : List (Option Bool)) : Tape :=
  {({right := rest} : Tape).moveRight with left := before}

private theorem advance_cells (before rest : List (Option Bool)) (bits : List Bool) :
    (Tape.moveRight^[bits.length]) (cellsAt before (bits.map some ++ rest)) =
      cellsAt (bits.reverse.map some ++ before) rest := by
  induction bits generalizing before with
  | nil => simp [cellsAt]
  | cons bit bits ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have moved : (cellsAt before ((bit::bits).map some ++ rest)).moveRight =
        cellsAt (some bit::before) (bits.map some ++ rest) := by
      cases h : bits.map some ++ rest <;> simp [cellsAt, Tape.moveRight, h]
    rw [moved, ih]
    simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Fixed-width scanning retains all following physical cells, including
blank separators and previously returned arithmetic results. -/
theorem runs_cells (before beforeOutput rest : List (Option Bool))
    (field counter : List Bool) (hLength : field.length = counter.length) :
    RunsFor program
      ({inputTape := {({right := field.map some ++ rest} : Tape).moveRight with left := before},
        outputTape := {Tape.ofBits counter with left := beforeOutput}} : Configuration)
      ({pc := 4, halted := true, inputTape := {({right := rest} : Tape).moveRight with left := field.reverse.map some ++ before},
        outputTape := {left := counter.reverse.map some ++ beforeOutput}} : Configuration)
      (4*counter.length+2) := by
  have run := runs_any (cellsAt before (field.map some ++ rest)) beforeOutput counter
  dsimp only [startAny, finishAny] at run
  rw [← hLength, advance_cells] at run
  simpa only [hLength, cellsAt] using run

private theorem advance_option_cells (before rest field : List (Option Bool)) :
    (Tape.moveRight^[field.length]) (cellsAt before (field++rest)) =
      cellsAt (field.reverse++before) rest := by
  induction field generalizing before with
  | nil => simp [cellsAt]
  | cons cell field ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have moved : (cellsAt before ((cell::field)++rest)).moveRight = cellsAt (cell::before) (field++rest) := by
      cases h : field++rest <;> simp [cellsAt,Tape.moveRight,h]
    rw [moved,ih]
    simp [List.reverse_cons,List.append_assoc]

/-- The output payload counts every physical input cell, including blanks.
This does not stop early at a guard and does not inspect unread values. -/
theorem runs_option_cells (before beforeOutput rest field : List (Option Bool))
    (counter : List Bool) (hLength : field.length = counter.length) :
    RunsFor program
      ({inputTape := {({right := field++rest} : Tape).moveRight with left := before},outputTape := {Tape.ofBits counter with left := beforeOutput}} : Configuration)
      ({pc := 4,halted := true,inputTape := {({right := rest} : Tape).moveRight with left := field.reverse++before},outputTape := {left := counter.reverse.map some ++ beforeOutput}} : Configuration)
      (4*counter.length+2) := by
  have run := runs_any (cellsAt before (field++rest)) beforeOutput counter
  dsimp only [startAny,finishAny] at run
  rw [←hLength,advance_option_cells] at run
  simpa only [hLength,cellsAt] using run

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by simp [program]

end Machine.AdvanceInputByOutput
