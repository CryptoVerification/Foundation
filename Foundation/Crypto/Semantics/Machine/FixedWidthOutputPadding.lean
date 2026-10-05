import Foundation.Crypto.Semantics.Machine.BinaryEncoding
import Foundation.Crypto.Semantics.Machine.TapeEquivalence

namespace Machine.FixedWidthOutputPadding

/-- Retain every sampled low bit, then append zero high bits up to the unary
width on the input tape. Both heads start at the first bit. This is a native
postprocessing routine, not a mathematical serialization instruction. -/
def program : Program :=
  [.branch .output 4 1 1, .moveRight .input, .moveRight .output, .jump 0,
   .branch .input 9 5 5, .write .output false, .moveRight .input,
   .moveRight .output, .jump 4, .halt]

private theorem replicate_cons_append {α : Type*} (count : Nat) (a : α) (before : List α) :
    List.replicate count a ++ a :: before = a :: (List.replicate count a ++ before) := by
  rw [← List.singleton_append, ← List.append_assoc, ← List.replicate_succ']
  rw [List.replicate_succ, List.cons_append]

private def scanStart (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (bits : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits (List.replicate width true) with left := beforeInput },
    outputTape := { Tape.ofBits bits with left := beforeOutput } }

private def scanFinish (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (bits : List Bool) : Configuration :=
  { pc := 4,
    inputTape := { Tape.ofBits (List.replicate (width-bits.length) true) with
      left := List.replicate bits.length (some true) ++ beforeInput },
    outputTape := { left := bits.reverse.map some ++ beforeOutput } }

private theorem scan_runs (beforeInput beforeOutput : List (Option Bool))
    (width : Nat) (bits : List Bool) (hWidth : bits.length ≤ width) :
    RunsFor program (scanStart beforeInput beforeOutput width bits)
      (scanFinish beforeInput beforeOutput width bits) (4*bits.length+1) := by
  induction bits generalizing width beforeInput beforeOutput with
  | nil =>
    have step : Step program (scanStart beforeInput beforeOutput width [])
        (scanFinish beforeInput beforeOutput width []) := by
      simp [Step, successors, next, program, scanStart, scanFinish, Tape.ofBits,
        Instruction.next, Configuration.tape]
    exact (RunsFor.zero _).succ step
  | cons bit rest ih =>
    cases width with
    | zero => simp at hWidth
    | succ width =>
      let start := scanStart beforeInput beforeOutput (width+1) (bit::rest)
      let selected := { start with pc := 1 }
      let movedInput := { selected with pc := 2, inputTape := selected.inputTape.moveRight }
      let movedOutput := { movedInput with pc := 3, outputTape := movedInput.outputTape.moveRight }
      have r₁ : Step program start selected := by
        cases bit <;> simp [Step, successors, next, program, start, selected, scanStart,
          Instruction.next, Configuration.tape, Tape.ofBits]
      have r₂ : Step program selected movedInput := by
        simp [Step, successors, next, program, start, selected, movedInput,
          Instruction.next, Configuration.updateTape, Configuration.advance, scanStart, start, selected]
      have r₃ : Step program movedInput movedOutput := by
        simp [Step, successors, next, program, movedInput, movedOutput,
          Instruction.next, Configuration.updateTape, Configuration.advance, scanStart, start, selected]
      have r₄ : Step program movedOutput
          (scanStart (some true::beforeInput) (some bit::beforeOutput) width rest) := by
        cases width <;> cases rest <;>
          simp [Step, successors, next, program, start, selected, movedInput, movedOutput,
            scanStart, Instruction.next, Tape.ofBits, Tape.moveRight,
            List.replicate_succ, Configuration.advance]
      have hRest : rest.length ≤ width := by simp only [List.length_cons] at hWidth; omega
      have run := ((((RunsFor.zero _).succ r₁).succ r₂).succ r₃).succ r₄
      have hFinish : scanFinish (some true::beforeInput) (some bit::beforeOutput) width rest =
          scanFinish beforeInput beforeOutput (width+1) (bit::rest) := by
        simp [scanFinish, List.reverse_cons, List.map_append, List.append_assoc,
          List.replicate_succ, Nat.add_sub_add_right, replicate_cons_append]
      have result := run.trans (ih _ _ width hRest)
      rw [hFinish] at result
      convert result using 1 <;> simp only [start, List.length_cons] <;> omega

private def fillStart (beforeInput beforeOutput : List (Option Bool)) (width : Nat) : Configuration :=
  { pc := 4,
    inputTape := { Tape.ofBits (List.replicate width true) with left := beforeInput },
    outputTape := { left := beforeOutput } }

private def fillFinish (beforeInput beforeOutput : List (Option Bool)) (width : Nat) : Configuration :=
  { pc := 9, halted := true,
    inputTape := { left := List.replicate width (some true) ++ beforeInput },
    outputTape := { left := List.replicate width (some false) ++ beforeOutput } }

private theorem fill_runs (beforeInput beforeOutput : List (Option Bool)) (width : Nat) :
    RunsFor program (fillStart beforeInput beforeOutput width)
      (fillFinish beforeInput beforeOutput width) (5*width+2) := by
  induction width generalizing beforeInput beforeOutput with
  | zero =>
    let start := fillStart beforeInput beforeOutput 0
    let selected := { start with pc := 9 }
    have r₁ : Step program start selected := by
      simp [Step, successors, next, program, start, selected, fillStart,
        Instruction.next, Configuration.tape, Tape.ofBits]
    have r₂ : Step program selected (fillFinish beforeInput beforeOutput 0) := by
      simp [Step, successors, next, program, selected, start, fillStart, fillFinish,
        Instruction.next, Tape.ofBits]
    exact ((RunsFor.zero _).succ r₁).succ r₂
  | succ width ih =>
    let start := fillStart beforeInput beforeOutput (width+1)
    let selected := { start with pc := 5 }
    let written := { selected with pc := 6, outputTape := selected.outputTape.write (some false) }
    let movedInput := { written with pc := 7, inputTape := written.inputTape.moveRight }
    let movedOutput := { movedInput with pc := 8, outputTape := movedInput.outputTape.moveRight }
    have r₁ : Step program start selected := by
      simp [Step, successors, next, program, start, selected, fillStart,
        Instruction.next, Configuration.tape, Tape.ofBits, List.replicate_succ]
    have r₂ : Step program selected written := by
      simp [Step, successors, next, program, selected, written, Instruction.next,
        Configuration.updateTape, Configuration.advance, fillStart, start, selected, written]
    have r₃ : Step program written movedInput := by
      simp [Step, successors, next, program, written, movedInput, Instruction.next,
        Configuration.updateTape, Configuration.advance, fillStart, start, selected, written]
    have r₄ : Step program movedInput movedOutput := by
      simp [Step, successors, next, program, movedInput, movedOutput, Instruction.next,
        Configuration.updateTape, Configuration.advance, fillStart, start, selected, written]
    have r₅ : Step program movedOutput
        (fillStart (some true::beforeInput) (some false::beforeOutput) width) := by
      cases width <;>
        simp [Step, successors, next, program, start, selected, written, movedInput, movedOutput,
          fillStart, Tape.ofBits, Tape.moveRight, Tape.write, List.replicate_succ,
          Instruction.next, Configuration.advance]
    have hFinish : fillFinish (some true::beforeInput) (some false::beforeOutput) width =
        fillFinish beforeInput beforeOutput (width+1) := by
      simp [fillFinish, List.replicate_succ, replicate_cons_append]
    have run := (((((RunsFor.zero _).succ r₁).succ r₂).succ r₃).succ r₄).succ r₅
    have result := run.trans (ih _ _)
    rw [hFinish] at result
    change RunsFor program (fillStart beforeInput beforeOutput (width+1)) _ _ at result
    convert result using 1 <;> omega

/-- The sampled bits are preserved and only high zeros are appended by actual
transitions. A unary counter fixes the full output width. -/
theorem runs (width : Nat) (bits : List Bool) (hWidth : bits.length ≤ width) :
    ∃ target used, used ≤ 5*width+3 ∧
      RunsFor program ({ inputTape := Tape.ofBits (List.replicate width true), outputTape := Tape.ofBits bits } : Configuration) target used ∧
      target.halted = true ∧ target.outputBits = bits ++ List.replicate (width-bits.length) false := by
  have first := scan_runs [] [] width bits hWidth
  have second := fill_runs (List.replicate bits.length (some true))
    (bits.reverse.map some) (width-bits.length)
  have hJoin : scanFinish [] [] width bits =
      fillStart (List.replicate bits.length (some true)) (bits.reverse.map some) (width-bits.length) := by
    simp [scanFinish, fillStart]
  rw [hJoin] at first
  have run := first.trans second
  have hStart : scanStart [] [] width bits =
      ({ inputTape := Tape.ofBits (List.replicate width true), outputTape := Tape.ofBits bits } : Configuration) := by
    cases width <;> cases bits <;> rfl
  rw [hStart] at run
  refine ⟨fillFinish (List.replicate bits.length (some true))
    (bits.reverse.map some) (width-bits.length), 4*bits.length+1+(5*(width-bits.length)+2),
    by omega, run, rfl, ?_⟩
  simp [fillFinish, Configuration.outputBits, Tape.bits, List.reverse_append,
    List.filterMap_append]

/-- This native padding yields exactly the project's fixed-width scalar codec. -/
theorem output_eq_encode (width : Nat) (bits : List Bool) (hWidth : bits.length ≤ width) :
    bits ++ List.replicate (width-bits.length) false = Binary.encode width (Binary.value bits) := by
  have hLength : (bits ++ List.replicate (width-bits.length) false).length = width := by
    simp only [List.length_append, List.length_replicate]; omega
  have hZero : Binary.value (List.replicate (width-bits.length) false) = 0 := by
    induction (width-bits.length) with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, Binary.value, ih]
  have h := Binary.encode_value (bits ++ List.replicate (width-bits.length) false)
  rw [hLength, Binary.value_append, hZero] at h
  simpa using h.symm

/-- The operational output itself is the fixed-width code; no separate
mathematical decoder is applied to the machine's result. -/
theorem runs_encoded (width : Nat) (bits : List Bool) (hWidth : bits.length ≤ width) :
    ∃ target used, used ≤ 5*width+3 ∧
      RunsFor program
        ({ inputTape := Tape.ofBits (List.replicate width true), outputTape := Tape.ofBits bits } : Configuration)
        target used ∧ target.halted = true ∧
      target.outputBits = Binary.encode width (Binary.value bits) := by
  obtain ⟨target, used, hUsed, run, hHalt, hOutput⟩ := runs width bits hWidth
  exact ⟨target, used, hUsed, run, hHalt, hOutput.trans (output_eq_encode width bits hWidth)⟩

/-- Padding uses only the counter above its protecting blank. Caller data
below that blank remains physically present on the input tape, allowing
later arithmetic to recover saved public parameters. -/
theorem runs_encoded_saved_layout (before : List (Option Bool)) (width : Nat) (bits : List Bool)
    (hWidth : bits.length ≤ width) :
    ∃ target used, used ≤ 5*width+3 ∧
      RunsFor program
        ({ inputTape := {Tape.ofBits (List.replicate width true) with left := none::before},
           outputTape := Tape.ofBits bits } : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape = {left := List.replicate width (some true) ++ none::before} ∧
      target.outputBits = Binary.encode width (Binary.value bits) ∧
      target.outputTape = {left := (Binary.encode width (Binary.value bits)).reverse.map some} := by
  have first := scan_runs (none::before) [] width bits hWidth
  have second := fill_runs (List.replicate bits.length (some true) ++ none::before)
    (bits.reverse.map some) (width-bits.length)
  have middle : scanFinish (none::before) [] width bits =
      fillStart (List.replicate bits.length (some true) ++ none::before)
        (bits.reverse.map some) (width-bits.length) := by
    simp [scanFinish, fillStart]
  rw [middle] at first
  have run := first.trans second
  have start : scanStart (none::before) [] width bits =
      ({inputTape := {Tape.ofBits (List.replicate width true) with left := none::before},
        outputTape := Tape.ofBits bits} : Configuration) := by
    cases width <;> cases bits <;> rfl
  rw [start] at run
  refine ⟨_, 4*bits.length+1+(5*(width-bits.length)+2), by omega, run, rfl, ?_, ?_⟩
  · have count : width-bits.length+bits.length = width := by omega
    simp [fillFinish, ← List.append_assoc, ← List.replicate_add, count]
  · constructor
    · simpa [fillFinish, Configuration.outputBits, Tape.bits, List.reverse_append,
        List.filterMap_append] using output_eq_encode width bits hWidth
    · rw [← output_eq_encode width bits hWidth]
      simp [fillFinish, List.reverse_append, List.map_append]

theorem runs_encoded_saved (before : List (Option Bool)) (width : Nat) (bits : List Bool)
    (hWidth : bits.length ≤ width) :
    ∃ target used, used ≤ 5*width+3 ∧
      RunsFor program
        ({ inputTape := {Tape.ofBits (List.replicate width true) with left := none::before},
           outputTape := Tape.ofBits bits } : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape = {left := List.replicate width (some true) ++ none::before} ∧
      target.outputBits = Binary.encode width (Binary.value bits) := by
  obtain ⟨target, used, bound, run, halted, input, bits, _⟩ :=
    runs_encoded_saved_layout before width bits hWidth
  exact ⟨target, used, bound, run, halted, input, bits⟩

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  simp [program]

end Machine.FixedWidthOutputPadding
