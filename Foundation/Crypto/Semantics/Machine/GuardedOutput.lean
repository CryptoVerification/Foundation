import Foundation.Crypto.Semantics.Machine.GuardedTransfer
import Foundation.Crypto.Semantics.Machine.BitstringCopy
import Foundation.Crypto.Semantics.Machine.BitstringRewind

namespace Machine.GuardedCompiler

open VirtualCell

/-- Decode a guarded output region into a fresh input scratch region.
Logical blanks `00` are skipped, and each word `1b` contributes the bit `b`.
Both physical cells of every inspected word are erased by ordinary opcodes.
The `01` guard and caller prefix remain untouched. This routine requires the
output head at the first logical word and blank input cells from its head
onwards; preparing those positions is a separate charged operation. -/
def decodeRegion : Program :=
  [.branch .output 20 1 7,
   .erase .output, .moveRight .output, .branch .output 20 4 20,
   .erase .output, .moveRight .output, .jump 0,
   .erase .output, .moveRight .output, .branch .output 20 10 15,
   .write .input false, .moveRight .input,
   .erase .output, .moveRight .output, .jump 0,
   .write .input true, .moveRight .input,
   .erase .output, .moveRight .output, .jump 0,
   .halt]

private def decodingOutput (before : List (Option Bool)) (erased : Nat) :
    List (Option Bool) → Tape
  | [] => { left := List.replicate (2 * erased) none ++ some true :: some false :: before }
  | cell :: rest => pairTape (code cell)
      (List.replicate (2 * erased) none ++ some true :: some false :: before) (encodedCells rest)

private def decodingState (beforeInput beforeOutput : List (Option Bool))
    (copied remaining : List (Option Bool)) : Configuration :=
  { inputTape := { left := (copied.filterMap id).reverse.map some ++ beforeInput },
    outputTape := decodingOutput beforeOutput copied.length remaining }

def decodeRegionStart (beforeInput beforeOutput : List (Option Bool))
    (cells : List (Option Bool)) : Configuration :=
  decodingState beforeInput beforeOutput [] cells

/-- All source words have been erased, including logical blank words.
Only the data bits were appended to the input scratch region. Both heads
are at its unwritten right frontier; the original output guard survives. -/
def decodeRegionFinish (beforeInput beforeOutput : List (Option Bool))
    (cells : List (Option Bool)) : Configuration :=
  { pc := 20,
    inputTape := { left := (cells.filterMap id).reverse.map some ++ beforeInput },
    outputTape := { left := (List.replicate (2 * cells.length) none ++
      some true :: some false :: beforeOutput) },
    halted := true }

def decodeRegionSteps : List (Option Bool) → Nat
  | [] => 2
  | cell :: rest => (if cell = none then 7 else 9) + decodeRegionSteps rest

private theorem decode_blank (beforeInput beforeOutput : List (Option Bool))
    (copied rest : List (Option Bool)) :
    RunsFor decodeRegion (decodingState beforeInput beforeOutput copied (none :: rest))
      (decodingState beforeInput beforeOutput (copied ++ [none]) rest) 7 := by
  let initial := decodingState beforeInput beforeOutput copied (none :: rest)
  let selected : Configuration := { initial with pc := 1 }
  let erased := (selected.updateTape .output (fun t => t.write none)).advance
  let atBit := (erased.updateTape .output Tape.moveRight).advance
  let ready : Configuration := { atBit with pc := 4 }
  let cleared := (ready.updateTape .output (fun t => t.write none)).advance
  let moved := (cleared.updateTape .output Tape.moveRight).advance
  have h0 : Step decodeRegion initial selected := by
    simp [Step, successors, next, decodeRegion, initial, selected, decodingState,
      decodingOutput, pairTape, code, Instruction.next, Configuration.tape]
  have h1 : Step decodeRegion selected erased := by
    simp [Step, successors, next, decodeRegion, initial, selected, erased, decodingState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step decodeRegion erased atBit := by
    simp [Step, successors, next, decodeRegion, initial, selected, erased, atBit,
      decodingState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step decodeRegion atBit ready := by
    simp [Step, successors, next, decodeRegion, initial, selected, erased, atBit, ready,
      decodingState, decodingOutput, pairTape, code, Instruction.next, Configuration.updateTape,
      Configuration.advance, Configuration.tape, Tape.moveRight, Tape.write]
  have h4 : Step decodeRegion ready cleared := by
    simp [Step, successors, next, decodeRegion, initial, selected, erased, atBit, ready, cleared,
      decodingState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h5 : Step decodeRegion cleared moved := by
    simp [Step, successors, next, decodeRegion, initial, selected, erased, atBit, ready, cleared,
      moved, decodingState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h6 : Step decodeRegion moved
      (decodingState beforeInput beforeOutput (copied ++ [none]) rest) := by
    cases rest <;> simp [Step, successors, next, decodeRegion, initial, selected, erased, atBit,
      ready, cleared, moved, decodingState, decodingOutput, pairTape, code, encodedCells,
      Instruction.next, Configuration.updateTape, Configuration.advance, Tape.moveRight,
      Tape.write, List.filterMap_append, Nat.mul_add, List.replicate_succ]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4) h5) h6

private theorem decode_bit (beforeInput beforeOutput : List (Option Bool))
    (copied rest : List (Option Bool)) (bit : Bool) :
    RunsFor decodeRegion (decodingState beforeInput beforeOutput copied (some bit :: rest))
      (decodingState beforeInput beforeOutput (copied ++ [some bit]) rest) 9 := by
  let initial := decodingState beforeInput beforeOutput copied (some bit :: rest)
  let selected : Configuration := { initial with pc := 7 }
  let erased := (selected.updateTape .output (fun t => t.write none)).advance
  let atBit := (erased.updateTape .output Tape.moveRight).advance
  let chosen : Configuration := { atBit with pc := if bit then 15 else 10 }
  let written := (chosen.updateTape .input (fun t => t.write (some bit))).advance
  let movedInput := (written.updateTape .input Tape.moveRight).advance
  let cleared := (movedInput.updateTape .output (fun t => t.write none)).advance
  let movedOutput := (cleared.updateTape .output Tape.moveRight).advance
  have h0 : Step decodeRegion initial selected := by
    simp [Step, successors, next, decodeRegion, initial, selected, decodingState,
      decodingOutput, pairTape, code, Instruction.next, Configuration.tape]
  have h1 : Step decodeRegion selected erased := by
    simp [Step, successors, next, decodeRegion, initial, selected, erased, decodingState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step decodeRegion erased atBit := by
    simp [Step, successors, next, decodeRegion, initial, selected, erased, atBit,
      decodingState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step decodeRegion atBit chosen := by
    cases bit <;> simp [Step, successors, next, decodeRegion, initial, selected, erased, atBit,
      chosen, decodingState, decodingOutput, pairTape, code, Instruction.next,
      Configuration.updateTape, Configuration.advance, Configuration.tape, Tape.moveRight, Tape.write]
  have h4 : Step decodeRegion chosen written := by
    cases bit <;> simp [Step, successors, next, decodeRegion, initial, selected, erased, atBit,
      chosen, written, decodingState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h5 : Step decodeRegion written movedInput := by
    cases bit <;> simp [Step, successors, next, decodeRegion, initial, selected, erased, atBit,
      chosen, written, movedInput, decodingState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h6 : Step decodeRegion movedInput cleared := by
    cases bit <;> simp [Step, successors, next, decodeRegion, initial, selected, erased, atBit,
      chosen, written, movedInput, cleared, decodingState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h7 : Step decodeRegion cleared movedOutput := by
    cases bit <;> simp [Step, successors, next, decodeRegion, initial, selected, erased, atBit,
      chosen, written, movedInput, cleared, movedOutput, decodingState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h8 : Step decodeRegion movedOutput
      (decodingState beforeInput beforeOutput (copied ++ [some bit]) rest) := by
    cases bit <;> cases rest <;>
      simp [Step, successors, next, decodeRegion, initial, selected, erased, atBit, chosen,
        written, movedInput, cleared, movedOutput, decodingState, decodingOutput, pairTape,
        code, encodedCells, Instruction.next, Configuration.updateTape, Configuration.advance,
        Tape.moveRight, Tape.write, List.filterMap_append, List.reverse_append, Nat.mul_add,
        List.replicate_succ]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1)
      h2) h3) h4) h5) h6) h7) h8

private theorem decode_loop (beforeInput beforeOutput : List (Option Bool))
    (copied remaining : List (Option Bool)) :
    RunsFor decodeRegion (decodingState beforeInput beforeOutput copied remaining)
      (decodeRegionFinish beforeInput beforeOutput (copied ++ remaining))
      (decodeRegionSteps remaining) := by
  induction remaining generalizing copied with
  | nil =>
      let initial := decodingState beforeInput beforeOutput copied []
      let selected : Configuration := { initial with pc := 20 }
      have h0 : Step decodeRegion initial selected := by
        simp [Step, successors, next, decodeRegion, initial, selected, decodingState,
          decodingOutput, Instruction.next, Configuration.tape]
      have h1 : Step decodeRegion selected (decodeRegionFinish beforeInput beforeOutput copied) := by
        simp [Step, successors, next, decodeRegion, initial, selected, decodingState,
          decodingOutput, decodeRegionFinish, Instruction.next]
      simpa [decodeRegionSteps] using RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1
  | cons cell rest ih =>
      cases cell with
      | none =>
          simpa [decodeRegionSteps, List.append_assoc] using
            (decode_blank beforeInput beforeOutput copied rest).trans (ih (copied ++ [none]))
      | some bit =>
          simpa [decodeRegionSteps, List.append_assoc] using
            (decode_bit beforeInput beforeOutput copied rest bit).trans (ih (copied ++ [some bit]))

/-- Each blank word costs seven transitions, each data word nine, and the
physical frontier branch plus explicit halt cost two. -/
theorem decodeRegion_runs (beforeInput beforeOutput : List (Option Bool))
    (cells : List (Option Bool)) :
    RunsFor decodeRegion (decodeRegionStart beforeInput beforeOutput cells)
      (decodeRegionFinish beforeInput beforeOutput cells) (decodeRegionSteps cells) := by
  simpa [decodeRegionStart] using decode_loop beforeInput beforeOutput [] cells

theorem decodeRegionSteps_le (cells : List (Option Bool)) :
    decodeRegionSteps cells ≤ 9 * cells.length + 2 := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      cases cell <;> simp only [decodeRegionSteps, List.length_cons, Option.some_ne_none,
        ↓reduceIte] <;> omega

theorem decodeRegion_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ decodeRegion := by simp [decodeRegion]

theorem decodeRegion_control_closed (c d : Configuration) (hPc : c.pc < decodeRegion.length)
    (step : Step decodeRegion c d) (_hRunning : d.halted = false) : d.pc < decodeRegion.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 21 at hPc
  change d.pc < 21
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, decodeRegion,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

theorem decodeRegion_eval (beforeInput beforeOutput : List (Option Bool))
    (cells : List (Option Bool)) :
    evalConfigWithin decodeRegion (decodeRegionStart beforeInput beforeOutput cells)
      (decodeRegionSteps cells) = PMF.pure (decodeRegionFinish beforeInput beforeOutput cells) :=
  (decodeRegion_runs beforeInput beforeOutput cells).evalConfigWithin_eq_pure_of_no_randomBit
    decodeRegion_no_randomBit

theorem decodeRegion_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (cells : List (Option Bool)) :
    evalConfigWithin (Program.withSubroutine pre decodeRegion suffix returnPc)
      ((decodeRegionStart beforeInput beforeOutput cells).rebasePc pre.length)
      (decodeRegionSteps cells) =
      PMF.pure ((decodeRegionFinish beforeInput beforeOutput cells).resumeAt returnPc) :=
  (decodeRegion_runs beforeInput beforeOutput cells).evalConfigWithin_withSubroutine_halted_of_closed
    pre decodeRegion suffix returnPc (by simp [decodeRegionStart, decodingState, decodeRegion])
    rfl rfl decodeRegion_control_closed decodeRegion_no_randomBit

/-- The mathematical decoding list agrees with the halted source tape's
existing observation. This is a postcondition of the charged decoding trace. -/
theorem decodeRegionStart_of_rewound (beforeInput beforeOutput : List (Option Bool)) (source : Tape) :
    (decodeRegionStart beforeInput beforeOutput
      (source.left.reverse ++ source.current :: source.right)).outputTape =
      encodeTape beforeOutput (rewoundTape source) := by
  cases hCells : source.left.reverse ++ source.current :: source.right with
  | nil =>
      have hLength := congrArg List.length hCells
      simp at hLength
  | cons cell rest =>
      simp [decodeRegionStart, decodingState, decodingOutput, rewoundTape, hCells,
        encodeTape, encodedLeftCells, pairTape]

theorem decodeRegionSteps_source_le (source : Tape) :
    decodeRegionSteps (source.left.reverse ++ source.current :: source.right) ≤
      9 * source.cells + 2 := by
  simpa [Tape.cells, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    decodeRegionSteps_le (source.left.reverse ++ source.current :: source.right)

/-- Both prefixes survive beyond the exact regions touched by decoding. -/
theorem decodeRegionFinish_preserves_prefixes (beforeInput beforeOutput : List (Option Bool))
    (cells : List (Option Bool)) :
    (decodeRegionFinish beforeInput beforeOutput cells).inputTape.left.drop
        (cells.filterMap id).length = beforeInput ∧
      (decodeRegionFinish beforeInput beforeOutput cells).outputTape.left.drop
        (2 * cells.length + 2) = beforeOutput := by
  constructor
  · simp [decodeRegionFinish]
  · simp [decodeRegionFinish, List.drop_append, List.drop_replicate]

/-- Remove the reserved output guard after all its words have been erased.
The scan crosses the erased cells, erases the guard's `1` and `0` separately,
and halts at the old left guard cell. It never reads or changes the caller
prefix beyond the guard. -/
def clearOutputGuard : Program :=
  [.moveLeft .output, .branch .output 0 6 2, .erase .output,
   .moveLeft .output, .erase .output, .halt, .halt]

private def guardClearState (before : List (Option Bool)) (count : Nat)
    (after : List (Option Bool)) (input : Tape) : Configuration :=
  { inputTape := input,
    outputTape := {
      left := List.replicate count none ++ some true :: some false :: before
      right := after } }

private def guardClearFinish (before : List (Option Bool)) (count : Nat)
    (after : List (Option Bool)) (input : Tape) : Configuration :=
  { pc := 5, inputTape := input,
    outputTape := { left := before, right := List.replicate (count + 2) none ++ after },
    halted := true }

private theorem guard_clear_loop (before : List (Option Bool)) (count : Nat)
    (after : List (Option Bool)) (input : Tape) :
    RunsFor clearOutputGuard (guardClearState before count after input)
      (guardClearFinish before count after input) (2 * count + 6) := by
  induction count generalizing after with
  | zero =>
      let initial := guardClearState before 0 after input
      let moved := (initial.updateTape .output Tape.moveLeft).advance
      let selected : Configuration := { moved with pc := 2 }
      let erased := (selected.updateTape .output (fun t => t.write none)).advance
      let atZero := (erased.updateTape .output Tape.moveLeft).advance
      let cleared := (atZero.updateTape .output (fun t => t.write none)).advance
      have h0 : Step clearOutputGuard initial moved := by
        simp [Step, successors, next, clearOutputGuard, initial, moved, guardClearState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h1 : Step clearOutputGuard moved selected := by
        simp [Step, successors, next, clearOutputGuard, initial, moved, selected, guardClearState,
          Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape,
          Tape.moveLeft]
      have h2 : Step clearOutputGuard selected erased := by
        simp [Step, successors, next, clearOutputGuard, initial, moved, selected, erased,
          guardClearState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h3 : Step clearOutputGuard erased atZero := by
        simp [Step, successors, next, clearOutputGuard, initial, moved, selected, erased, atZero,
          guardClearState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h4 : Step clearOutputGuard atZero cleared := by
        simp [Step, successors, next, clearOutputGuard, initial, moved, selected, erased, atZero,
          cleared, guardClearState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h5 : Step clearOutputGuard cleared (guardClearFinish before 0 after input) := by
        simp [Step, successors, next, clearOutputGuard, initial, moved, selected, erased, atZero,
          cleared, guardClearState, guardClearFinish, Instruction.next, Configuration.updateTape,
          Configuration.advance, Tape.moveLeft, Tape.write, List.replicate_succ]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4) h5
  | succ count ih =>
      let initial := guardClearState before (count + 1) after input
      let moved := (initial.updateTape .output Tape.moveLeft).advance
      have h0 : Step clearOutputGuard initial moved := by
        simp [Step, successors, next, clearOutputGuard, initial, moved, guardClearState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h1 : Step clearOutputGuard moved (guardClearState before count (none :: after) input) := by
        simp [Step, successors, next, clearOutputGuard, initial, moved, guardClearState,
          Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape,
          Tape.moveLeft, List.replicate_succ]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1).trans (ih (none :: after))
      have hFinish : guardClearFinish before count (none :: after) input =
          guardClearFinish before (count + 1) after input := by
        have hList : List.replicate (count + 2) none ++ none :: after =
            List.replicate (count + 1 + 2) none ++ after := by
          rw [show count + 1 + 2 = (count + 2) + 1 by omega]
          conv_rhs => rw [List.replicate_succ']
          simp only [List.append_assoc, List.singleton_append]
        simp only [guardClearFinish, hList]
      rw [hFinish] at run
      convert run using 1; omega

def clearOutputGuardStart (before : List (Option Bool)) (erasedCells : Nat) (input : Tape) : Configuration :=
  guardClearState before erasedCells [] input

def clearOutputGuardFinish (before : List (Option Bool)) (erasedCells : Nat) (input : Tape) : Configuration :=
  guardClearFinish before erasedCells [] input

theorem clearOutputGuard_runs (before : List (Option Bool)) (erasedCells : Nat) (input : Tape) :
    RunsFor clearOutputGuard (clearOutputGuardStart before erasedCells input)
      (clearOutputGuardFinish before erasedCells input) (2 * erasedCells + 6) :=
  guard_clear_loop before erasedCells [] input

theorem clearOutputGuard_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ clearOutputGuard := by simp [clearOutputGuard]

theorem clearOutputGuard_control_closed (c d : Configuration) (hPc : c.pc < clearOutputGuard.length)
    (step : Step clearOutputGuard c d) (_hRunning : d.halted = false) : d.pc < clearOutputGuard.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 7 at hPc
  change d.pc < 7
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, clearOutputGuard,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

theorem clearOutputGuard_eval (before : List (Option Bool)) (erasedCells : Nat) (input : Tape) :
    evalConfigWithin clearOutputGuard (clearOutputGuardStart before erasedCells input)
      (2 * erasedCells + 6) = PMF.pure (clearOutputGuardFinish before erasedCells input) :=
  (clearOutputGuard_runs before erasedCells input).evalConfigWithin_eq_pure_of_no_randomBit
    clearOutputGuard_no_randomBit

/-- Actual composition: decode into scratch input, clear the old output
guard, and halt with the decoded input scratch and now-blank output region.
Rewinding scratch input and copying to final output are still required. -/
def decodeAndClear : Program :=
  decodeRegion.asSubroutine 0 22 ++ clearOutputGuard.asSubroutine 22 30 ++ [.halt]

def decodeAndClearFinish (beforeInput beforeOutput : List (Option Bool))
    (cells : List (Option Bool)) : Configuration :=
  { pc := 30,
    inputTape := { left := (cells.filterMap id).reverse.map some ++ beforeInput },
    outputTape := { left := beforeOutput, right := List.replicate (2 * cells.length + 2) none },
    halted := true }

theorem decodeAndClear_runs (beforeInput beforeOutput : List (Option Bool)) (cells : List (Option Bool)) :
    RunsFor decodeAndClear (decodeRegionStart beforeInput beforeOutput cells)
      (decodeAndClearFinish beforeInput beforeOutput cells) (decodeRegionSteps cells + 4 * cells.length + 7) := by
  have hDecode := (decodeRegion_runs beforeInput beforeOutput cells).withSubroutine_halted_of_closed
    [] decodeRegion (clearOutputGuard.asSubroutine 22 30 ++ [.halt]) 22
    (by simp [decodeRegionStart, decodingState, decodeRegion]) rfl rfl decodeRegion_control_closed
  change RunsFor decodeAndClear (decodeRegionStart beforeInput beforeOutput cells)
    ((decodeRegionFinish beforeInput beforeOutput cells).resumeAt 22) (decodeRegionSteps cells) at hDecode
  have hClear := (clearOutputGuard_runs beforeOutput (2 * cells.length)
      { left := (cells.filterMap id).reverse.map some ++ beforeInput }).withSubroutine_halted_of_closed
    (decodeRegion.asSubroutine 0 22) clearOutputGuard [.halt] 30
    (by simp [clearOutputGuardStart, guardClearState, clearOutputGuard]) rfl rfl clearOutputGuard_control_closed
  change RunsFor decodeAndClear ((decodeRegionFinish beforeInput beforeOutput cells).resumeAt 22)
    ((clearOutputGuardFinish beforeOutput (2 * cells.length)
      { left := (cells.filterMap id).reverse.map some ++ beforeInput }).resumeAt 30)
    (2 * (2 * cells.length) + 6) at hClear
  have hFinish : (clearOutputGuardFinish beforeOutput (2 * cells.length)
      { left := (cells.filterMap id).reverse.map some ++ beforeInput }).resumeAt 30 =
      (decodeAndClearFinish beforeInput beforeOutput cells).resumeAt 30 := by
    simp [clearOutputGuardFinish, guardClearFinish, decodeAndClearFinish, Configuration.resumeAt]
  rw [hFinish] at hClear
  have hHalt : Step decodeAndClear ((decodeAndClearFinish beforeInput beforeOutput cells).resumeAt 30)
      (decodeAndClearFinish beforeInput beforeOutput cells) := by
    simp [Step, successors, next, decodeAndClear, decodeRegion, clearOutputGuard,
      Program.asSubroutine, Instruction.asSubroutine, decodeAndClearFinish,
      Configuration.resumeAt, Instruction.next]
  convert RunsFor.succ (hDecode.trans hClear) hHalt using 1; omega

theorem decodeAndClear_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ decodeAndClear := by
  simp [decodeAndClear, decodeRegion, clearOutputGuard, Program.asSubroutine, Instruction.asSubroutine]

theorem decodeAndClear_eval (beforeInput beforeOutput : List (Option Bool)) (cells : List (Option Bool)) :
    evalConfigWithin decodeAndClear (decodeRegionStart beforeInput beforeOutput cells)
      (decodeRegionSteps cells + 4 * cells.length + 7) =
      PMF.pure (decodeAndClearFinish beforeInput beforeOutput cells) :=
  (decodeAndClear_runs beforeInput beforeOutput cells).evalConfigWithin_eq_pure_of_no_randomBit
    decodeAndClear_no_randomBit

theorem decodeAndClear_steps_le (cells : List (Option Bool)) :
    decodeRegionSteps cells + 4 * cells.length + 7 ≤ 13 * cells.length + 9 := by
  have h := decodeRegionSteps_le cells
  omega

/-- With no caller output prefix, clearing leaves a genuinely blank
output tape, possibly with stored outer blank cells. This proof relation
does not normalize or reset the machine tape. -/
theorem decodeAndClearFinish_output_equivalent_blank (beforeInput : List (Option Bool))
    (cells : List (Option Bool)) :
    (decodeAndClearFinish beforeInput [] cells).outputTape.Equivalent ({} : Tape) := by
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro i
  simp only [decodeAndClearFinish, List.getD, List.getElem?_replicate]
  split <;> rfl

/-- Seek the unwritten right frontier of a contiguous physical bit region,
then move once further to leave an actual blank separator before the new
scratch space. The output tape and all traversed input bits are unchanged. -/
def seekScratchInput : Program :=
  [.branch .input 3 1 1, .moveRight .input, .jump 0, .moveRight .input, .halt]

private def scratchSeekState (before : List (Option Bool)) (copied remaining : List Bool)
    (output : Tape) : Configuration :=
  { inputTape := { Tape.ofBits remaining with left := copied.reverse.map some ++ before },
    outputTape := output }

def seekScratchInputStart (before : List (Option Bool)) (bits : List Bool) (output : Tape) : Configuration :=
  scratchSeekState before [] bits output

def seekScratchInputFinish (before : List (Option Bool)) (bits : List Bool) (output : Tape) : Configuration :=
  { pc := 4,
    inputTape := { left := none :: bits.reverse.map some ++ before },
    outputTape := output,
    halted := true }

private theorem scratch_seek_loop (before : List (Option Bool))
    (copied remaining : List Bool) (output : Tape) :
    RunsFor seekScratchInput (scratchSeekState before copied remaining output)
      (seekScratchInputFinish before (copied ++ remaining) output) (3 * remaining.length + 3) := by
  induction remaining generalizing copied with
  | nil =>
      let initial := scratchSeekState before copied [] output
      let selected : Configuration := { initial with pc := 3 }
      let moved := (selected.updateTape .input Tape.moveRight).advance
      have h0 : Step seekScratchInput initial selected := by
        simp [Step, successors, next, seekScratchInput, initial, selected,
          scratchSeekState, Tape.ofBits, Instruction.next, Configuration.tape]
      have h1 : Step seekScratchInput selected moved := by
        simp [Step, successors, next, seekScratchInput, initial, selected, moved,
          scratchSeekState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step seekScratchInput moved (seekScratchInputFinish before copied output) := by
        simp [Step, successors, next, seekScratchInput, initial, selected, moved,
          scratchSeekState, seekScratchInputFinish, Tape.ofBits, Tape.moveRight,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      simpa using RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2
  | cons bit rest ih =>
      let initial := scratchSeekState before copied (bit :: rest) output
      let selected : Configuration := { initial with pc := 1 }
      let moved := (selected.updateTape .input Tape.moveRight).advance
      have h0 : Step seekScratchInput initial selected := by
        cases bit <;> simp [Step, successors, next, seekScratchInput, initial, selected,
          scratchSeekState, Tape.ofBits, Instruction.next, Configuration.tape]
      have h1 : Step seekScratchInput selected moved := by
        simp [Step, successors, next, seekScratchInput, initial, selected, moved,
          scratchSeekState, Instruction.next, Configuration.updateTape, Configuration.advance]
      have h2 : Step seekScratchInput moved (scratchSeekState before (copied ++ [bit]) rest output) := by
        cases rest <;> simp [Step, successors, next, seekScratchInput, initial, selected, moved,
          scratchSeekState, Tape.ofBits, Tape.moveRight, List.reverse_append,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2).trans
        (ih (copied ++ [bit]))
      simpa [List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using run

theorem seekScratchInput_runs (before : List (Option Bool)) (bits : List Bool) (output : Tape) :
    RunsFor seekScratchInput (seekScratchInputStart before bits output)
      (seekScratchInputFinish before bits output) (3 * bits.length + 3) := by
  simpa [seekScratchInputStart] using scratch_seek_loop before [] bits output

theorem seekScratchInput_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ seekScratchInput := by simp [seekScratchInput]

theorem seekScratchInput_control_closed (c d : Configuration) (hPc : c.pc < seekScratchInput.length)
    (step : Step seekScratchInput c d) (_hRunning : d.halted = false) : d.pc < seekScratchInput.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 5 at hPc
  change d.pc < 5
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, seekScratchInput,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

theorem seekScratchInput_eval (before : List (Option Bool)) (bits : List Bool) (output : Tape) :
    evalConfigWithin seekScratchInput (seekScratchInputStart before bits output)
      (3 * bits.length + 3) = PMF.pure (seekScratchInputFinish before bits output) :=
  (seekScratchInput_runs before bits output).evalConfigWithin_eq_pure_of_no_randomBit
    seekScratchInput_no_randomBit

private theorem encodedCells_filterMap_map (cells : List (Option Bool)) :
    ((encodedCells cells).filterMap (fun cell => cell)).map some = encodedCells cells := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp only [encodedCells, List.filterMap_cons, List.map_cons, ih]

private theorem encodedCells_filterMap_length (cells : List (Option Bool)) :
    ((encodedCells cells).filterMap (fun cell => cell)).length = 2 * cells.length := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp only [encodedCells, List.filterMap_cons, List.length_cons, ih]
      omega

/-- Physical bits from the current logical pair to the right frontier.
This list is used only to state entry layouts and transition counts; it is
not a machine instruction or a free tape conversion. -/
def encodedRightBits (source : Tape) : List Bool :=
  (code source.current).1 :: (code source.current).2 ::
    (encodedCells source.right).filterMap (fun cell => cell)

theorem encodedRightBits_length (source : Tape) :
    (encodedRightBits source).length = 2 * source.right.length + 2 := by
  simp only [encodedRightBits, List.length_cons, encodedCells_filterMap_length]

theorem seekScratchInputStart_encoded (before : List (Option Bool)) (source output : Tape) :
    seekScratchInputStart (encodeTape before source).left (encodedRightBits source) output =
      start (encodeTape before source) output := by
  simp only [seekScratchInputStart, scratchSeekState, encodedRightBits, Tape.ofBits,
    encodedCells_filterMap_map, start, encodeTape, pairTape, List.map_cons,
    List.reverse_nil, List.map_nil, List.nil_append]

theorem seekScratchInput_encoded_steps_le (source : Tape) :
    3 * (encodedRightBits source).length + 3 ≤ 6 * source.cells + 3 := by
  rw [encodedRightBits_length]
  simp only [Tape.cells]
  omega

/-- Reserve scratch space beyond the encoded input, rewind the encoded
output, decode it into that scratch space, and erase the old output guard.
Each operation and each subroutine return is ordinary finite machine code.
The decoded string is still on the input tape; final copying is separate. -/
def extractToScratch : Program :=
  seekScratchInput.asSubroutine 0 6 ++
    (rewindRegion .output).asSubroutine 6 17 ++
    decodeRegion.asSubroutine 17 39 ++
    clearOutputGuard.asSubroutine 39 47 ++ [.halt]

/-- Saved physical input before the fresh scratch string. The first blank
is the separator installed by `seekScratchInput`, not a free tape reset. -/
def scratchPrefix (before : List (Option Bool)) (input : Tape) : List (Option Bool) :=
  none :: (encodedRightBits input).reverse.map some ++ (encodeTape before input).left

def extractToScratchStart (beforeInput beforeOutput : List (Option Bool))
    (input output : Tape) : Configuration :=
  start (encodeTape beforeInput input) (encodeTape beforeOutput output)

def extractToScratchFinish (beforeInput beforeOutput : List (Option Bool))
    (input output : Tape) : Configuration :=
  { pc := 47,
    inputTape := { left := output.bits.reverse.map some ++ scratchPrefix beforeInput input },
    outputTape := { left := beforeOutput, right := List.replicate (2 * output.cells + 2) none },
    halted := true }

def extractToScratchSteps (input output : Tape) : Nat :=
  3 * (encodedRightBits input).length + 3 + rewindRegionSteps output.left +
    decodeRegionSteps (output.left.reverse ++ output.current :: output.right) +
    4 * output.cells + 7

theorem extractToScratch_runs (beforeInput beforeOutput : List (Option Bool))
    (input output : Tape) :
    RunsFor extractToScratch (extractToScratchStart beforeInput beforeOutput input output)
      (extractToScratchFinish beforeInput beforeOutput input output)
      (extractToScratchSteps input output) := by
  let a := seekScratchInput.asSubroutine 0 6
  let b := (rewindRegion .output).asSubroutine 6 17
  let c := decodeRegion.asSubroutine 17 39
  let d := clearOutputGuard.asSubroutine 39 47
  let saved := scratchPrefix beforeInput input
  let cells := output.left.reverse ++ output.current :: output.right
  have hCells : cells.length = output.cells := by
    simp [cells, Tape.cells, Nat.add_comm, Nat.add_left_comm]
  have hBits : cells.filterMap id = output.bits := rfl
  have hSeek := (seekScratchInput_runs (encodeTape beforeInput input).left
      (encodedRightBits input) (encodeTape beforeOutput output)).withSubroutine_halted_of_closed
    [] seekScratchInput (b ++ c ++ d ++ [.halt]) 6
    (by simp [seekScratchInputStart, scratchSeekState, seekScratchInput]) rfl rfl
    seekScratchInput_control_closed
  rw [seekScratchInputStart_encoded] at hSeek
  change RunsFor extractToScratch (extractToScratchStart beforeInput beforeOutput input output)
    ((rewindRegionStart .output beforeOutput output { left := saved }).rebasePc 6)
    (3 * (encodedRightBits input).length + 3) at hSeek
  have hRewind := (rewindRegion_runs .output beforeOutput output
      { left := saved }).withSubroutine_halted_of_closed
    a (rewindRegion .output) (c ++ d ++ [.halt]) 17
    (by simp [rewindRegionStart, start, rewindRegion]) rfl rfl (rewindRegion_control_closed .output)
  change RunsFor extractToScratch
    ((rewindRegionStart .output beforeOutput output { left := saved }).rebasePc 6)
    ((rewindRegionFinish .output beforeOutput output { left := saved }).resumeAt 17)
    (rewindRegionSteps output.left) at hRewind
  have hDecodeStart : (rewindRegionFinish .output beforeOutput output { left := saved }).resumeAt 17 =
      (decodeRegionStart saved beforeOutput cells).rebasePc 17 := by
    have hTape := decodeRegionStart_of_rewound saved beforeOutput output
    change (decodeRegionStart saved beforeOutput cells).outputTape =
      encodeTape beforeOutput (rewoundTape output) at hTape
    simp only [rewindRegionFinish, rewindRegionStart, start, Configuration.resumeAt,
      Configuration.rebasePc, decodeRegionStart, decodingState, List.filterMap_nil,
      List.reverse_nil, List.map_nil, List.nil_append] at hTape ⊢
    rw [hTape]
  rw [hDecodeStart] at hRewind
  have hDecode := (decodeRegion_runs saved beforeOutput cells).withSubroutine_halted_of_closed
    (a ++ b) decodeRegion (d ++ [.halt]) 39
    (by simp [decodeRegionStart, decodingState, decodeRegion]) rfl rfl decodeRegion_control_closed
  change RunsFor extractToScratch ((decodeRegionStart saved beforeOutput cells).rebasePc 17)
    ((decodeRegionFinish saved beforeOutput cells).resumeAt 39) (decodeRegionSteps cells) at hDecode
  have hClear := (clearOutputGuard_runs beforeOutput (2 * cells.length)
      { left := (cells.filterMap id).reverse.map some ++ saved }).withSubroutine_halted_of_closed
    (a ++ b ++ c) clearOutputGuard [.halt] 47
    (by simp [clearOutputGuardStart, guardClearState, clearOutputGuard]) rfl rfl
    clearOutputGuard_control_closed
  change RunsFor extractToScratch ((decodeRegionFinish saved beforeOutput cells).resumeAt 39)
    ((clearOutputGuardFinish beforeOutput (2 * cells.length)
      { left := (cells.filterMap id).reverse.map some ++ saved }).resumeAt 47)
    (2 * (2 * cells.length) + 6) at hClear
  have hFinish : (clearOutputGuardFinish beforeOutput (2 * cells.length)
      { left := (cells.filterMap id).reverse.map some ++ saved }).resumeAt 47 =
      (extractToScratchFinish beforeInput beforeOutput input output).resumeAt 47 := by
    simp only [clearOutputGuardFinish, guardClearFinish, extractToScratchFinish,
      Configuration.resumeAt, hCells, hBits, saved, List.append_nil]
  rw [hFinish] at hClear
  have hHalt : Step extractToScratch
      ((extractToScratchFinish beforeInput beforeOutput input output).resumeAt 47)
      (extractToScratchFinish beforeInput beforeOutput input output) := by
    simp [Step, successors, next, extractToScratch, seekScratchInput, rewindRegion,
      decodeRegion, clearOutputGuard, Program.asSubroutine, Instruction.asSubroutine,
      extractToScratchFinish, Configuration.resumeAt, Instruction.next]
  convert RunsFor.succ (((hSeek.trans hRewind).trans hDecode).trans hClear) hHalt using 1
  simp only [extractToScratchSteps, hCells, cells] at *
  omega

theorem extractToScratch_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ extractToScratch := by
  simp [extractToScratch, seekScratchInput, rewindRegion, decodeRegion, clearOutputGuard,
    Program.asSubroutine, Instruction.asSubroutine]

theorem extractToScratch_eval (beforeInput beforeOutput : List (Option Bool))
    (input output : Tape) :
    evalConfigWithin extractToScratch (extractToScratchStart beforeInput beforeOutput input output)
      (extractToScratchSteps input output) =
      PMF.pure (extractToScratchFinish beforeInput beforeOutput input output) :=
  (extractToScratch_runs beforeInput beforeOutput input output).evalConfigWithin_eq_pure_of_no_randomBit
    extractToScratch_no_randomBit

theorem extractToScratchSteps_le (input output : Tape) :
    extractToScratchSteps input output ≤ 20 * (input.cells + output.cells) + 19 := by
  have hSeek := seekScratchInput_encoded_steps_le input
  have hRewind := rewindRegionSteps_le output.left
  have hDecode := decodeRegionSteps_source_le output
  simp only [extractToScratchSteps, Tape.cells] at *
  omega

private def scratchCopyState (beforeInput beforeOutput : List (Option Bool))
    (copied remaining : List Bool) (blanks : Nat) : Configuration :=
  { inputTape := { packedLogicalInput remaining with
      left := copied.reverse.map some ++ beforeInput },
    outputTape := {
      left := copied.reverse.map some ++ beforeOutput
      right := List.replicate blanks none } }

def copyScratchStart (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  scratchCopyState beforeInput beforeOutput [] bits blanks

def copyScratchFinish (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  { pc := 7,
    inputTape := { left := bits.reverse.map some ++ beforeInput },
    outputTape := {
      left := bits.reverse.map some ++ beforeOutput
      right := List.replicate (blanks - bits.length) none },
    halted := true }

private theorem copy_scratch_bit (beforeInput beforeOutput : List (Option Bool))
    (copied rest : List Bool) (bit : Bool) (blanks : Nat) :
    RunsFor copyBitstring (scratchCopyState beforeInput beforeOutput copied (bit :: rest) blanks)
      (scratchCopyState beforeInput beforeOutput (copied ++ [bit]) rest (blanks - 1))
      (if bit then 5 else 6) := by
  let initial := scratchCopyState beforeInput beforeOutput copied (bit :: rest) blanks
  let selected : Configuration := { initial with pc := if bit then 3 else 1 }
  let written : Configuration := { initial with
    pc := if bit then 4 else 2
    outputTape := initial.outputTape.write (some bit) }
  let ready : Configuration := { written with pc := 4 }
  let movedInput : Configuration := { ready with pc := 5, inputTape := ready.inputTape.moveRight }
  let movedOutput : Configuration := { movedInput with pc := 6, outputTape := movedInput.outputTape.moveRight }
  have h0 : Step copyBitstring initial selected := by
    cases bit <;> simp [Step, successors, next, copyBitstring, initial, selected,
      scratchCopyState, packedLogicalInput_cons, Instruction.next, Configuration.tape]
  have h1 : Step copyBitstring selected written := by
    cases bit <;> simp [Step, successors, next, copyBitstring, initial, selected, written,
      scratchCopyState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step copyBitstring ready movedInput := by
    simp [Step, successors, next, copyBitstring, initial, written, ready, movedInput,
      scratchCopyState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step copyBitstring movedInput movedOutput := by
    simp [Step, successors, next, copyBitstring, initial, written, ready, movedInput, movedOutput,
      scratchCopyState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step copyBitstring movedOutput
      (scratchCopyState beforeInput beforeOutput (copied ++ [bit]) rest (blanks - 1)) := by
    cases blanks <;> cases rest <;>
      simp [Step, successors, next, copyBitstring, initial, written, ready, movedInput,
        movedOutput, scratchCopyState, packedLogicalInput, rewoundTape, Instruction.next,
        Tape.moveRight, Tape.write, List.reverse_append, List.replicate_succ]
  cases bit with
  | false =>
      have hJump : Step copyBitstring written ready := by
        simp [Step, successors, next, copyBitstring, initial, written, ready,
          scratchCopyState, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) hJump) h2) h3) h4
  | true =>
      have hReady : ready = written := by simp [ready, written]
      rw [hReady] at h2
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4

private theorem copy_scratch_loop (beforeInput beforeOutput : List (Option Bool))
    (copied remaining : List Bool) (blanks : Nat) :
    RunsFor copyBitstring (scratchCopyState beforeInput beforeOutput copied remaining blanks)
      (copyScratchFinish beforeInput beforeOutput (copied ++ remaining) (blanks + copied.length))
      (copyBitstringSteps remaining) := by
  induction remaining generalizing copied blanks with
  | nil =>
      let initial := scratchCopyState beforeInput beforeOutput copied [] blanks
      let selected : Configuration := { initial with pc := 7 }
      have h0 : Step copyBitstring initial selected := by
        simp [Step, successors, next, copyBitstring, initial, selected, scratchCopyState,
          packedLogicalInput, rewoundTape, Instruction.next, Configuration.tape]
      have h1 : Step copyBitstring selected
          (copyScratchFinish beforeInput beforeOutput copied (blanks + copied.length)) := by
        simp [Step, successors, next, copyBitstring, initial, selected, scratchCopyState,
          packedLogicalInput, rewoundTape, copyScratchFinish, Instruction.next]
      simpa [copyBitstringSteps] using RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1
  | cons bit rest ih =>
      have run := (copy_scratch_bit beforeInput beforeOutput copied rest bit blanks).trans
        (ih (copied ++ [bit]) (blanks - 1))
      have hFinish : copyScratchFinish beforeInput beforeOutput ((copied ++ [bit]) ++ rest)
          (blanks - 1 + (copied ++ [bit]).length) =
          copyScratchFinish beforeInput beforeOutput (copied ++ bit :: rest) (blanks + copied.length) := by
        have hSubtract : blanks - 1 + (copied ++ [bit]).length - (copied ++ bit :: rest).length =
            blanks + copied.length - (copied ++ bit :: rest).length := by simp; omega
        simp only [copyScratchFinish, List.append_assoc, List.singleton_append]
        rw [hSubtract]
      rw [hFinish] at run
      exact run

/-- Copy the contiguous decoded scratch string into the erased output
region using the existing one-bit copying code. Arbitrary saved prefixes and
the stored blank suffix survive; no tape is silently normalized. -/
theorem copyScratch_runs (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    RunsFor copyBitstring (copyScratchStart beforeInput beforeOutput bits blanks)
      (copyScratchFinish beforeInput beforeOutput bits blanks) (copyBitstringSteps bits) := by
  simpa [copyScratchStart] using copy_scratch_loop beforeInput beforeOutput [] bits blanks

theorem copyBitstring_control_closed (c d : Configuration)
    (hPc : c.pc < copyBitstring.length) (step : Step copyBitstring c d)
    (_hRunning : d.halted = false) : d.pc < copyBitstring.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 8 at hPc
  change d.pc < 8
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, copyBitstring,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

theorem copyScratch_eval (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    evalConfigWithin copyBitstring (copyScratchStart beforeInput beforeOutput bits blanks)
      (copyBitstringSteps bits) = PMF.pure (copyScratchFinish beforeInput beforeOutput bits blanks) :=
  (copyScratch_runs beforeInput beforeOutput bits blanks).evalConfigWithin_eq_pure_of_no_randomBit
    (by intro tape; simp [copyBitstring])

set_option maxHeartbeats 800000 in
theorem extractToScratch_control_closed (c d : Configuration)
    (hPc : c.pc < extractToScratch.length) (step : Step extractToScratch c d)
    (_hRunning : d.halted = false) : d.pc < extractToScratch.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 48 at hPc
  change d.pc < 48
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, extractToScratch, seekScratchInput,
    rewindRegion, decodeRegion, clearOutputGuard, Program.asSubroutine, Instruction.asSubroutine,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- Complete output extraction: reserve input scratch space, decode and
erase the guarded output, rewind the scratch string, then copy its raw bits
back to output. All scans, erasures, copying, returns and the final halt are
actual transitions in this fixed 64-instruction program. -/
def extractOutput : Program :=
  extractToScratch.asSubroutine 0 49 ++
    rewindBitstring.asSubroutine 49 54 ++ copyBitstring.asSubroutine 54 63 ++ [.halt]

def extractOutputFinish (beforeInput beforeOutput : List (Option Bool))
    (input output : Tape) : Configuration :=
  { copyScratchFinish (scratchPrefix beforeInput input) beforeOutput output.bits
      (2 * output.cells + 2) with pc := 63 }

def extractOutputSteps (input output : Tape) : Nat :=
  extractToScratchSteps input output + 2 * output.bits.length + 4 +
    copyBitstringSteps output.bits + 1

theorem extractOutput_runs (beforeInput beforeOutput : List (Option Bool))
    (input output : Tape) :
    RunsFor extractOutput (extractToScratchStart beforeInput beforeOutput input output)
      (extractOutputFinish beforeInput beforeOutput input output) (extractOutputSteps input output) := by
  let a := extractToScratch.asSubroutine 0 49
  let b := rewindBitstring.asSubroutine 49 54
  let c := copyBitstring.asSubroutine 54 63
  let saved := (encodedRightBits input).reverse.map some ++ (encodeTape beforeInput input).left
  let blankOutput : Tape := { left := beforeOutput, right := List.replicate (2 * output.cells + 2) none }
  have hExtract := (extractToScratch_runs beforeInput beforeOutput input output).withSubroutine_halted_of_closed
    [] extractToScratch (b ++ c ++ [.halt]) 49
    (by simp [extractToScratchStart, start, extractToScratch]) rfl rfl extractToScratch_control_closed
  change RunsFor extractOutput (extractToScratchStart beforeInput beforeOutput input output)
    ((rewindScratchStart saved output.bits blankOutput).rebasePc 49)
    (extractToScratchSteps input output) at hExtract
  have hRewind := (rewindScratch_runs saved output.bits blankOutput).withSubroutine_halted_of_closed
    a rewindBitstring (c ++ [.halt]) 54
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  change RunsFor extractOutput ((rewindScratchStart saved output.bits blankOutput).rebasePc 49)
    ((rewindScratchFinish saved output.bits blankOutput).resumeAt 54)
    (2 * output.bits.length + 4) at hRewind
  have hCopyStart : (rewindScratchFinish saved output.bits blankOutput).resumeAt 54 =
      (copyScratchStart (scratchPrefix beforeInput input) beforeOutput output.bits
        (2 * output.cells + 2)).rebasePc 54 := by
    cases hBits : output.bits <;>
      simp [rewindScratchFinish, copyScratchStart, scratchCopyState, packedLogicalInput,
        rewoundTape, scratchPrefix, saved, blankOutput, Configuration.resumeAt,
        Configuration.rebasePc, Tape.moveRight]
  rw [hCopyStart] at hRewind
  have hCopy := (copyScratch_runs (scratchPrefix beforeInput input) beforeOutput output.bits
      (2 * output.cells + 2)).withSubroutine_halted_of_closed
    (a ++ b) copyBitstring [.halt] 63
    (by simp [copyScratchStart, scratchCopyState, copyBitstring]) rfl rfl copyBitstring_control_closed
  change RunsFor extractOutput
    ((copyScratchStart (scratchPrefix beforeInput input) beforeOutput output.bits
      (2 * output.cells + 2)).rebasePc 54)
    ((extractOutputFinish beforeInput beforeOutput input output).resumeAt 63)
    (copyBitstringSteps output.bits) at hCopy
  have hHalt : Step extractOutput ((extractOutputFinish beforeInput beforeOutput input output).resumeAt 63)
      (extractOutputFinish beforeInput beforeOutput input output) := by
    simp [Step, successors, next, extractOutput, extractToScratch, seekScratchInput, rewindRegion,
      decodeRegion, clearOutputGuard, rewindBitstring, copyBitstring, Program.asSubroutine,
      Instruction.asSubroutine, extractOutputFinish, copyScratchFinish,
      Configuration.resumeAt, Instruction.next]
  simpa only [extractOutputSteps, Nat.add_assoc] using
    RunsFor.succ ((hExtract.trans hRewind).trans hCopy) hHalt

theorem extractOutput_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ extractOutput := by
  simp [extractOutput, extractToScratch, seekScratchInput, rewindRegion, decodeRegion,
    clearOutputGuard, rewindBitstring, copyBitstring, Program.asSubroutine, Instruction.asSubroutine]

theorem extractOutput_eval (beforeInput beforeOutput : List (Option Bool))
    (input output : Tape) :
    evalConfigWithin extractOutput (extractToScratchStart beforeInput beforeOutput input output)
      (extractOutputSteps input output) = PMF.pure (extractOutputFinish beforeInput beforeOutput input output) :=
  (extractOutput_runs beforeInput beforeOutput input output).evalConfigWithin_eq_pure_of_no_randomBit
    extractOutput_no_randomBit

/-- Extraction costs at most a linear function of the represented logical
tape cells. These cells include blanks, so holes in output are not free. -/
theorem extractOutputSteps_le (input output : Tape) :
    extractOutputSteps input output ≤ 28 * (input.cells + output.cells) + 26 := by
  have hExtract := extractToScratchSteps_le input output
  have hCopy := copyBitstringSteps_le output.bits
  have hBits := output.bits_length_le_cells
  simp only [extractOutputSteps] at *
  omega

/-- The complete physical output contains precisely the source's observed
raw bits when there was no saved output prefix. Blank cells stay stored and
are omitted by the existing halted-tape observation only. -/
theorem extractOutputFinish_outputBits (beforeInput : List (Option Bool)) (input output : Tape) :
    (extractOutputFinish beforeInput [] input output).outputBits = output.bits := by
  simp [extractOutputFinish, copyScratchFinish, Configuration.outputBits, Tape.bits,
    List.filterMap_append]

set_option maxHeartbeats 1200000 in
theorem extractOutput_control_closed (c d : Configuration)
    (hPc : c.pc < extractOutput.length) (step : Step extractOutput c d)
    (_hRunning : d.halted = false) : d.pc < extractOutput.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 64 at hPc
  change d.pc < 64
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, extractOutput, extractToScratch,
    seekScratchInput, rewindRegion, decodeRegion, clearOutputGuard, rewindBitstring, copyBitstring,
    Program.asSubroutine, Instruction.asSubroutine, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- Exact full-configuration law for a caller, even when its surrounding
code uses random instructions. The extraction itself is a charged,
deterministic subroutine on a valid guarded representation. -/
theorem extractOutput_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (input output : Tape) :
    evalConfigWithin (Program.withSubroutine pre extractOutput suffix returnPc)
      ((extractToScratchStart beforeInput beforeOutput input output).rebasePc pre.length)
      (extractOutputSteps input output) =
      PMF.pure ((extractOutputFinish beforeInput beforeOutput input output).resumeAt returnPc) :=
  (extractOutput_runs beforeInput beforeOutput input output).evalConfigWithin_withSubroutine_halted_of_closed
    pre extractOutput suffix returnPc (by simp [extractToScratchStart, start, extractOutput])
    rfl rfl extractOutput_control_closed extractOutput_no_randomBit

private theorem extraction_halted_eval (p : Program) (c : Configuration)
    (hHalted : c.halted = true) (steps : Nat) : evalConfigWithin p c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, hHalted]

/-- A common upper budget for all valid represented source tapes. Padding
occurs only after the actual final halt, and therefore changes neither tape
nor probability. No standalone bound is asserted for malformed regions. -/
theorem extractOutput_eval_at_bound (beforeInput beforeOutput : List (Option Bool))
    (input output : Tape) :
    evalConfigWithin extractOutput (extractToScratchStart beforeInput beforeOutput input output)
      (28 * (input.cells + output.cells) + 26) =
      PMF.pure (extractOutputFinish beforeInput beforeOutput input output) := by
  have hFits := extractOutputSteps_le input output
  rw [show 28 * (input.cells + output.cells) + 26 = extractOutputSteps input output +
      (28 * (input.cells + output.cells) + 26 - extractOutputSteps input output) by omega,
    evalConfigWithin_add, extractOutput_eval, PMF.pure_bind]
  exact extraction_halted_eval _ _ rfl _

/-- Every possible operational branch from the valid guarded layout has
halted by the linear upper budget, not just the constructed native trace. -/
theorem extractOutput_all_branches_halted (beforeInput beforeOutput : List (Option Bool))
    (input output : Tape) (final : Configuration)
    (run : PaddedRunsFor extractOutput (extractToScratchStart beforeInput beforeOutput input output)
      final (28 * (input.cells + output.cells) + 26)) : final.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [extractOutput_eval_at_bound] at hMem
  have hFinal : final = extractOutputFinish beforeInput beforeOutput input output := by simpa using hMem
  subst final
  rfl

theorem extractOutput_rawOutput_eval (beforeInput : List (Option Bool)) (input output : Tape) :
    (evalConfigWithin extractOutput (extractToScratchStart beforeInput [] input output)
      (28 * (input.cells + output.cells) + 26)).map
        (fun c => if c.halted then some c.outputBits else none) = PMF.pure (some output.bits) := by
  rw [extractOutput_eval_at_bound, PMF.pure_map]
  simp only [extractOutputFinish, copyScratchFinish, ↓reduceIte]
  exact congrArg (fun bits => PMF.pure (some bits)) (extractOutputFinish_outputBits beforeInput input output)

/-- Rewinding and copying restore the scratch input's final head position,
and the output's saved prefix remains immediately left of the copied bits. -/
theorem extractOutputFinish_preserves_saved_data
    (beforeInput beforeOutput : List (Option Bool)) (input output : Tape) :
    (extractOutputFinish beforeInput beforeOutput input output).inputTape =
        (extractToScratchFinish beforeInput beforeOutput input output).inputTape ∧
      (extractOutputFinish beforeInput beforeOutput input output).outputTape.left.drop
        output.bits.length = beforeOutput := by
  constructor
  · rfl
  · simp [extractOutputFinish, copyScratchFinish]

private theorem seekScratchInput_cell_from_anyTape (input output : Tape) (cell : Option Bool)
    (hCell : input.current = cell) :
    RunsFor seekScratchInput ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := if cell = none then 4 else 0, inputTape := input.moveRight,
         outputTape := output, halted := cell = none } : Configuration) 3 := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let selected : Configuration := { start with pc := if cell = none then 3 else 1 }
  let moved : Configuration := { selected with pc := if cell = none then 4 else 2, inputTape := input.moveRight }
  have h0 : Step seekScratchInput start selected := by
    cases cell with
    | none => simp [Step, successors, next, seekScratchInput, start, selected, Instruction.next, Configuration.tape, hCell]
    | some bit => cases bit <;> simp [Step, successors, next, seekScratchInput, start, selected,
        Instruction.next, Configuration.tape, hCell]
  have h1 : Step seekScratchInput selected moved := by
    cases cell <;> simp [Step, successors, next, seekScratchInput, start, selected, moved,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step seekScratchInput moved
      ({ pc := if cell = none then 4 else 0, inputTape := input.moveRight,
         outputTape := output, halted := cell = none } : Configuration) := by
    cases cell <;> simp [Step, successors, next, seekScratchInput, start, selected, moved, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) h2

private theorem seekScratchInput_exact_cells (left right : List (Option Bool))
    (current : Option Bool) (output : Tape) :
    let input : Tape := { left := left, current := current, right := right }
    let moves := ((current :: right).takeWhile Option.isSome).length + 1
    RunsFor seekScratchInput
      ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 4, inputTape := (Tape.moveRight^[moves]) input,
         outputTape := output, halted := true } : Configuration) (3 * moves) := by
  induction right generalizing left current with
  | nil =>
      let input : Tape := { left := left, current := current }
      have hCell := seekScratchInput_cell_from_anyTape input output current rfl
      cases current with
      | none =>
          simpa [input, List.takeWhile, Function.iterate_succ_apply] using hCell
      | some bit =>
          have hBlank := seekScratchInput_cell_from_anyTape input.moveRight output none rfl
          simpa [input, List.takeWhile, Function.iterate_succ_apply, Tape.moveRight] using hCell.trans hBlank
  | cons cell rest ih =>
      let input : Tape := { left := left, current := current, right := cell :: rest }
      have hCell := seekScratchInput_cell_from_anyTape input output current rfl
      cases current with
      | none =>
          simpa [input, List.takeWhile, Function.iterate_succ_apply] using hCell
      | some bit =>
          have hRest := ih (some bit :: left) cell
          change RunsFor seekScratchInput
            ({ inputTape := input.moveRight, outputTape := output } : Configuration)
            ({ pc := 4, inputTape := (Tape.moveRight^[((cell :: rest).takeWhile Option.isSome).length + 1]) input.moveRight,
               outputTape := output, halted := true } : Configuration)
            (3 * (((cell :: rest).takeWhile Option.isSome).length + 1)) at hRest
          have hMoves : ((some bit :: cell :: rest).takeWhile Option.isSome).length + 1 =
              (((cell :: rest).takeWhile Option.isSome).length + 1) + 1 := by
            simp [List.takeWhile, Nat.add_assoc]
          dsimp only
          rw [hMoves, Function.iterate_succ_apply]
          simpa [input, Nat.mul_add, Nat.add_comm] using hCell.trans hRest

/-- Exact head movement and transition count on arbitrary retained input.
The native scanner consumes the leading bit cells and their first blank;
it leaves all other cells on the same physical tape. `takeWhile` describes
that trace mathematically and is not a machine instruction. -/
theorem seekScratchInput_runs_from_anyTape (input output : Tape) :
    let moves := ((input.current :: input.right).takeWhile Option.isSome).length + 1
    RunsFor seekScratchInput
      ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 4, inputTape := (Tape.moveRight^[moves]) input,
         outputTape := output, halted := true } : Configuration) (3 * moves) :=
  seekScratchInput_exact_cells input.left input.right input.current output

/-- Every halted trace of the native scan has the exact retained input
position computed by its leading bit cells. This identifies an existing
physical tape, and does not replace it with a new input fixture. -/
theorem seekScratchInput_halted_input_layout (input output : Tape)
    (finish : Configuration) (used : Nat)
    (run : RunsFor seekScratchInput
      ({ inputTape := input, outputTape := output } : Configuration) finish used)
    (hHalted : finish.halted = true) :
    let moves := ((input.current :: input.right).takeWhile Option.isSome).length + 1
    finish.inputTape = (Tape.moveRight^[moves]) input ∧ finish.outputTape = output := by
  have hFinish := run.halted_finish_eq_of_no_randomBit
    (seekScratchInput_runs_from_anyTape input output) hHalted rfl seekScratchInput_no_randomBit
  rw [hFinish]
  exact ⟨rfl, rfl⟩

private theorem moveRight_scan_left (left right : List (Option Bool))
    (current : Option Bool) :
    let input : Tape := { left := left, current := current, right := right }
    let leading := (current :: right).takeWhile Option.isSome
    ((Tape.moveRight^[leading.length + 1]) input).left = none :: leading.reverse ++ left := by
  induction right generalizing left current with
  | nil =>
      cases current <;> simp [List.takeWhile, Function.iterate_succ_apply, Tape.moveRight]
  | cons cell rest ih =>
      cases current with
      | none => simp [List.takeWhile, Tape.moveRight]
      | some bit =>
          have hMoves : ((some bit :: cell :: rest).takeWhile Option.isSome).length + 1 =
              (((cell :: rest).takeWhile Option.isSome).length + 1) + 1 := by
            simp [List.takeWhile, Nat.add_assoc]
          dsimp only
          rw [hMoves, Function.iterate_succ_apply]
          simpa [Tape.moveRight, List.takeWhile, List.reverse_cons, List.append_assoc] using
            ih (some bit :: left) cell

/-- The crossed blank remains immediately behind the returned head. All
leading bit cells and the caller's earlier cells are retained to its left.
This separator is a postcondition of the actual scan, including when the
first blank lies outside the explicitly represented finite cells. -/
theorem seekScratchInput_halted_input_left (input output : Tape)
    (finish : Configuration) (used : Nat)
    (run : RunsFor seekScratchInput
      ({ inputTape := input, outputTape := output } : Configuration) finish used)
    (hHalted : finish.halted = true) :
    finish.inputTape.left =
      none :: ((input.current :: input.right).takeWhile Option.isSome).reverse ++ input.left := by
  obtain ⟨hInput, _⟩ := seekScratchInput_halted_input_layout input output finish used run hHalted
  rw [hInput]
  exact moveRight_scan_left input.left input.right input.current

private theorem moveRight_iterate_right (input : Tape) (moves : Nat) :
    ((Tape.moveRight^[moves]) input).right = input.right.drop moves := by
  induction moves generalizing input with
  | zero => simp
  | succ moves ih =>
      rw [Function.iterate_succ_apply, ih]
      cases input with
      | mk left current right =>
          cases right <;> simp [Tape.moveRight]

private theorem moveRight_iterate_current (input : Tape) (moves : Nat) :
    ((Tape.moveRight^[moves]) input).current =
      (input.current :: input.right).getD moves none := by
  induction moves generalizing input with
  | zero => simp
  | succ moves ih =>
      rw [Function.iterate_succ_apply, ih]
      cases input with
      | mk left current right =>
          cases right with
          | nil => cases moves <;> simp [Tape.moveRight]
          | cons cell rest => simp [Tape.moveRight]

/-- The cells still visible after right-only head motion are the original
remaining cells with that many cells consumed. Past the represented end,
the head observes the one virtual blank rather than a new input payload. -/
theorem moveRight_iterate_remaining (input : Tape) (moves : Nat) :
    let remaining := (input.current :: input.right).drop moves
    ((Tape.moveRight^[moves]) input).current :: ((Tape.moveRight^[moves]) input).right =
      if remaining = [] then [none] else remaining := by
  induction moves generalizing input with
  | zero => simp
  | succ moves ih =>
      rw [Function.iterate_succ_apply]
      have h := ih input.moveRight
      cases input with
      | mk left current right =>
          cases right with
          | nil =>
              cases moves with
              | zero => simp [Tape.moveRight]
              | succ moves => simpa [Tape.moveRight] using h
          | cons cell rest => simpa [Tape.moveRight] using h

/-- Exact current-cell and right-suffix observations after the scan. In
particular an internal blank does not imply that all later cells are blank;
the original cells beyond that separator remain available to the caller. -/
theorem seekScratchInput_halted_input_cells (input output : Tape)
    (finish : Configuration) (used : Nat)
    (run : RunsFor seekScratchInput
      ({ inputTape := input, outputTape := output } : Configuration) finish used)
    (hHalted : finish.halted = true) :
    let moves := ((input.current :: input.right).takeWhile Option.isSome).length + 1
    finish.inputTape.current = (input.current :: input.right).getD moves none ∧
      finish.inputTape.right = input.right.drop moves := by
  obtain ⟨hInput, _⟩ := seekScratchInput_halted_input_layout input output finish used run hHalted
  rw [hInput]
  exact ⟨moveRight_iterate_current input _, moveRight_iterate_right input _⟩

/-- The retained cells after a completed scan are the suffix past the first
blank. If no represented cells remain, the physical head observes a blank
with an empty right side. The extra `[none]` records that current cell. -/
theorem seekScratchInput_halted_input_remaining (input output : Tape)
    (finish : Configuration) (used : Nat)
    (run : RunsFor seekScratchInput
      ({ inputTape := input, outputTape := output } : Configuration) finish used)
    (hHalted : finish.halted = true) :
    let remaining := (input.current :: input.right).drop
      (((input.current :: input.right).takeWhile Option.isSome).length + 1)
    finish.inputTape.current :: finish.inputTape.right =
      if remaining = [] then [none] else remaining := by
  obtain ⟨hInput, _⟩ := seekScratchInput_halted_input_layout input output finish used run hHalted
  rw [hInput]
  exact moveRight_iterate_remaining input _

private theorem seekScratchInput_finite_cells (left right : List (Option Bool))
    (current : Option Bool) (output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 3 * (right.length + 1) + 3 ∧
      RunsFor seekScratchInput
        ({ inputTape := { left := left, current := current, right := right }, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.outputTape = output := by
  let input : Tape := { left := left, current := current, right := right }
  let moves := ((current :: right).takeWhile Option.isSome).length + 1
  let finish : Configuration :=
    { pc := 4, inputTape := (Tape.moveRight^[moves]) input,
      outputTape := output, halted := true }
  refine ⟨finish, 3 * moves, ?_,
    seekScratchInput_exact_cells left right current output, rfl, rfl⟩
  have hPrefix := (List.takeWhile_sublist (l := current :: right) Option.isSome).length_le
  simp only [List.length_cons] at hPrefix
  dsimp only [moves]
  omega

/-- Linear stopping bound after arbitrary retained-tape computation. The
scan stops at the first physical blank and moves one further cell. Saved
output data are preserved; no valid scratch-region layout is inferred for
malformed caller input containing internal blanks. -/
theorem seekScratchInput_terminates_from_anyTape (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 3 * input.cells + 3 ∧
      RunsFor seekScratchInput ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output := by
  obtain ⟨finish, used, hBound, hRun, hHalted, hOutput⟩ :=
    seekScratchInput_finite_cells input.left input.right input.current output
  refine ⟨finish, used, ?_, hRun, hHalted, hOutput⟩
  dsimp only [Tape.cells]
  omega

end Machine.GuardedCompiler
