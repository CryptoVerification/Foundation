import Foundation.Crypto.Semantics.Machine.Adversary
import Foundation.Crypto.Semantics.Machine.PolynomialTime
import Foundation.Crypto.Semantics.Machine.TapeEquivalence
import Mathlib.Data.List.GetD

namespace Machine

/-- Skip one `frame bits` on the input tape using a unary counter on an
initially blank output tape. Counting, consuming the payload, and erasing the
counter use actual bit-level transitions. The input is not overwritten.
This routine does not parse arbitrary dirty or noncontiguous caller tapes. -/
def skipFrame : Program :=
  [.branch .input 12 5 1,
   .write .output true, .moveRight .input, .moveRight .output, .jump 0,
   .moveRight .input, .moveLeft .output,
   .branch .output 12 8 8,
   .erase .output, .moveRight .input, .moveLeft .output, .jump 7,
   .halt]

private def advanceTape (t : Tape) : Nat → Tape
  | 0 => t
  | n + 1 => advanceTape t.moveRight n

private def counterTape : Nat → List (Option Bool) → Tape
  | 0, right => { right := right }
  | n + 1, right =>
      { left := List.replicate n (some true), current := some true, right := right }

private def consumeState (n : Nat) (right : List (Option Bool))
    (input : Tape) : Configuration :=
  { pc := 7, inputTape := input, outputTape := counterTape n right }

private def consumeFinish (n : Nat) (right : List (Option Bool))
    (input : Tape) : Configuration :=
  { pc := 12,
    inputTape := advanceTape input n,
    outputTape := { right := List.replicate n none ++ right },
    halted := true }

private theorem consume_run (n : Nat) (right : List (Option Bool))
    (input : Tape) :
    RunsFor skipFrame (consumeState n right input)
      (consumeFinish n right input) (5 * n + 2) := by
  induction n generalizing right input with
  | zero =>
      have hBranch : Step skipFrame (consumeState 0 right input)
          { consumeState 0 right input with pc := 12 } := by
        simp [Step, successors, next, skipFrame, consumeState, counterTape,
          Instruction.next, Configuration.tape]
      have hHalt : Step skipFrame
          ({ consumeState 0 right input with pc := 12 } : Configuration)
          (consumeFinish 0 right input) := by
        simp [Step, successors, next, skipFrame, consumeState, consumeFinish,
          counterTape, advanceTape, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch) hHalt
  | succ n ih =>
      let start := consumeState (n + 1) right input
      let selected : Configuration := { start with pc := 8 }
      let erased : Configuration :=
        { selected with pc := 9, outputTape := selected.outputTape.write none }
      let movedInput : Configuration :=
        { erased with pc := 10, inputTape := input.moveRight }
      let movedOutput : Configuration :=
        { movedInput with pc := 11, outputTape := movedInput.outputTape.moveLeft }
      have hBranch : Step skipFrame start selected := by
        simp [Step, successors, next, skipFrame, consumeState, counterTape,
          start, selected, Instruction.next, Configuration.tape]
      have hErase : Step skipFrame selected erased := by
        simp [Step, successors, next, skipFrame, consumeState, counterTape,
          start, selected, erased, Instruction.next, Configuration.updateTape,
          Configuration.advance]
      have hInput : Step skipFrame erased movedInput := by
        simp [Step, successors, next, skipFrame, consumeState, counterTape,
          start, selected, erased, movedInput, Instruction.next,
          Configuration.updateTape, Configuration.advance]
      have hOutput : Step skipFrame movedInput movedOutput := by
        simp [Step, successors, next, skipFrame, consumeState, counterTape,
          start, selected, erased, movedInput, movedOutput, Instruction.next,
          Configuration.updateTape, Configuration.advance]
      have hBack : Step skipFrame movedOutput
          (consumeState n (none :: right) input.moveRight) := by
        cases n <;> simp [Step, successors, next, skipFrame, consumeState,
          counterTape, start, selected, erased, movedInput, movedOutput,
          Instruction.next, Tape.moveLeft, Tape.write, List.replicate_succ]
      have hFinish : consumeFinish n (none :: right) input.moveRight =
          consumeFinish (n + 1) right input := by
        simp [consumeFinish, advanceTape, List.replicate_succ', List.append_assoc]
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch) hErase)
          hInput) hOutput) hBack).trans (ih (none :: right) input.moveRight)
      rw [hFinish] at run
      convert run using 1
      omega

private def readState (prefixBits : List (Option Bool))
    (copied : Nat) (bits : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits bits with
      left := List.replicate copied (some true) ++ prefixBits },
    outputTape := { left := List.replicate copied (some true) } }

private def payloadTape (prefixBits : List (Option Bool))
    (count : Nat) (rest : List Bool) : Tape :=
  { Tape.ofBits rest with
    left := some false :: (List.replicate count (some true) ++ prefixBits) }

private theorem read_one (prefixBits : List (Option Bool))
    (copied : Nat) (rest : List Bool) :
    RunsFor skipFrame (readState prefixBits copied (true :: rest))
      (readState prefixBits (copied + 1) rest) 5 := by
  let start := readState prefixBits copied (true :: rest)
  let selected : Configuration := { start with pc := 1 }
  let written : Configuration :=
    { selected with pc := 2, outputTape := selected.outputTape.write (some true) }
  let movedInput : Configuration :=
    { written with pc := 3, inputTape := written.inputTape.moveRight }
  let movedOutput : Configuration :=
    { movedInput with pc := 4, outputTape := movedInput.outputTape.moveRight }
  have hBranch : Step skipFrame start selected := by
    simp [Step, successors, next, skipFrame, start, selected, readState,
      Tape.ofBits, Instruction.next, Configuration.tape]
  have hWrite : Step skipFrame selected written := by
    simp [Step, successors, next, skipFrame, start, selected, written, readState,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hInput : Step skipFrame written movedInput := by
    simp [Step, successors, next, skipFrame, start, selected, written,
      movedInput, readState, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hOutput : Step skipFrame movedInput movedOutput := by
    simp [Step, successors, next, skipFrame, start, selected, written,
      movedInput, movedOutput, readState, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hBack : Step skipFrame movedOutput (readState prefixBits (copied + 1) rest) := by
    cases rest <;> simp [Step, successors, next, skipFrame, start, selected,
      written, movedInput, movedOutput, readState, Instruction.next,
      Tape.moveRight, Tape.write, Tape.ofBits, List.replicate_succ]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) hBranch) hWrite) hInput) hOutput) hBack

private theorem read_run (prefixBits : List (Option Bool))
    (remaining copied : Nat) (rest : List Bool) :
    RunsFor skipFrame
      (readState prefixBits copied (List.replicate remaining true ++ false :: rest))
      (consumeState (copied + remaining) [none]
        (payloadTape prefixBits (copied + remaining) rest)) (5 * remaining + 3) := by
  induction remaining generalizing copied with
  | zero =>
      let start := readState prefixBits copied (false :: rest)
      let selected : Configuration := { start with pc := 5 }
      let movedInput : Configuration :=
        { selected with pc := 6, inputTape := selected.inputTape.moveRight }
      have hBranch : Step skipFrame start selected := by
        simp [Step, successors, next, skipFrame, start, selected, readState,
          Tape.ofBits, Instruction.next, Configuration.tape]
      have hInput : Step skipFrame selected movedInput := by
        simp [Step, successors, next, skipFrame, start, selected, movedInput,
          readState, Instruction.next, Configuration.updateTape,
          Configuration.advance]
      have hOutput : Step skipFrame movedInput
          (consumeState copied [none] (payloadTape prefixBits copied rest)) := by
        cases copied <;> cases rest <;> simp [Step, successors, next,
          skipFrame, start, selected, movedInput, readState, consumeState,
          payloadTape, counterTape, Instruction.next, Configuration.updateTape,
          Configuration.advance, Tape.moveRight, Tape.moveLeft, Tape.ofBits,
          List.replicate_succ]
      simpa using RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) hBranch) hInput) hOutput
  | succ remaining ih =>
      have run := (read_one prefixBits copied (List.replicate remaining true ++ false :: rest)).trans
        (ih (copied + 1))
      simpa [List.replicate_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using run

/-- Exact halted state after a frame whose advertised length is `count`.
The counter tape is blank again. The input head has advanced past exactly
`count` payload cells, even if malformed input ends before that many cells. -/
def skipFrameFinish (count : Nat) (rest : List Bool)
    (prefixBits : List (Option Bool) := []) : Configuration :=
  { pc := 12,
    inputTape := advanceTape (payloadTape prefixBits count rest) count,
    outputTape := { right := List.replicate (count + 1) none },
    halted := true }

/-- Invocation state at a frame boundary, with previously read input cells
retained to the left of the head and a blank scratch tape. -/
def skipFrameStart (count : Nat) (rest : List Bool)
    (prefixBits : List (Option Bool) := []) : Configuration :=
  { inputTape := { Tape.ofBits (List.replicate count true ++ false :: rest)
      with left := prefixBits } }

theorem skipFrame_runs_from (prefixBits : List (Option Bool))
    (count : Nat) (rest : List Bool) :
    RunsFor skipFrame (skipFrameStart count rest prefixBits)
      (skipFrameFinish count rest prefixBits) (10 * count + 5) := by
  have reader := read_run prefixBits count 0 rest
  simp only [Nat.zero_add] at reader
  have run := reader.trans
    (consume_run count [none] (payloadTape prefixBits count rest))
  have hCount : 5 * count + 3 + (5 * count + 2) = 10 * count + 5 := by omega
  rw [hCount] at run
  simpa [readState, skipFrameStart, skipFrameFinish, consumeFinish,
    List.replicate_succ'] using run

theorem skipFrame_runs (count : Nat) (rest : List Bool) :
    RunsFor skipFrame
      (Configuration.initial (List.replicate count true ++ false :: rest))
      (skipFrameFinish count rest) (10 * count + 5) := by
  have hInitial : skipFrameStart count rest [] =
      Configuration.initial (List.replicate count true ++ false :: rest) := by
    cases hBits : List.replicate count true ++ false :: rest <;>
      simp [skipFrameStart, Configuration.initial, hBits, Tape.ofBits]
  simpa only [hInitial] using skipFrame_runs_from [] count rest

private theorem advanceTape_bits (bits rest : List Bool)
    (left : List (Option Bool)) :
    advanceTape ({ Tape.ofBits (bits ++ rest) with left := left } : Tape)
      bits.length =
      { Tape.ofBits rest with left := bits.reverse.map some ++ left } := by
  induction bits generalizing left with
  | nil => simp [advanceTape]
  | cons bit bits ih =>
      have hMove : ({ Tape.ofBits ((bit :: bits) ++ rest) with left := left } : Tape).moveRight =
          { Tape.ofBits (bits ++ rest) with left := some bit :: left } := by
        cases hRest : bits ++ rest <;> simp [Tape.ofBits, Tape.moveRight, hRest]
      simp only [List.length_cons, advanceTape, hMove]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

/-- For a well-formed `frame bits`, the routine stops immediately before the
following field, retaining every prefix bit on the input tape. -/
theorem skipFrameFinish_input (bits rest : List Bool)
    (prefixBits : List (Option Bool) := []) :
    (skipFrameFinish bits.length (bits ++ rest) prefixBits).inputTape =
      { Tape.ofBits rest with
        left := bits.reverse.map some ++
          some false :: (List.replicate bits.length (some true) ++ prefixBits) } := by
  exact advanceTape_bits bits rest _

theorem skipFrameFinish_output_blank (count : Nat) (rest : List Bool)
    (prefixBits : List (Option Bool) := []) :
    (skipFrameFinish count rest prefixBits).outputTape.Equivalent ({} : Tape) := by
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro i
  simp [skipFrameFinish]

theorem skipFrame_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ skipFrame := by simp [skipFrame]

/-- Native source addresses remain inside the frame-skipping block until
its explicit halt, so a caller can embed the proved trace without extra
fall-through or return steps. -/
theorem skipFrame_control_closed (c d : Configuration)
    (hPc : c.pc < skipFrame.length) (step : Step skipFrame c d)
    (_hRunning : d.halted = false) : d.pc < skipFrame.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 13 at hPc
  change d.pc < 13
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, skipFrame,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

private theorem read_unterminated (prefixBits : List (Option Bool))
    (remaining copied : Nat) :
    RunsFor skipFrame (readState prefixBits copied (List.replicate remaining true))
      ({ readState prefixBits (copied + remaining) [] with
        pc := 12
        halted := true } : Configuration)
      (5 * remaining + 2) := by
  induction remaining generalizing copied with
  | zero =>
      have hBranch : Step skipFrame (readState prefixBits copied [])
          { readState prefixBits copied [] with pc := 12 } := by
        simp [Step, successors, next, skipFrame, readState, Tape.ofBits,
          Instruction.next, Configuration.tape]
      have hHalt : Step skipFrame
          ({ readState prefixBits copied [] with pc := 12 } : Configuration)
          ({ readState prefixBits copied [] with pc := 12, halted := true } : Configuration) := by
        simp [Step, successors, next, skipFrame, readState, Instruction.next]
      simpa using RunsFor.succ (RunsFor.succ (RunsFor.zero _) hBranch) hHalt
  | succ remaining ih =>
      have run := (read_one prefixBits copied (List.replicate remaining true)).trans
        (ih (copied + 1))
      simpa [List.replicate_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using run

private theorem unary_split (input : List Bool) :
    (∃ count, input = List.replicate count true) ∨
      (∃ count rest, input = List.replicate count true ++ false :: rest) := by
  induction input with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons bit rest ih =>
      cases bit with
      | false => exact Or.inr ⟨0, rest, rfl⟩
      | true =>
          rcases ih with ⟨count, h⟩ | ⟨count, tail, h⟩
          · exact Or.inl ⟨count + 1, by simp [h, List.replicate_succ]⟩
          · exact Or.inr ⟨count + 1, tail, by simp [h, List.replicate_succ]⟩

/-- Even malformed finite input terminates within a linear transition bound.
A missing delimiter halts on blank; a truncated payload consumes the unary
counter and then halts. No validity or well-formedness assumption is needed
for this all-input runtime assertion. -/
theorem skipFrame_terminates_from (prefixBits : List (Option Bool))
    (input : List Bool) :
    ∃ finish used, used ≤ 10 * input.length + 5 ∧
      RunsFor skipFrame
        ({ inputTape := { Tape.ofBits input with left := prefixBits } } : Configuration)
        finish used ∧
      finish.halted = true := by
  rcases unary_split input with ⟨count, hInput⟩ | ⟨count, rest, hInput⟩
  · subst input
    have run := read_unterminated prefixBits count 0
    have hInitial : readState prefixBits 0 (List.replicate count true) =
        ({ inputTape := { Tape.ofBits (List.replicate count true)
          with left := prefixBits } } : Configuration) := by
      simp [readState]
    rw [hInitial] at run
    refine ⟨_, 5 * count + 2, ?_, run, rfl⟩
    simp only [List.length_replicate]
    omega
  · subst input
    refine ⟨skipFrameFinish count rest prefixBits, 10 * count + 5, ?_,
      skipFrame_runs_from prefixBits count rest, rfl⟩
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega

theorem skipFrame_terminates (input : List Bool) :
    ∃ finish used, used ≤ 10 * input.length + 5 ∧
      RunsFor skipFrame (Configuration.initial input) finish used ∧
      finish.halted = true := by
  have hInitial : ({ inputTape := { Tape.ofBits input with left := [] } } : Configuration) =
      Configuration.initial input := by cases input <;> rfl
  simpa only [hInitial] using skipFrame_terminates_from [] input

theorem skipFrame_haltsWithin (input : List Bool) :
    HaltsWithin skipFrame input (10 * input.length + 5) := by
  obtain ⟨finish, used, hBound, run, hHalted⟩ := skipFrame_terminates input
  have hHalts : HaltsWith skipFrame input finish.outputBits used :=
    ⟨finish, run, hHalted, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit skipFrame_no_randomBit).mono hBound

/-- Polynomial time in total encoded input length, including on malformed
inputs. The proof measures actual bit-machine transitions on every branch. -/
theorem skipFrame_polynomialTime : PolynomialTime skipFrame := by
  refine ⟨fun m => 10 * m + 5, ?_, skipFrame_haltsWithin⟩
  exact ((PolynomiallyBounded.const 10).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 5)

/-- Exact probability semantics of framed-input preparation. This is a
machine computation, not an uncharged call to the mathematical `frame`. -/
theorem skipFrame_eval (bits rest : List Bool) :
    evalConfigWithin skipFrame (Configuration.initial (frame bits ++ rest))
      (10 * bits.length + 5) =
        PMF.pure (skipFrameFinish bits.length (bits ++ rest)) := by
  have run := skipFrame_runs bits.length (bits ++ rest)
  have hInput : List.replicate bits.length true ++ false :: (bits ++ rest) =
      frame bits ++ rest := by simp [frame, List.append_assoc]
  rw [hInput] at run
  exact run.evalConfigWithin_eq_pure_of_no_randomBit skipFrame_no_randomBit

private theorem advanceTape_suffix (before : List (Option Bool)) (bits : List Bool) (count : Nat) :
    ∃ left : List (Option Bool),
      advanceTape ({ Tape.ofBits bits with left := before } : Tape) count =
        { Tape.ofBits (bits.drop count) with left := left } := by
  induction count generalizing before bits with
  | zero => exact ⟨before, rfl⟩
  | succ count ih =>
      cases bits with
      | nil =>
          simpa [advanceTape, Tape.ofBits, Tape.moveRight] using ih (none :: before) []
      | cons bit rest =>
          cases rest with
          | nil =>
              simpa [advanceTape, Tape.ofBits, Tape.moveRight] using ih (some bit :: before) []
          | cons next tail =>
              simpa [advanceTape, Tape.ofBits, Tape.moveRight] using ih (some bit :: before) (next :: tail)

/-- The all-input stopping trace also leaves a contiguous unread suffix
and a blank current output cell followed by finitely many blank cells.
Even a truncated payload only moves past the finite input into blanks.
The retained prefixes may contain parser artifacts; they are not reset. -/
theorem skipFrame_terminates_with_layout (prefixBits : List (Option Bool)) (input : List Bool) :
    ∃ (finish : Configuration) (used : Nat) (beforeInput : List (Option Bool))
      (rest : List Bool) (beforeOutput : List (Option Bool)) (blanks : Nat),
      used ≤ 10 * input.length + 5 ∧
      RunsFor skipFrame
        ({ inputTape := { Tape.ofBits input with left := prefixBits } } : Configuration) finish used ∧
      finish.halted = true ∧
      finish.inputTape = { Tape.ofBits rest with left := beforeInput } ∧
      finish.outputTape = { left := beforeOutput, right := List.replicate blanks none } := by
  rcases unary_split input with ⟨count, hInput⟩ | ⟨count, rest, hInput⟩
  · subst input
    have hRun := read_unterminated prefixBits count 0
    have hStart : readState prefixBits 0 (List.replicate count true) =
        ({ inputTape := { Tape.ofBits (List.replicate count true) with left := prefixBits } } : Configuration) := by
      simp [readState]
    rw [hStart] at hRun
    refine ⟨_, 5 * count + 2, List.replicate count (some true) ++ prefixBits, [],
      List.replicate count (some true), 0, ?_, hRun, rfl, ?_, ?_⟩
    · simp only [List.length_replicate]; omega
    · simp [readState]
    · simp [readState]
  · subst input
    obtain ⟨before, hAdvance⟩ := advanceTape_suffix
      (some false :: (List.replicate count (some true) ++ prefixBits)) rest count
    refine ⟨skipFrameFinish count rest prefixBits, 10 * count + 5, before, rest.drop count,
      [], count + 1, ?_, skipFrame_runs_from prefixBits count rest, rfl, ?_, rfl⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons]; omega
    · simpa only [skipFrameFinish, payloadTape] using hAdvance

/-- The only time the frame skipper leaves a nonempty counter on its scratch
tape is when it reaches the end of the input before finding a delimiter.
Then no following parser can see a bit under the input head. -/
theorem skipFrame_terminates_clean_or_empty (prefixBits : List (Option Bool))
    (input : List Bool) :
    ∃ (finish : Configuration) (used : Nat) (beforeInput : List (Option Bool))
      (rest : List Bool) (beforeOutput : List (Option Bool)) (blanks : Nat),
      used ≤ 10 * input.length + 5 ∧
      RunsFor skipFrame
        ({ inputTape := { Tape.ofBits input with left := prefixBits } } : Configuration)
        finish used ∧
      finish.halted = true ∧
      finish.inputTape = { Tape.ofBits rest with left := beforeInput } ∧
      finish.outputTape = { left := beforeOutput, right := List.replicate blanks none } ∧
      rest.length ≤ input.length ∧
      (rest = [] ∨ beforeOutput = []) ∧
      (beforeOutput = [] ∨ ∃ count, beforeOutput = List.replicate count (some true)) := by
  rcases unary_split input with ⟨count, hInput⟩ | ⟨count, tail, hInput⟩
  · subst input
    have hRun := read_unterminated prefixBits count 0
    have hStart : readState prefixBits 0 (List.replicate count true) =
        ({ inputTape := { Tape.ofBits (List.replicate count true)
          with left := prefixBits } } : Configuration) := by
      simp [readState]
    rw [hStart] at hRun
    refine ⟨_, 5 * count + 2, List.replicate count (some true) ++ prefixBits,
      [], List.replicate count (some true), 0, ?_, hRun, rfl, ?_, ?_, ?_,
      Or.inl rfl, Or.inr ⟨count, rfl⟩⟩
    · simp only [List.length_replicate]; omega
    · simp [readState]
    · simp [readState]
    · simp
  · subst input
    obtain ⟨before, hAdvance⟩ := advanceTape_suffix
      (some false :: (List.replicate count (some true) ++ prefixBits)) tail count
    refine ⟨skipFrameFinish count tail prefixBits, 10 * count + 5, before,
      tail.drop count, [], count + 1, ?_, skipFrame_runs_from prefixBits count tail,
      rfl, ?_, rfl, ?_, Or.inr rfl, Or.inl rfl⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons]; omega
    · simpa only [skipFrameFinish, payloadTape] using hAdvance
    · simp only [List.length_drop, List.length_append, List.length_replicate,
        List.length_cons]
      omega


private theorem skipFrame_consume_blank (input output : Tape) (hBlank : output.current = none) :
    RunsFor skipFrame ({ pc := 7, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 12, inputTape := input, outputTape := output, halted := true } : Configuration) 2 := by
  have branch : Step skipFrame
      ({ pc := 7, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 12, inputTape := input, outputTape := output } : Configuration) := by
    simp [Step, successors, next, skipFrame, Instruction.next, Configuration.tape, hBlank]
  have halt : Step skipFrame
      ({ pc := 12, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 12, inputTape := input, outputTape := output, halted := true } : Configuration) := by
    simp [Step, successors, next, skipFrame, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) branch) halt

private theorem skipFrame_consume_cell (input output : Tape) (bit : Bool)
    (hCell : output.current = some bit) :
    RunsFor skipFrame ({ pc := 7, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 7, inputTape := input.moveRight, outputTape := (output.write none).moveLeft } : Configuration) 5 := by
  let selected : Configuration := { pc := 8, inputTape := input, outputTape := output }
  let erased : Configuration := { selected with pc := 9, outputTape := output.write none }
  let moved : Configuration := { erased with pc := 10, inputTape := input.moveRight }
  let back : Configuration := { moved with pc := 11, outputTape := (output.write none).moveLeft }
  have a : Step skipFrame
      ({ pc := 7, inputTape := input, outputTape := output } : Configuration) selected := by
    cases bit <;> simp [Step, successors, next, skipFrame, selected, Instruction.next,
      Configuration.tape, hCell]
  have b : Step skipFrame selected erased := by
    simp [Step, successors, next, skipFrame, selected, erased, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have c : Step skipFrame erased moved := by
    simp [Step, successors, next, skipFrame, erased, selected, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have d : Step skipFrame moved back := by
    simp [Step, successors, next, skipFrame, moved, erased, selected, back, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have e : Step skipFrame back
      ({ pc := 7, inputTape := input.moveRight, outputTape := (output.write none).moveLeft } : Configuration) := by
    simp [Step, successors, next, skipFrame, back, moved, erased, selected, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) a) b) c) d) e

/-- The counter loop also stops when the scratch tape contains unrelated
bits. Each nonblank iteration erases one cell and moves left; it can inspect
at most the finite left segment and the original current cell. -/
private theorem skipFrame_consume_anyTape (left : List (Option Bool))
    (input : Tape) (current : Option Bool) (right : List (Option Bool)) :
    ∃ finish used, used ≤ 5 * (left.length + 1) + 2 ∧
      RunsFor skipFrame
        ({ pc := 7, inputTape := input, outputTape := { left := left, current := current, right := right } } : Configuration)
        finish used ∧ finish.halted = true := by
  induction left generalizing input current right with
  | nil =>
      cases current with
      | none => exact ⟨_, 2, by simp, skipFrame_consume_blank input _ rfl, rfl⟩
      | some bit =>
          have first := skipFrame_consume_cell input
            ({ current := some bit, right := right } : Tape) bit rfl
          have last := skipFrame_consume_blank input.moveRight
            ({ right := none :: right } : Tape) rfl
          have run := first.trans last
          simpa [Tape.write, Tape.moveLeft] using
            (show ∃ finish used, used ≤ 5 * (0 + 1) + 2 ∧
              RunsFor skipFrame
                ({ pc := 7, inputTape := input, outputTape := { current := some bit, right := right } } : Configuration)
                finish used ∧ finish.halted = true from
              ⟨_, 7, by decide, run, rfl⟩)
  | cons cell rest ih =>
      cases current with
      | none => exact ⟨_, 2, by omega, skipFrame_consume_blank input _ rfl, rfl⟩
      | some bit =>
          obtain ⟨finish, used, hUsed, tailRun, hHalt⟩ := ih input.moveRight cell (none :: right)
          have first := skipFrame_consume_cell input
            ({ left := cell :: rest, current := some bit, right := right } : Tape) bit rfl
          have run := first.trans (by simpa [Tape.write, Tape.moveLeft] using tailRun)
          exact ⟨finish, 5 + used, by simp only [List.length_cons]; omega, run, hHalt⟩

private theorem skipFrame_count_cell (input output : Tape) (hCell : input.current = some true) :
    RunsFor skipFrame ({ inputTape := input, outputTape := output } : Configuration)
      ({ inputTape := input.moveRight, outputTape := (output.write (some true)).moveRight } : Configuration) 5 := by
  let selected : Configuration := { pc := 1, inputTape := input, outputTape := output }
  let written : Configuration := { selected with pc := 2, outputTape := output.write (some true) }
  let moved : Configuration := { written with pc := 3, inputTape := input.moveRight }
  let back : Configuration := { moved with pc := 4, outputTape := (output.write (some true)).moveRight }
  have a : Step skipFrame ({ inputTape := input, outputTape := output } : Configuration) selected := by
    simp [Step, successors, next, skipFrame, selected, Instruction.next, Configuration.tape, hCell]
  have b : Step skipFrame selected written := by
    simp [Step, successors, next, skipFrame, selected, written, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have c : Step skipFrame written moved := by
    simp [Step, successors, next, skipFrame, selected, written, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have d : Step skipFrame moved back := by
    simp [Step, successors, next, skipFrame, selected, written, moved, back, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have e : Step skipFrame back
      ({ inputTape := input.moveRight, outputTape := (output.write (some true)).moveRight } : Configuration) := by
    simp [Step, successors, next, skipFrame, selected, written, moved, back, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) a) b) c) d) e

private theorem skipFrame_header_blank (input output : Tape) (hBlank : input.current = none) :
    RunsFor skipFrame ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 12, inputTape := input, outputTape := output, halted := true } : Configuration) 2 := by
  have a : Step skipFrame ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 12, inputTape := input, outputTape := output } : Configuration) := by
    simp [Step, successors, next, skipFrame, Instruction.next, Configuration.tape, hBlank]
  have b : Step skipFrame ({ pc := 12, inputTape := input, outputTape := output } : Configuration)
      ({ pc := 12, inputTape := input, outputTape := output, halted := true } : Configuration) := by
    simp [Step, successors, next, skipFrame, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.zero _) a) b

private theorem skipFrame_header_delimiter (input output : Tape) (hCell : input.current = some false) :
    RunsFor skipFrame ({ inputTape := input, outputTape := output } : Configuration)
      ({ pc := 7, inputTape := input.moveRight, outputTape := output.moveLeft } : Configuration) 3 := by
  let selected : Configuration := { pc := 5, inputTape := input, outputTape := output }
  let moved : Configuration := { selected with pc := 6, inputTape := input.moveRight }
  have a : Step skipFrame ({ inputTape := input, outputTape := output } : Configuration) selected := by
    simp [Step, successors, next, skipFrame, selected, Instruction.next, Configuration.tape, hCell]
  have b : Step skipFrame selected moved := by
    simp [Step, successors, next, skipFrame, selected, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have c : Step skipFrame moved
      ({ pc := 7, inputTape := input.moveRight, outputTape := output.moveLeft } : Configuration) := by
    simp [Step, successors, next, skipFrame, selected, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.zero _) a) b) c

private theorem skipFrame_header_anyTape (right : List (Option Bool))
    (left : List (Option Bool)) (current : Option Bool) (output : Tape) :
    ∃ finish used, used ≤ 10 * (right.length + 1) + 5 * (output.left.length + 1) + 10 ∧
      RunsFor skipFrame
        ({ inputTape := { left := left, current := current, right := right }, outputTape := output } : Configuration) finish used ∧ finish.halted = true := by
  induction right generalizing left current output with
  | nil =>
      cases current with
      | none => exact ⟨_, 2, by omega, skipFrame_header_blank _ output rfl, rfl⟩
      | some bit =>
          cases bit with
          | true =>
              have first := skipFrame_count_cell
                ({ left := left, current := some true } : Tape) output rfl
              have last := skipFrame_header_blank
                ({ left := some true :: left } : Tape) ((output.write (some true)).moveRight) rfl
              have run := first.trans (by simpa [Tape.moveRight] using last)
              exact ⟨_, 7, by omega, run, rfl⟩
          | false =>
              obtain ⟨finish, used, hUsed, tailRun, hHalt⟩ := skipFrame_consume_anyTape
                output.moveLeft.left ({ left := left, current := some false } : Tape).moveRight
                output.moveLeft.current output.moveLeft.right
              have first := skipFrame_header_delimiter
                ({ left := left, current := some false } : Tape) output rfl
              have run := first.trans tailRun
              refine ⟨finish, 3 + used, ?_, run, hHalt⟩
              cases output with
              | mk before cell after => cases before <;> simp [Tape.moveLeft] at hUsed ⊢ <;> omega
  | cons cell rest ih =>
      cases current with
      | none => exact ⟨_, 2, by omega, skipFrame_header_blank _ output rfl, rfl⟩
      | some bit =>
          cases bit with
          | true =>
              obtain ⟨finish, used, hUsed, tailRun, hHalt⟩ := ih (some true :: left) cell
                ((output.write (some true)).moveRight)
              have first := skipFrame_count_cell
                ({ left := left, current := some true, right := cell :: rest } : Tape) output rfl
              have run := first.trans (by simpa [Tape.moveRight] using tailRun)
              refine ⟨finish, 5 + used, ?_, run, hHalt⟩
              cases output with
              | mk before old after => cases after <;>
                  simp [Tape.write, Tape.moveRight] at hUsed ⊢ <;> omega
          | false =>
              obtain ⟨finish, used, hUsed, tailRun, hHalt⟩ := skipFrame_consume_anyTape
                output.moveLeft.left
                ({ left := left, current := some false, right := cell :: rest } : Tape).moveRight
                output.moveLeft.current output.moveLeft.right
              have first := skipFrame_header_delimiter
                ({ left := left, current := some false, right := cell :: rest } : Tape) output rfl
              have run := first.trans tailRun
              refine ⟨finish, 3 + used, ?_, run, hHalt⟩
              cases output with
              | mk before old after => cases before <;> simp [Tape.moveLeft] at hUsed ⊢ <;> omega

/-- The native frame skipper stops on arbitrary finite caller tapes, including
internal blanks, missing delimiters, and a dirty scratch counter. This is a
stopping theorem only: it makes no successful parsing claim on malformed data. -/
theorem skipFrame_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 20 * (input.cells + output.cells) + 20 ∧
      RunsFor skipFrame ({ inputTape := input, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true := by
  obtain ⟨finish, used, hUsed, run, hHalt⟩ :=
    skipFrame_header_anyTape input.right input.left input.current output
  refine ⟨finish, used, ?_, run, hHalt⟩
  simp only [Tape.cells] at ⊢
  omega


/-- Every padded execution from the retained caller tapes has halted at the
same displayed budget. This uses the actual deterministic stopping trace. -/
theorem skipFrame_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor skipFrame
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (20 * (input.cells + output.cells) + 20)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ :=
    skipFrame_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted skipFrame_no_randomBit hBound finish trace

end Machine
