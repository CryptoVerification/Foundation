import Foundation.Machine.StoredOutputCleanup
import Foundation.Machine.TaggedGuess

namespace Machine

/-- Parse a raw tagged guess, compare it with the adjacent saved challenge,
then erase all remaining known output scratch blocks. The comparison bit
is physically retained in an input cell during cleanup. Malformed guesses
use the same false default as `taggedGuessValue`, before comparison. -/
def finishStoredTaggedGuess (count : Nat) : Program :=
  let pre := finishTaggedGuess.asSubroutine 0 28
  let cleanup := cleanStoredOutputBit count
  Program.withSubroutine pre cleanup [.halt] (pre.length + cleanup.length + 1)

def finishStoredTaggedGuessStart (beforeInput : List (Option Bool))
    (blocks : List (List Bool)) (challenge : Bool) (bits : List Bool) : Configuration :=
  finishTaggedGuessStart beforeInput (savedOutputBlocks blocks) challenge bits

def finishStoredTaggedGuessSteps (blocks : List (List Bool)) (bits : List Bool) : Nat :=
  (readTaggedGuessBudget bits + 7) + (cleanStoredOutputBitSteps blocks + 1)

def finishStoredTaggedGuessFinish (beforeInput : List (Option Bool))
    (blocks : List (List Bool)) (challenge : Bool) (bits : List Bool) : Configuration :=
  let input := (readTaggedGuessFinish beforeInput (some challenge :: savedOutputBlocks blocks) bits).inputTape
  { cleanStoredOutputBitFinish input blocks [none] (taggedGuessValue bits == challenge) with
    pc := 28 + (cleanStoredOutputBit blocks.length).length + 1 }

theorem finishStoredTaggedGuess_eval (beforeInput : List (Option Bool))
    (blocks : List (List Bool)) (challenge : Bool) (bits : List Bool) :
    evalConfigWithin (finishStoredTaggedGuess blocks.length)
      (finishStoredTaggedGuessStart beforeInput blocks challenge bits)
      (finishStoredTaggedGuessSteps blocks bits) =
      PMF.pure (finishStoredTaggedGuessFinish beforeInput blocks challenge bits) := by
  let pre := finishTaggedGuess.asSubroutine 0 28
  let cleanup := cleanStoredOutputBit blocks.length
  let finalPc := 28 + cleanup.length + 1
  let input := (readTaggedGuessFinish beforeInput (some challenge :: savedOutputBlocks blocks) bits).inputTape
  let start := cleanStoredOutputBitStart input blocks [none] (taggedGuessValue bits == challenge)
  have hPre : pre.length = 28 := by
    simp [pre, Program.asSubroutine_length, finishTaggedGuess, readTaggedGuess, matchPreviousOutputBit]
  have first := (finishTaggedGuess_runs beforeInput (savedOutputBlocks blocks) challenge bits).evalConfigWithin_withSubroutine_halted_of_closed
    [] finishTaggedGuess (cleanup.asSubroutine 28 finalPc ++ [.halt]) 28
    (by change 0 < 27; decide) rfl rfl finishTaggedGuess_control_closed finishTaggedGuess_no_randomBit
  have hProgram : Program.withSubroutine [] finishTaggedGuess
      (cleanup.asSubroutine 28 finalPc ++ [.halt]) 28 = finishStoredTaggedGuess blocks.length := by
    simp only [Program.withSubroutine, finishStoredTaggedGuess, hPre,
      List.length_nil, List.nil_append, pre, cleanup, finalPc, List.append_assoc]
  rw [hProgram] at first
  have hStart : (finishTaggedGuessStart beforeInput (savedOutputBlocks blocks) challenge bits).rebasePc 0 =
      finishStoredTaggedGuessStart beforeInput blocks challenge bits := by
    simp [Configuration.rebasePc, finishStoredTaggedGuessStart, finishTaggedGuessStart, readTaggedGuessStart]
  have hMiddle : (finishTaggedGuessFinish beforeInput (savedOutputBlocks blocks) challenge bits).resumeAt 28 =
      start.rebasePc pre.length := by
    simp [finishTaggedGuessFinish, start, cleanStoredOutputBitStart, saveCurrentOutputBitStart,
      input, Configuration.rebasePc, Configuration.resumeAt, hPre]
  simp only [List.length_nil] at first
  rw [hStart, hMiddle] at first
  have last := Program.evalConfigWithin_withSubroutine_final_halt pre cleanup start
    (by change 0 ≤ cleanup.length; omega) rfl (cleanStoredOutputBitSteps blocks)
    (cleanStoredOutputBit_haltsFrom input blocks [none] (taggedGuessValue bits == challenge))
  have hLastProgram : Program.withSubroutine pre cleanup [.halt] (pre.length + cleanup.length + 1) =
      finishStoredTaggedGuess blocks.length := rfl
  dsimp only at last
  rw [hLastProgram] at last
  change evalConfigWithin (finishStoredTaggedGuess blocks.length) (start.rebasePc pre.length)
    (cleanStoredOutputBitSteps blocks + 1) = _ at last
  dsimp only [cleanup, start] at last
  rw [cleanStoredOutputBit_eval] at last
  have hLast : evalConfigWithin (finishStoredTaggedGuess blocks.length) (start.rebasePc pre.length)
      (cleanStoredOutputBitSteps blocks + 1) =
      PMF.pure (finishStoredTaggedGuessFinish beforeInput blocks challenge bits) := by
    simpa only [PMF.pure_map, finishStoredTaggedGuessFinish, hPre, input, cleanup, start,
      cleanStoredOutputBitFinish] using last
  rw [finishStoredTaggedGuessSteps, evalConfigWithin_add, first, PMF.pure_bind, hLast]

theorem finishStoredTaggedGuessFinish_output (beforeInput : List (Option Bool))
    (blocks : List (List Bool)) (challenge : Bool) (bits : List Bool) :
    (finishStoredTaggedGuessFinish beforeInput blocks challenge bits).outputBits =
      [taggedGuessValue bits == challenge] := by
  simpa only [finishStoredTaggedGuessFinish, Configuration.outputBits, List.replicate_succ, List.replicate_zero] using
    cleanStoredOutputBitFinish_output
      (readTaggedGuessFinish beforeInput (some challenge :: savedOutputBlocks blocks) bits).inputTape
      blocks 1 (taggedGuessValue bits == challenge)

theorem finishStoredTaggedGuess_evalResult (beforeInput : List (Option Bool))
    (blocks : List (List Bool)) (challenge : Bool) (bits : List Bool) :
    (evalConfigWithin (finishStoredTaggedGuess blocks.length)
      (finishStoredTaggedGuessStart beforeInput blocks challenge bits)
      (finishStoredTaggedGuessSteps blocks bits)).map (fun c => (c.halted, c.outputBits)) =
      PMF.pure (true, [taggedGuessValue bits == challenge]) := by
  rw [finishStoredTaggedGuess_eval, PMF.pure_map, finishStoredTaggedGuessFinish_output]
  rfl

theorem finishStoredTaggedGuess_haltsFrom (beforeInput : List (Option Bool))
    (blocks : List (List Bool)) (challenge : Bool) (bits : List Bool) :
    ∀ c, PaddedRunsFor (finishStoredTaggedGuess blocks.length)
      (finishStoredTaggedGuessStart beforeInput blocks challenge bits) c
      (finishStoredTaggedGuessSteps blocks bits) → c.halted = true := by
  intro c run
  have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [finishStoredTaggedGuess_eval] at hc
  have heq : c = finishStoredTaggedGuessFinish beforeInput blocks challenge bits := by simpa using hc
  rw [heq]; rfl

theorem finishStoredTaggedGuess_length (count : Nat) :
    (finishStoredTaggedGuess count).length = 8 * count + 47 := by
  simp [finishStoredTaggedGuess, Program.withSubroutine, Program.asSubroutine_length,
    finishTaggedGuess, readTaggedGuess, matchPreviousOutputBit, cleanStoredOutputBit_length]
  omega

theorem finishStoredTaggedGuess_steps_le (blocks : List (List Bool)) (bits : List Bool) :
    finishStoredTaggedGuessSteps blocks bits ≤
      4 * ((blocks.map List.length).sum + blocks.length) + 25 := by
  have h := readTaggedGuess_budget_le bits
  rw [finishStoredTaggedGuessSteps, cleanStoredOutputBit_steps]
  omega

/-- Parse, compare, and clean up actual arbitrary finite tapes. Missing
challenge cells and malformed guess strings do not affect the stopping
certificate. No known transcript layout is required by this runtime proof. -/
theorem finishStoredTaggedGuess_terminates_from_anyTape (count : Nat) (input output : Tape) :
    ∃ finish used,
      used ≤ (count + 1) * 10000 * (output.cells + 1) ∧
      RunsFor (finishStoredTaggedGuess count)
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧ finish.halted = true := by
  obtain ⟨parsed, parseTime, hParseTime, parseRun, parseHalt⟩ :=
    finishTaggedGuess_terminates_from_anyTape input output
  obtain ⟨cleaned, cleanTime, hCleanTime, cleanRun, cleanHalt⟩ :=
    cleanStoredOutputBit_terminates_from_anyTape count parsed.inputTape parsed.outputTape
  let pre := finishTaggedGuess.asSubroutine 0 28
  let cleanup := cleanStoredOutputBit count
  let finalPc := 28 + cleanup.length + 1
  obtain ⟨parseUsed, hParseUsed, first⟩ := parseRun.withSubroutine_halted
    [] finishTaggedGuess (cleanup.asSubroutine 28 finalPc ++ [.halt]) 28
    (Nat.zero_le _) rfl parseHalt
  have firstProgram : Program.withSubroutine [] finishTaggedGuess
      (cleanup.asSubroutine 28 finalPc ++ [.halt]) 28 = finishStoredTaggedGuess count := by
    simp only [finishStoredTaggedGuess, Program.withSubroutine, List.length_nil, List.nil_append,
      cleanup, finalPc, show (finishTaggedGuess.asSubroutine 0 28).length = 28 from rfl,
      List.append_assoc]
  rw [firstProgram] at first
  change RunsFor (finishStoredTaggedGuess count)
    ({ inputTape := input, outputTape := output } : Configuration) (parsed.resumeAt 28) parseUsed at first
  obtain ⟨cleanUsed, hCleanUsed, second⟩ := cleanRun.withSubroutine_halted
    pre cleanup [.halt] finalPc (Nat.zero_le _) rfl cleanHalt
  change RunsFor (finishStoredTaggedGuess count) (parsed.resumeAt 28) (cleaned.resumeAt finalPc) cleanUsed at second
  let finish : Configuration := { cleaned with pc := finalPc, halted := true }
  have last : Step (finishStoredTaggedGuess count) (cleaned.resumeAt finalPc) finish := by
    have code : (finishStoredTaggedGuess count)[finalPc]? = some .halt := by
      change (Program.withSubroutine pre cleanup [.halt] finalPc)[finalPc]? = some .halt
      have h := Program.withSubroutine_getElem?_suffix pre cleanup [.halt] finalPc 0
      simpa only [show pre.length = 28 from rfl, Nat.add_zero, List.getElem?_cons_zero, finalPc] using h
    simp [Step, successors, next, Configuration.resumeAt, finish, code, Instruction.next]
  refine ⟨finish, parseUsed + cleanUsed + 1, ?_, RunsFor.succ (first.trans second) last, rfl⟩
  have hStorage := parseRun.toPadded.outputTape_cells_le
  change parsed.outputTape.cells ≤ output.cells + parseTime at hStorage
  have hCleanBound := hCleanTime.trans
    (Nat.mul_le_mul_left ((count + 1) * 100) (Nat.add_le_add_right hStorage 1))
  nlinarith

theorem finishStoredTaggedGuess_no_randomBit (count : Nat) (tape : TapeId) :
    Instruction.randomBit tape ∉ finishStoredTaggedGuess count := by
  simp [finishStoredTaggedGuess, Program.withSubroutine, Program.asSubroutine, Instruction.asSubroutine,
    finishTaggedGuess, readTaggedGuess, matchPreviousOutputBit]
  intro instruction hMem hEq
  cases instruction <;> simp_all [cleanStoredOutputBit_no_randomBit]

theorem finishStoredTaggedGuess_haltsFrom_anyTape (count : Nat) (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor (finishStoredTaggedGuess count)
      ({ inputTape := input, outputTape := output } : Configuration) finish
      ((count + 1) * 10000 * (output.cells + 1))) : finish.halted = true := by
  obtain ⟨target, used, hBound, actual, hHalt⟩ := finishStoredTaggedGuess_terminates_from_anyTape count input output
  exact actual.haltsFrom_of_no_randomBit hHalt (finishStoredTaggedGuess_no_randomBit count) hBound finish run

end Machine
