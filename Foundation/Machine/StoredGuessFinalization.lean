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

end Machine
