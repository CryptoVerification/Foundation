import Foundation.Machine.GuardedResult
import Foundation.Machine.BitstringErasure
import Foundation.Machine.TapeSwap
import Foundation.Machine.StoredGuessFinalization

namespace Machine

/-- Rewind the raw guess on the input tape while erasing its parallel
output copy. The output copy has a protected blank boundary, whereas the
input copy can be immediately adjacent to retained request bits. Therefore
the branch tests the output tape, not the input tape. The two heads move
in lockstep until that boundary; only the input head is restored right. -/
def rewindStoredGuess : Program :=
  [.moveLeft .input, .moveLeft .output, .branch .output 5 3 3,
   .erase .output, .jump 0, .moveRight .input, .halt]

private def storedRewindState (beforeInput beforeOutput : List (Option Bool))
    (boundary : Option Bool) (left : List Bool) (current : Option Bool)
    (inputRight outputRight : List (Option Bool)) : Configuration :=
  { inputTape := {
      left := left.map some ++ boundary :: beforeInput
      current := current
      right := inputRight },
    outputTape := { left := left.map some ++ none :: beforeOutput, right := outputRight } }

private def storedRewindFinish (beforeInput beforeOutput : List (Option Bool))
    (boundary : Option Bool) (left : List Bool) (current : Option Bool)
    (inputRight outputRight : List (Option Bool)) : Configuration :=
  { pc := 6,
    inputTape := ({
      left := beforeInput
      current := boundary
      right := left.reverse.map some ++ current :: inputRight } : Tape).moveRight,
    outputTape := {
      left := beforeOutput
      right := List.replicate (left.length + 1) none ++ outputRight },
    halted := true }

private theorem storedRewind_run (beforeInput beforeOutput : List (Option Bool))
    (boundary : Option Bool) (left : List Bool) (current : Option Bool)
    (inputRight outputRight : List (Option Bool)) :
    RunsFor rewindStoredGuess
      (storedRewindState beforeInput beforeOutput boundary left current inputRight outputRight)
      (storedRewindFinish beforeInput beforeOutput boundary left current inputRight outputRight)
      (5 * left.length + 5) := by
  induction left generalizing current inputRight outputRight with
  | nil =>
      let start := storedRewindState beforeInput beforeOutput boundary [] current inputRight outputRight
      let a : Configuration := { start with pc := 1, inputTape := start.inputTape.moveLeft }
      let b : Configuration := { a with pc := 2, outputTape := a.outputTape.moveLeft }
      let c : Configuration := { b with pc := 5 }
      let d : Configuration := { c with pc := 6, inputTape := c.inputTape.moveRight }
      have h₁ : Step rewindStoredGuess start a := by
        simp [Step, successors, next, rewindStoredGuess, start, a, storedRewindState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h₂ : Step rewindStoredGuess a b := by
        simp [Step, successors, next, rewindStoredGuess, start, a, b, storedRewindState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h₃ : Step rewindStoredGuess b c := by
        simp [Step, successors, next, rewindStoredGuess, start, a, b, c, storedRewindState,
          Instruction.next, Configuration.tape, Tape.moveLeft]
      have h₄ : Step rewindStoredGuess c d := by
        simp [Step, successors, next, rewindStoredGuess, start, a, b, c, d, storedRewindState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h₅ : Step rewindStoredGuess d
          (storedRewindFinish beforeInput beforeOutput boundary [] current inputRight outputRight) := by
        simp [Step, successors, next, rewindStoredGuess, start, a, b, c, d, storedRewindState,
          storedRewindFinish, Instruction.next, Tape.moveLeft, Tape.moveRight]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) h₁) h₂) h₃) h₄) h₅
  | cons bit rest ih =>
      let start := storedRewindState beforeInput beforeOutput boundary (bit :: rest) current inputRight outputRight
      let a : Configuration := { start with pc := 1, inputTape := start.inputTape.moveLeft }
      let b : Configuration := { a with pc := 2, outputTape := a.outputTape.moveLeft }
      let c : Configuration := { b with pc := 3 }
      let d : Configuration := { c with pc := 4, outputTape := c.outputTape.write none }
      have h₁ : Step rewindStoredGuess start a := by
        simp [Step, successors, next, rewindStoredGuess, start, a, storedRewindState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h₂ : Step rewindStoredGuess a b := by
        simp [Step, successors, next, rewindStoredGuess, start, a, b, storedRewindState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h₃ : Step rewindStoredGuess b c := by
        cases bit <;> simp [Step, successors, next, rewindStoredGuess, start, a, b, c,
          storedRewindState, Instruction.next, Configuration.tape, Tape.moveLeft]
      have h₄ : Step rewindStoredGuess c d := by
        simp [Step, successors, next, rewindStoredGuess, start, a, b, c, d, storedRewindState,
          Instruction.next, Configuration.updateTape, Configuration.advance]
      have h₅ : Step rewindStoredGuess d
          (storedRewindState beforeInput beforeOutput boundary rest (some bit)
            (current :: inputRight) (none :: outputRight)) := by
        simp [Step, successors, next, rewindStoredGuess, start, a, b, c, d, storedRewindState,
          Instruction.next, Tape.moveLeft, Tape.write]
      have hFinish : storedRewindFinish beforeInput beforeOutput boundary rest (some bit)
          (current :: inputRight) (none :: outputRight) =
          storedRewindFinish beforeInput beforeOutput boundary (bit :: rest) current inputRight outputRight := by
        simp only [storedRewindFinish, List.reverse_cons, List.map_append, List.map_cons,
          List.map_nil, List.length_cons, List.append_assoc, List.cons_append, List.nil_append,
          List.replicate_succ']
      have run := (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) h₁) h₂) h₃) h₄) h₅).trans
          (ih (some bit) (current :: inputRight) (none :: outputRight))
      rw [hFinish] at run
      convert run using 1
      simp [List.length_cons]
      omega

def rewindStoredGuessStart (beforeInput beforeOutput : List (Option Bool))
    (boundary : Option Bool) (bits : List Bool) (inputBlanks outputBlanks : Nat) : Configuration :=
  storedRewindState beforeInput beforeOutput boundary bits.reverse none
    (List.replicate inputBlanks none) (List.replicate outputBlanks none)

def rewindStoredGuessFinish (beforeInput beforeOutput : List (Option Bool))
    (boundary : Option Bool) (bits : List Bool) (inputBlanks outputBlanks : Nat) : Configuration :=
  storedRewindFinish beforeInput beforeOutput boundary bits.reverse none
    (List.replicate inputBlanks none) (List.replicate outputBlanks none)

theorem rewindStoredGuess_runs (beforeInput beforeOutput : List (Option Bool))
    (boundary : Option Bool) (bits : List Bool) (inputBlanks outputBlanks : Nat) :
    RunsFor rewindStoredGuess (rewindStoredGuessStart beforeInput beforeOutput boundary bits inputBlanks outputBlanks)
      (rewindStoredGuessFinish beforeInput beforeOutput boundary bits inputBlanks outputBlanks)
      (5 * bits.length + 5) := by
  simpa [rewindStoredGuessStart, rewindStoredGuessFinish] using
    storedRewind_run beforeInput beforeOutput boundary bits.reverse none
      (List.replicate inputBlanks none) (List.replicate outputBlanks none)

theorem rewindStoredGuess_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ rewindStoredGuess := by simp [rewindStoredGuess]

theorem rewindStoredGuess_eval (beforeInput beforeOutput : List (Option Bool))
    (boundary : Option Bool) (bits : List Bool) (inputBlanks outputBlanks : Nat) :
    evalConfigWithin rewindStoredGuess
      (rewindStoredGuessStart beforeInput beforeOutput boundary bits inputBlanks outputBlanks)
      (5 * bits.length + 5) =
      PMF.pure (rewindStoredGuessFinish beforeInput beforeOutput boundary bits inputBlanks outputBlanks) :=
  (rewindStoredGuess_runs beforeInput beforeOutput boundary bits inputBlanks outputBlanks).evalConfigWithin_eq_pure_of_no_randomBit
    rewindStoredGuess_no_randomBit

theorem rewindStoredGuess_control_closed (c d : Configuration)
    (hPc : c.pc < rewindStoredGuess.length) (step : Step rewindStoredGuess c d)
    (_hRunning : d.halted = false) : d.pc < rewindStoredGuess.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 7 at hPc
  change d.pc < 7
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, rewindStoredGuess,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- The starting state is exactly a guarded call's physical raw result on
opposite tapes, including the possibly nonblank input boundary. No reply
bits are reloaded and no caller cells are removed. -/
theorem rawResultFrom_rewindStoredGuessStart (source : Program) (request : List Bool)
    (beforeVirtual beforeInput : List (Option Bool)) (boundary : Option Bool) (c : Configuration) :
    ((GuardedCompiler.rawResultFrom source request beforeVirtual (boundary :: beforeInput) c).swapTapes).resumeAt 0 =
      rewindStoredGuessStart beforeInput
        ((GuardedCompiler.encodedRightBits c.inputTape).reverse.map some ++
          (GuardedCompiler.encodeTape (request.reverse.map some ++ beforeVirtual) c.inputTape).left)
        boundary c.outputBits (2 * c.outputTape.cells + 2 - c.outputBits.length)
          0 := by
  simp only [GuardedCompiler.rawResultFrom, GuardedCompiler.extractOutputFinish,
    GuardedCompiler.copyScratchFinish, GuardedCompiler.scratchPrefix, Configuration.swapTapes,
    Configuration.resumeAt, rewindStoredGuessStart, storedRewindState,
    List.replicate_zero, List.cons_append, Configuration.outputBits]

/-- Rewind the raw reply, erase its parallel copy, then erase the fixed
number of blocks between that copy and the saved challenge. -/
def prepareStoredGuess (count : Nat) : Program :=
  let pre := rewindStoredGuess.asSubroutine 0 8
  let eraser := eraseOutputBlocks count
  Program.withSubroutine pre eraser [.halt] (pre.length + eraser.length + 1)

def prepareStoredGuessStart (beforeInput : List (Option Bool)) (boundary : Option Bool)
    (front back : List (List Bool)) (challenge : Bool) (bits : List Bool)
    (inputBlanks outputBlanks : Nat) : Configuration :=
  rewindStoredGuessStart beforeInput (savedOutputBlocks front ++ some challenge :: savedOutputBlocks back)
    boundary bits inputBlanks outputBlanks

def prepareStoredGuessSteps (front : List (List Bool)) (bits : List Bool) : Nat :=
  (5 * bits.length + 5) + (eraseOutputBlocksSteps front + 1)

def prepareStoredGuessFinish (beforeInput : List (Option Bool)) (boundary : Option Bool)
    (front back : List (List Bool)) (challenge : Bool) (bits : List Bool)
    (inputBlanks outputBlanks : Nat) : Configuration :=
  let rewound := rewindStoredGuessFinish beforeInput
    (savedOutputBlocks front ++ some challenge :: savedOutputBlocks back) boundary bits inputBlanks outputBlanks
  { eraseOutputBlocksFinish rewound.inputTape (some challenge :: savedOutputBlocks back) front
      rewound.outputTape.right with pc := 8 + (eraseOutputBlocks front.length).length + 1 }

theorem prepareStoredGuess_eval (beforeInput : List (Option Bool)) (boundary : Option Bool)
    (front back : List (List Bool)) (challenge : Bool) (bits : List Bool)
    (inputBlanks outputBlanks : Nat) :
    evalConfigWithin (prepareStoredGuess front.length)
      (prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks)
      (prepareStoredGuessSteps front bits) =
      PMF.pure (prepareStoredGuessFinish beforeInput boundary front back challenge bits inputBlanks outputBlanks) := by
  let pre := rewindStoredGuess.asSubroutine 0 8
  let eraser := eraseOutputBlocks front.length
  let finalPc := 8 + eraser.length + 1
  let saved := savedOutputBlocks front ++ some challenge :: savedOutputBlocks back
  let rewound := rewindStoredGuessFinish beforeInput saved boundary bits inputBlanks outputBlanks
  let middle := eraseOutputBlocksStart rewound.inputTape (some challenge :: savedOutputBlocks back) front rewound.outputTape.right
  have hPre : pre.length = 8 := rfl
  have first := (rewindStoredGuess_runs beforeInput saved boundary bits inputBlanks outputBlanks).evalConfigWithin_withSubroutine_halted_of_closed
    [] rewindStoredGuess (eraser.asSubroutine 8 finalPc ++ [.halt]) 8
    (by change 0 < 7; decide) rfl rfl rewindStoredGuess_control_closed rewindStoredGuess_no_randomBit
  have hProgram : Program.withSubroutine [] rewindStoredGuess
      (eraser.asSubroutine 8 finalPc ++ [.halt]) 8 = prepareStoredGuess front.length := by
    simp only [Program.withSubroutine, prepareStoredGuess, hPre, List.length_nil,
      List.nil_append, pre, eraser, finalPc, List.append_assoc]
  rw [hProgram] at first
  have hStart : (rewindStoredGuessStart beforeInput saved boundary bits inputBlanks outputBlanks).rebasePc 0 =
      prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks := by
    simp [rewindStoredGuessStart, storedRewindState, Configuration.rebasePc, prepareStoredGuessStart, saved]
  have hMiddle : rewound.resumeAt 8 = middle.rebasePc pre.length := by
    simp [rewound, rewindStoredGuessFinish, storedRewindFinish, middle, eraseOutputBlocksStart,
      saved, hPre, Configuration.resumeAt, Configuration.rebasePc]
  simp only [List.length_nil] at first
  rw [hStart] at first
  change evalConfigWithin (prepareStoredGuess front.length)
    (prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks)
    (5 * bits.length + 5) = PMF.pure (rewound.resumeAt 8) at first
  rw [hMiddle] at first
  have last := Program.evalConfigWithin_withSubroutine_final_halt pre eraser middle
    (by change 0 ≤ eraser.length; omega) rfl (eraseOutputBlocksSteps front)
    (eraseOutputBlocks_haltsFrom rewound.inputTape (some challenge :: savedOutputBlocks back) front rewound.outputTape.right)
  have hLastProgram : Program.withSubroutine pre eraser [.halt] (pre.length + eraser.length + 1) =
      prepareStoredGuess front.length := rfl
  dsimp only at last
  rw [hLastProgram] at last
  dsimp only [eraser, middle] at last
  rw [eraseOutputBlocks_eval] at last
  have hLast : evalConfigWithin (prepareStoredGuess front.length) (middle.rebasePc pre.length)
      (eraseOutputBlocksSteps front + 1) =
      PMF.pure (prepareStoredGuessFinish beforeInput boundary front back challenge bits inputBlanks outputBlanks) := by
    simpa only [PMF.pure_map, prepareStoredGuessFinish, hPre, rewound, saved, eraser,
      middle, eraseOutputBlocksFinish] using last
  rw [prepareStoredGuessSteps, evalConfigWithin_add, first, PMF.pure_bind, hLast]

private theorem blank_getD (count i : Nat) :
    (List.replicate count (none : Option Bool)).getD i none = none := by
  induction count generalizing i with
  | zero => simp
  | succ count ih => cases i with
    | zero => simp [List.replicate_succ]
    | succ i => simpa only [List.replicate_succ, List.getD_cons_succ] using ih i

private theorem append_blanks_getD (cells : List (Option Bool)) (blanks i : Nat) :
    (cells ++ none :: List.replicate blanks none).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i with
    | zero => rfl
    | succ i => simpa only [List.nil_append, List.getD_cons_succ, List.getD_nil] using blank_getD blanks i
  | cons cell rest ih => cases i with
    | zero => rfl
    | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

/-- Extra blank cells produced by real erasures agree with the parser's
specified cells. This equality of observations performs no tape cleanup. -/
theorem prepareStoredGuessFinish_equivalent (beforeInput : List (Option Bool)) (boundary : Option Bool)
    (front back : List (List Bool)) (challenge : Bool) (bits : List Bool)
    (inputBlanks outputBlanks : Nat) :
    ((prepareStoredGuessFinish beforeInput boundary front back challenge bits inputBlanks outputBlanks).resumeAt 0).Equivalent
      (finishStoredTaggedGuessStart (boundary :: beforeInput) back challenge bits) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · cases bits with
    | nil =>
        refine ⟨rfl, fun _ => rfl, ?_⟩
        intro i
        exact blank_getD inputBlanks i
    | cons bit rest =>
        refine ⟨?_, ?_, ?_⟩
        · simp [prepareStoredGuessFinish, eraseOutputBlocksFinish, rewindStoredGuessFinish,
            storedRewindFinish, finishStoredTaggedGuessStart, finishTaggedGuessStart,
            readTaggedGuessStart, Tape.ofBits, Tape.moveRight, Configuration.resumeAt]
        · intro i
          simp [prepareStoredGuessFinish, eraseOutputBlocksFinish, rewindStoredGuessFinish,
            storedRewindFinish, finishStoredTaggedGuessStart, finishTaggedGuessStart,
            readTaggedGuessStart, Tape.ofBits, Tape.moveRight, Configuration.resumeAt]
        intro i
        simpa [prepareStoredGuessFinish, eraseOutputBlocksFinish, rewindStoredGuessFinish,
          storedRewindFinish, finishStoredTaggedGuessStart, finishTaggedGuessStart,
          readTaggedGuessStart, Tape.ofBits, Tape.moveRight, Configuration.resumeAt] using append_blanks_getD (rest.map some) inputBlanks i
  · refine ⟨rfl, fun _ => rfl, ?_⟩
    intro i
    simp only [prepareStoredGuessFinish, eraseOutputBlocksFinish, rewindStoredGuessFinish,
      storedRewindFinish, List.length_reverse, Configuration.resumeAt]
    rw [← List.append_assoc, List.replicate_append_replicate, List.replicate_append_replicate]
    exact blank_getD _ i

theorem prepareStoredGuess_haltsFrom (beforeInput : List (Option Bool)) (boundary : Option Bool)
    (front back : List (List Bool)) (challenge : Bool) (bits : List Bool)
    (inputBlanks outputBlanks : Nat) :
    ∀ c, PaddedRunsFor (prepareStoredGuess front.length)
      (prepareStoredGuessStart beforeInput boundary front back challenge bits inputBlanks outputBlanks) c
      (prepareStoredGuessSteps front bits) → c.halted = true := by
  intro c run
  have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [prepareStoredGuess_eval] at hc
  have heq : c = prepareStoredGuessFinish beforeInput boundary front back challenge bits inputBlanks outputBlanks := by
    simpa using hc
  rw [heq]; rfl

theorem prepareStoredGuess_length (count : Nat) : (prepareStoredGuess count).length = 8 * count + 11 := by
  simp [prepareStoredGuess, Program.withSubroutine, Program.asSubroutine_length,
    rewindStoredGuess, eraseOutputBlocks_length]; omega

end Machine
