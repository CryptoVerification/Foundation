import Foundation.Crypto.Semantics.Machine.GuardedResult
import Foundation.Crypto.Semantics.Machine.BitstringErasure
import Foundation.Crypto.Semantics.Machine.TapeSwap
import Foundation.Crypto.Semantics.Machine.StoredGuessFinalization

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

private theorem rewindStoredGuess_blank_stop (input output : Tape)
    (hBlank : output.moveLeft.current = none) :
    RunsFor rewindStoredGuess ({ inputTape := input, outputTape := output } : Configuration)
      { pc := 6, inputTape := input.moveLeft.moveRight, outputTape := output.moveLeft, halted := true } 5 := by
  let start : Configuration := { inputTape := input, outputTape := output }
  let a : Configuration := { start with pc := 1, inputTape := input.moveLeft }
  let b : Configuration := { a with pc := 2, outputTape := output.moveLeft }
  let c : Configuration := { b with pc := 5 }
  let d : Configuration := { c with pc := 6, inputTape := input.moveLeft.moveRight }
  have first : Step rewindStoredGuess start a := by
    simp [Step, successors, next, rewindStoredGuess, start, a, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have second : Step rewindStoredGuess a b := by
    simp [Step, successors, next, rewindStoredGuess, start, a, b, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have third : Step rewindStoredGuess b c := by
    simp [Step, successors, next, rewindStoredGuess, start, a, b, c, Instruction.next,
      Configuration.tape, hBlank]
  have fourth : Step rewindStoredGuess c d := by
    simp [Step, successors, next, rewindStoredGuess, start, a, b, c, d, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have last : Step rewindStoredGuess d
      { pc := 6, inputTape := input.moveLeft.moveRight, outputTape := output.moveLeft, halted := true } := by
    simp [Step, successors, next, rewindStoredGuess, start, a, b, c, d, Instruction.next]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.zero _) first) second) third) fourth) last

private theorem rewindStoredGuess_terminates_left (input : Tape)
    (left : List (Option Bool)) (current : Option Bool) (right : List (Option Bool)) :
    ∃ finish used,
      used ≤ 5 * left.length + 5 ∧
      RunsFor rewindStoredGuess
        ({ inputTape := input, outputTape := { left := left, current := current, right := right } } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.outputTape.left.length ≤ left.length := by
  induction left generalizing input current right with
  | nil =>
      refine ⟨{
        pc := 6, inputTape := input.moveLeft.moveRight,
        outputTape := ({ current := current, right := right } : Tape).moveLeft, halted := true },
        5, by simp, rewindStoredGuess_blank_stop _ _ rfl, rfl, ?_⟩
      simp [Tape.moveLeft]
  | cons cell rest ih =>
      cases cell with
      | none =>
          refine ⟨{
            pc := 6, inputTape := input.moveLeft.moveRight,
            outputTape := ({ left := none :: rest, current := current, right := right } : Tape).moveLeft,
            halted := true }, 5, by simp, rewindStoredGuess_blank_stop _ _ rfl, rfl, ?_⟩
          simp [Tape.moveLeft]
      | some bit =>
          let start : Configuration :=
            { inputTape := input, outputTape := { left := some bit :: rest, current := current, right := right } }
          let a : Configuration := { start with pc := 1, inputTape := input.moveLeft }
          let b : Configuration := { a with pc := 2, outputTape := start.outputTape.moveLeft }
          let c : Configuration := { b with pc := 3 }
          let d : Configuration := { c with pc := 4, outputTape := c.outputTape.write none }
          have first : Step rewindStoredGuess start a := by
            simp [Step, successors, next, rewindStoredGuess, start, a, Instruction.next,
              Configuration.updateTape, Configuration.advance]
          have second : Step rewindStoredGuess a b := by
            simp [Step, successors, next, rewindStoredGuess, start, a, b, Instruction.next,
              Configuration.updateTape, Configuration.advance]
          have third : Step rewindStoredGuess b c := by
            cases bit <;> simp [Step, successors, next, rewindStoredGuess, start, a, b, c,
              Instruction.next, Configuration.tape, Tape.moveLeft]
          have fourth : Step rewindStoredGuess c d := by
            simp [Step, successors, next, rewindStoredGuess, start, a, b, c, d,
              Instruction.next, Configuration.updateTape, Configuration.advance]
          have fifth : Step rewindStoredGuess d
              { inputTape := input.moveLeft, outputTape := { left := rest, right := current :: right } } := by
            simp [Step, successors, next, rewindStoredGuess, start, a, b, c, d,
              Instruction.next, Tape.moveLeft, Tape.write]
          obtain ⟨finish, used, hUsed, run, hHalt, hLeft⟩ := ih input.moveLeft none (current :: right)
          refine ⟨finish, 5 + used, ?_, ?_, hHalt, ?_⟩
          · simp only [List.length_cons]
            omega
          · exact (RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
              (RunsFor.succ (RunsFor.zero _) first) second) third) fourth) fifth).trans run
          · simp only [List.length_cons]
            omega

/-- The paired rewind stops even when the parallel copy or saved separators
are malformed. Its controlling output head moves left on each iteration;
the finite represented prefix bounds all actual native transitions. -/
theorem rewindStoredGuess_terminates_from_anyTape (input output : Tape) :
    ∃ finish used,
      used ≤ 5 * output.left.length + 5 ∧
      RunsFor rewindStoredGuess ({ inputTape := input, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.outputTape.left.length ≤ output.left.length :=
  rewindStoredGuess_terminates_left input output.left output.current output.right

/-- Paired rewind followed by the fixed number of front-block erasures,
on the very tapes returned by the rewind. Missing/malformed blocks impose
no validity premise on this stopping and storage-layout certificate. -/
theorem prepareStoredGuess_terminates_from_anyTape (count : Nat) (input output : Tape) :
    ∃ finish used,
      used ≤ (count + 1) * 100 * (output.cells + 1) ∧
      RunsFor (prepareStoredGuess count) ({ inputTape := input, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.outputTape.left.length ≤ output.left.length := by
  obtain ⟨rewound, rewindTime, hRewindTime, rewindRun, rewindHalt, rewindLeft⟩ :=
    rewindStoredGuess_terminates_from_anyTape input output
  obtain ⟨erased, eraseTime, hEraseTime, eraseRun, eraseHalt, _eraseInput, eraseLeft⟩ :=
    eraseOutputBlocks_terminates_from_anyTape count rewound.inputTape rewound.outputTape
  let pre := rewindStoredGuess.asSubroutine 0 8
  let eraser := eraseOutputBlocks count
  let finalPc := 8 + eraser.length + 1
  obtain ⟨rewindUsed, hRewindUsed, first⟩ := rewindRun.withSubroutine_halted
    [] rewindStoredGuess (eraser.asSubroutine 8 finalPc ++ [.halt]) 8 (Nat.zero_le _) rfl rewindHalt
  have firstProgram : Program.withSubroutine [] rewindStoredGuess
      (eraser.asSubroutine 8 finalPc ++ [.halt]) 8 = prepareStoredGuess count := by
    simp only [prepareStoredGuess, Program.withSubroutine, List.length_nil, List.nil_append,
      eraser, finalPc, show (rewindStoredGuess.asSubroutine 0 8).length = 8 from rfl, List.append_assoc]
  rw [firstProgram] at first
  change RunsFor (prepareStoredGuess count)
    ({ inputTape := input, outputTape := output } : Configuration) (rewound.resumeAt 8) rewindUsed at first
  obtain ⟨eraseUsed, hEraseUsed, second⟩ := eraseRun.withSubroutine_halted
    pre eraser [.halt] finalPc (Nat.zero_le _) rfl eraseHalt
  change RunsFor (prepareStoredGuess count) (rewound.resumeAt 8) (erased.resumeAt finalPc) eraseUsed at second
  let finish : Configuration := { erased with pc := finalPc, halted := true }
  have last : Step (prepareStoredGuess count) (erased.resumeAt finalPc) finish := by
    have code : (prepareStoredGuess count)[finalPc]? = some .halt := by
      change (Program.withSubroutine pre eraser [.halt] finalPc)[finalPc]? = some .halt
      have h := Program.withSubroutine_getElem?_suffix pre eraser [.halt] finalPc 0
      simpa only [show pre.length = 8 from rfl, Nat.add_zero, List.getElem?_cons_zero, finalPc] using h
    simp [Step, successors, next, Configuration.resumeAt, finish, code, Instruction.next]
  refine ⟨finish, rewindUsed + eraseUsed + 1, ?_, RunsFor.succ (first.trans second) last,
    rfl, eraseLeft.trans rewindLeft⟩
  have hEraseBound := hEraseTime.trans
    (Nat.mul_le_mul_left (count + 1) (Nat.add_le_add_right (Nat.mul_le_mul_left 4 rewindLeft) 5))
  have hCells : output.left.length ≤ output.cells := by simp [Tape.cells]; omega
  nlinarith

theorem prepareStoredGuess_no_randomBit (count : Nat) (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareStoredGuess count := by
  simp [prepareStoredGuess, Program.withSubroutine, Program.asSubroutine, Instruction.asSubroutine,
    rewindStoredGuess]
  intro instruction hMem hEq
  cases instruction <;> simp_all [eraseOutputBlocks_no_randomBit]

end Machine
