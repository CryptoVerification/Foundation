import Foundation.Machine.StoredInputScratch

namespace Machine

/-- Reach scratch beyond all five retained blocks. The first two scans
preserve the DDH input and raw reply; the existing three-block scan preserves
the canonical response, selected message and returned product. -/
def seekGuessInputScratch : Program :=
  GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++
    GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
    seekStoredInputScratch.asSubroutine 12 32 ++ [.halt]

def seekGuessInputScratchStart (before : List (Option Bool))
    (first second third fourth fifth : List Bool) (blanks : Nat) (output : Tape) : Configuration :=
  seekBitstringNextStart before first
    (second.map some ++ none :: third.map some ++ none :: fourth.map some ++ none ::
      fifth.map some ++ none :: List.replicate blanks none) output

def seekGuessInputScratchFinish (before : List (Option Bool))
    (first second third fourth fifth : List Bool) (blanks : Nat) (output : Tape) : Configuration :=
  { seekStoredInputScratchFinish
      (none :: second.reverse.map some ++ none :: first.reverse.map some ++ before)
      third fourth fifth blanks output with pc := 32 }

def seekGuessInputScratchSteps (first second third fourth fifth : List Bool) : Nat :=
  (3*first.length + 3) + (3*second.length + 3) +
    seekStoredInputScratchSteps third fourth fifth + 1

theorem seekGuessInputScratch_runs (before : List (Option Bool))
    (first second third fourth fifth : List Bool) (blanks : Nat) (output : Tape) :
    RunsFor seekGuessInputScratch
      (seekGuessInputScratchStart before first second third fourth fifth blanks output)
      (seekGuessInputScratchFinish before first second third fourth fifth blanks output)
      (seekGuessInputScratchSteps first second third fourth fifth) := by
  let beforeSecond := none :: first.reverse.map some ++ before
  let beforeThird := none :: second.reverse.map some ++ beforeSecond
  let following := third.map some ++ none :: fourth.map some ++ none ::
    fifth.map some ++ none :: List.replicate blanks none
  let afterFirst := seekBitstringNextFinish before first (second.map some ++ none :: following) output
  have hFirst := (seekBitstringNext_runs before first (second.map some ++ none :: following) output).withSubroutine_halted_of_closed
    [] GuardedCompiler.seekScratchInput (GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
      seekStoredInputScratch.asSubroutine 12 32 ++ [.halt]) 6
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  have hFirst' : RunsFor seekGuessInputScratch
      (seekGuessInputScratchStart before first second third fourth fifth blanks output)
      (afterFirst.resumeAt 6) (3*first.length + 3) := by
    simpa [seekGuessInputScratch, seekGuessInputScratchStart, following, afterFirst,
      Program.withSubroutine, Configuration.rebasePc, List.append_assoc] using hFirst
  have hSecondStart : afterFirst.resumeAt 6 =
      (seekBitstringNextStart beforeSecond second following output).rebasePc 6 := by
    cases second <;> simp [afterFirst, seekBitstringNextFinish_layout_cells,
      seekBitstringNextStart_layout, beforeSecond, Configuration.resumeAt,
      Configuration.rebasePc, Tape.moveRight]
  rw [hSecondStart] at hFirst'
  have hSecond := (seekBitstringNext_runs beforeSecond second following output).withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6) GuardedCompiler.seekScratchInput
    (seekStoredInputScratch.asSubroutine 12 32 ++ [.halt]) 12
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  let afterSecond := seekBitstringNextFinish beforeSecond second following output
  change RunsFor seekGuessInputScratch
    ((seekBitstringNextStart beforeSecond second following output).rebasePc 6)
    (afterSecond.resumeAt 12) (3*second.length + 3) at hSecond
  have hThirdStart : afterSecond.resumeAt 12 =
      (seekStoredInputScratchStart beforeThird third fourth fifth blanks output).rebasePc 12 := by
    cases third <;> simp [afterSecond, seekBitstringNextFinish_layout_cells,
      seekStoredInputScratchStart, seekBitstringNextStart_layout, beforeThird, following,
      Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight]
  rw [hThirdStart] at hSecond
  have hThird := (seekStoredInputScratch_runs beforeThird third fourth fifth blanks output).withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++ GuardedCompiler.seekScratchInput.asSubroutine 6 12)
    seekStoredInputScratch [.halt] 32
    (by change 0 < 19; decide) rfl rfl seekStoredInputScratch_control_closed
  change RunsFor seekGuessInputScratch
    ((seekStoredInputScratchStart beforeThird third fourth fifth blanks output).rebasePc 12)
    ((seekStoredInputScratchFinish beforeThird third fourth fifth blanks output).resumeAt 32)
    (seekStoredInputScratchSteps third fourth fifth) at hThird
  have hFinish : (seekStoredInputScratchFinish beforeThird third fourth fifth blanks output).resumeAt 32 =
      (seekGuessInputScratchFinish before first second third fourth fifth blanks output).resumeAt 32 := by
    simp [seekGuessInputScratchFinish, beforeThird, beforeSecond, Configuration.resumeAt,
      List.append_assoc]
  rw [hFinish] at hThird
  have hLength : (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++
      GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
      seekStoredInputScratch.asSubroutine 12 32).length = 32 := by
    simp only [List.length_append, Program.asSubroutine_length,
      show GuardedCompiler.seekScratchInput.length = 5 from rfl,
      show seekStoredInputScratch.length = 19 from rfl]
  have hInstruction : seekGuessInputScratch[32]? = some Instruction.halt := by
    change (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++
      GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
      seekStoredInputScratch.asSubroutine 12 32 ++ [Instruction.halt])[32]? = _
    rw [List.getElem?_append_right (by rw [hLength]), hLength]
    rfl
  have hHalt : Step seekGuessInputScratch
      ((seekGuessInputScratchFinish before first second third fourth fifth blanks output).resumeAt 32)
      (seekGuessInputScratchFinish before first second third fourth fifth blanks output) := by
    simp [Step, successors, next, hInstruction, seekGuessInputScratchFinish,
      seekStoredInputScratchFinish, Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ ((hFirst'.trans hSecond).trans hThird) hHalt

theorem seekGuessInputScratch_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ seekGuessInputScratch := by
  simp [seekGuessInputScratch, seekStoredInputScratch, GuardedCompiler.seekScratchInput,
    Program.asSubroutine, Instruction.asSubroutine]

theorem seekGuessInputScratch_eval (before : List (Option Bool))
    (first second third fourth fifth : List Bool) (blanks : Nat) (output : Tape) :
    evalConfigWithin seekGuessInputScratch
      (seekGuessInputScratchStart before first second third fourth fifth blanks output)
      (seekGuessInputScratchSteps first second third fourth fifth) =
      PMF.pure (seekGuessInputScratchFinish before first second third fourth fifth blanks output) :=
  (seekGuessInputScratch_runs _ _ _ _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit seekGuessInputScratch_no_randomBit

theorem seekGuessInputScratch_steps_eq (first second third fourth fifth : List Bool) :
    seekGuessInputScratchSteps first second third fourth fifth =
      3*(first.length + second.length + third.length + fourth.length + fifth.length) + 17 := by
  rw [seekGuessInputScratchSteps, seekStoredInputScratch_steps_eq]
  omega

set_option maxHeartbeats 1000000 in
theorem seekGuessInputScratch_control_closed (c d : Configuration)
    (hPc : c.pc < seekGuessInputScratch.length) (step : Step seekGuessInputScratch c d)
    (_hRunning : d.halted = false) : d.pc < seekGuessInputScratch.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 33 at hPc
  change d.pc < 33
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, seekGuessInputScratch,
    seekStoredInputScratch, GuardedCompiler.seekScratchInput, Program.asSubroutine,
    Instruction.asSubroutine, subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- The two leading scans and three-block continuation retain the exact
five successive input positions, including malformed internal separators.
`advance` observes the charged native scan and does not load a new tape. -/
theorem seekGuessInputScratch_terminates_with_input_layout (input output : Tape) :
    let advance := fun t : Tape =>
      (Tape.moveRight^[((t.current :: t.right).takeWhile Option.isSome).length + 1]) t
    ∃ finish used, used ≤ 10000 * (input.cells + output.cells) + 10000 ∧
      RunsFor seekGuessInputScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape = advance (advance (advance (advance (advance input)))) := by
  obtain ⟨first, firstTime, hFirstTime, firstRun, firstHalt, firstOutput⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape input output
  obtain ⟨second, secondTime, hSecondTime, secondRun, secondHalt, secondOutput⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape first.inputTape first.outputTape
  obtain ⟨third, thirdTime, hThirdTime, thirdRun, thirdHalt, thirdOutput, thirdInput⟩ :=
    seekStoredInputScratch_terminates_with_input_layout second.inputTape second.outputTape
  have hFirst := firstRun.withSubroutine_halted_of_closed
    [] GuardedCompiler.seekScratchInput
    (GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++ seekStoredInputScratch.asSubroutine 12 32 ++ [.halt]) 6
    (by change 0 < 5; decide) rfl firstHalt GuardedCompiler.seekScratchInput_control_closed
  change RunsFor seekGuessInputScratch
    ({ inputTape := input, outputTape := output } : Configuration) (first.resumeAt 6) firstTime at hFirst
  have hSecond := secondRun.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6) GuardedCompiler.seekScratchInput
    (seekStoredInputScratch.asSubroutine 12 32 ++ [.halt]) 12
    (by change 0 < 5; decide) rfl secondHalt GuardedCompiler.seekScratchInput_control_closed
  change RunsFor seekGuessInputScratch (first.resumeAt 6) (second.resumeAt 12) secondTime at hSecond
  have leading := hFirst.trans hSecond
  have hThird := thirdRun.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++ GuardedCompiler.seekScratchInput.asSubroutine 6 12)
    seekStoredInputScratch [.halt] 32
    (by change 0 < 19; decide) rfl thirdHalt seekStoredInputScratch_control_closed
  change RunsFor seekGuessInputScratch (second.resumeAt 12) (third.resumeAt 32) thirdTime at hThird
  let finish : Configuration := { third with pc := 32, halted := true }
  have last : Step seekGuessInputScratch (third.resumeAt 32) finish := by
    have code : seekGuessInputScratch[32]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, firstTime + secondTime + thirdTime + 1, ?_,
    RunsFor.succ (leading.trans hThird) last, rfl,
    thirdOutput.trans (secondOutput.trans firstOutput), ?_⟩
  · have storageFirst := GuardedCompiler.sourceStorage_le_of_run firstRun
    have storageSecond := GuardedCompiler.sourceStorage_le_of_run leading
    change first.inputTape.cells + first.outputTape.cells ≤ input.cells + output.cells + firstTime at storageFirst
    change second.inputTape.cells + second.outputTape.cells ≤ input.cells + output.cells + (firstTime + secondTime) at storageSecond
    omega
  · have firstInput := (GuardedCompiler.seekScratchInput_halted_input_layout
      input output first firstTime firstRun firstHalt).1
    have secondInput := (GuardedCompiler.seekScratchInput_halted_input_layout
      first.inputTape first.outputTape second secondTime secondRun secondHalt).1
    dsimp only [finish]
    rw [thirdInput, secondInput, firstInput]

/-- The two leading scans and three-block continuation stop on arbitrary
finite input tapes. Malformed separators need not identify the intended
scratch region; this certificate concerns the actual five scans only. -/
theorem seekGuessInputScratch_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 10000 * (input.cells + output.cells) + 10000 ∧
      RunsFor seekGuessInputScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output := by
  obtain ⟨finish, used, hBound, run, hHalted, hOutput, _⟩ :=
    seekGuessInputScratch_terminates_with_input_layout input output
  exact ⟨finish, used, hBound, run, hHalted, hOutput⟩

theorem seekGuessInputScratch_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor seekGuessInputScratch
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (10000 * (input.cells + output.cells) + 10000)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted, _⟩ := seekGuessInputScratch_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted seekGuessInputScratch_no_randomBit hBound finish trace

-- The following local list observations track retained tape cells only.
-- They do not introduce a string operation into the machine instruction set.

private def pastBlank (cells : List (Option Bool)) : List (Option Bool) :=
  (cells.dropWhile Option.isSome).tail

private theorem pastBlank_eq_drop (cells : List (Option Bool)) :
    pastBlank cells = cells.drop ((cells.takeWhile Option.isSome).length + 1) := by
  induction cells with
  | nil => simp [pastBlank]
  | cons cell rest ih =>
      cases cell with
      | none => simp [pastBlank]
      | some bit => simpa [pastBlank, List.takeWhile, Nat.add_assoc] using ih

private theorem pastBlank_drop_suffix (cells : List (Option Bool)) (count : Nat) :
    ∃ shift, pastBlank (cells.drop count) = (pastBlank cells).drop shift := by
  induction count generalizing cells with
  | zero => exact ⟨0, by simp⟩
  | succ count ih =>
      cases cells with
      | nil => exact ⟨0, by simp [pastBlank]⟩
      | cons cell rest =>
          cases cell with
          | none =>
              refine ⟨count + ((rest.drop count).takeWhile Option.isSome).length + 1, ?_⟩
              simp only [List.drop_succ_cons, pastBlank]
              rw [← pastBlank, pastBlank_eq_drop, List.drop_drop]
              simp [Nat.add_assoc]
          | some bit => simpa [pastBlank] using ih rest

private theorem pastBlank_iterate_drop_suffix (cells : List (Option Bool))
    (count scans : Nat) :
    ∃ shift, (pastBlank^[scans]) (cells.drop count) =
      ((pastBlank^[scans]) cells).drop shift := by
  induction scans with
  | zero => exact ⟨count, rfl⟩
  | succ scans ih =>
      obtain ⟨shift, hShift⟩ := ih
      simp only [Function.iterate_succ_apply']
      rw [hShift]
      exact pastBlank_drop_suffix _ shift

private theorem pastBlank_block (bits : List Bool) (tail : List (Option Bool)) :
    pastBlank (bits.map some ++ none :: tail) = tail := by
  induction bits with
  | nil => simp [pastBlank]
  | cons bit bits ih => simpa [pastBlank] using ih

private theorem five_scans_suffix_blank (first second third fourth fifth : List Bool)
    (padding count : Nat) (bit : Bool) :
    let cells := first.map some ++ none :: second.map some ++ none :: third.map some ++
      none :: fourth.map some ++ none :: fifth.map some ++ none :: List.replicate padding none
    ∀ cell ∈ (pastBlank^[5]) (some bit :: cells.drop count), cell = none := by
  let cells := first.map some ++ none :: second.map some ++ none :: third.map some ++
    none :: fourth.map some ++ none :: fifth.map some ++ none :: List.replicate padding none
  have hFirst : pastBlank (some bit :: cells.drop count) = pastBlank (cells.drop count) := by
    simp [pastBlank]
  have hStrip : (pastBlank^[5]) (some bit :: cells.drop count) =
      (pastBlank^[5]) (cells.drop count) := by
    rw [show 5 = 4 + 1 from rfl, Function.iterate_succ_apply, hFirst]
    rfl
  have hAligned : (pastBlank^[5]) cells = List.replicate padding none := by
    dsimp only [cells]
    simp only [List.append_assoc, List.cons_append, Function.iterate_succ_apply, pastBlank_block, Function.iterate_zero_apply]
  obtain ⟨shift, hShift⟩ := pastBlank_iterate_drop_suffix cells count 5
  dsimp only
  rw [hStrip, hShift, hAligned]
  intro cell hCell
  exact List.mem_replicate.mp ((List.drop_sublist _ _).subset hCell) |>.2

private theorem five_scans_blank_head_suffix (first second third fourth : List Bool)
    (padding count : Nat) :
    let cells := first.map some ++ none :: second.map some ++ none :: third.map some ++
      none :: fourth.map some ++ none :: List.replicate padding none
    ∀ cell ∈ (pastBlank^[5]) (none :: cells.drop count), cell = none := by
  let cells := first.map some ++ none :: second.map some ++ none :: third.map some ++
    none :: fourth.map some ++ none :: List.replicate padding none
  have hStrip : (pastBlank^[5]) (none :: cells.drop count) =
      (pastBlank^[4]) (cells.drop count) := by
    rw [show 5 = 4 + 1 from rfl, Function.iterate_succ_apply]
    rfl
  have hAligned : (pastBlank^[4]) cells = List.replicate padding none := by
    dsimp only [cells]
    simp only [List.append_assoc, List.cons_append, Function.iterate_succ_apply,
      pastBlank_block, Function.iterate_zero_apply]
  obtain ⟨shift, hShift⟩ := pastBlank_iterate_drop_suffix cells count 4
  dsimp only
  rw [hStrip, hShift, hAligned]
  intro cell hCell
  exact List.mem_replicate.mp ((List.drop_sublist _ _).subset hCell) |>.2

private def paddedCurrent (cells : List (Option Bool)) : List (Option Bool) :=
  if cells = [] then [none] else cells

private def scanTape (input : Tape) : Tape :=
  (Tape.moveRight^[((input.current :: input.right).takeWhile Option.isSome).length + 1]) input

private theorem pastBlank_paddedCurrent (cells : List (Option Bool)) :
    pastBlank (paddedCurrent cells) = pastBlank cells := by
  by_cases h : cells = [] <;> simp [paddedCurrent, h, pastBlank]

private theorem scanTape_remaining (input : Tape) :
    (scanTape input).current :: (scanTape input).right =
      paddedCurrent (pastBlank (input.current :: input.right)) := by
  have h := GuardedCompiler.seekScratchInput_halted_input_remaining input {}
    ({ pc := 4, inputTape := scanTape input, halted := true } : Configuration)
    (3 * (((input.current :: input.right).takeWhile Option.isSome).length + 1))
    (GuardedCompiler.seekScratchInput_runs_from_anyTape input {}) rfl
  simpa only [paddedCurrent, pastBlank_eq_drop] using h

private theorem scanTape_iterate_remaining (input : Tape) (scans : Nat) (hScans : 0 < scans) :
    ((scanTape^[scans]) input).current :: ((scanTape^[scans]) input).right =
      paddedCurrent ((pastBlank^[scans]) (input.current :: input.right)) := by
  induction scans with
  | zero => omega
  | succ scans ih =>
      cases scans with
      | zero => simpa using scanTape_remaining input
      | succ scans =>
          rw [Function.iterate_succ_apply', scanTape_remaining, ih (by omega),
            pastBlank_paddedCurrent]
          simp only [Function.iterate_succ_apply']

private theorem paddedCurrent_blank (cells : List (Option Bool))
    (h : ∀ cell ∈ cells, cell = none) :
    ∀ cell ∈ paddedCurrent cells, cell = none := by
  by_cases hEmpty : cells = []
  · simp [paddedCurrent, hEmpty]
  · simpa only [paddedCurrent, hEmpty, ↓reduceIte] using h

/-- Convert the blank cells at the observed five-scan position into a
postcondition of the actual bounded native trace. Its final crossed separator
and the caller's saved cells remain represented on the same tape. -/
private theorem seekGuessInputScratch_frontier_of_scanned_cells
    (input output : Tape)
    (hScanned : ∀ cell ∈ ((scanTape^[5]) input).current :: ((scanTape^[5]) input).right,
      cell = none) :
    ∃ finish used after remaining,
      used ≤ 10000 * (input.cells + output.cells) + 10000 ∧
      RunsFor seekGuessInputScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape = { left := none :: after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, hBound, run, hHalted, hOutput, hInput⟩ :=
    seekGuessInputScratch_terminates_with_input_layout input output
  have hCells : ∀ cell ∈ finish.inputTape.current :: finish.inputTape.right, cell = none := by
    rw [hInput]
    change ∀ cell ∈ ((scanTape^[5]) input).current :: ((scanTape^[5]) input).right, cell = none
    exact hScanned
  have hBlank : finish.inputTape.current = none := hCells _ (by simp)
  have hRightBlank : finish.inputTape.right = List.replicate finish.inputTape.right.length none :=
    List.eq_replicate_of_mem (fun cell h => hCells cell (List.mem_cons_of_mem _ h))
  let lastInput := (scanTape^[4]) input
  have hLastLeft := GuardedCompiler.seekScratchInput_halted_input_left lastInput {}
    ({ pc := 4, inputTape := scanTape lastInput, halted := true } : Configuration)
    (3 * (((lastInput.current :: lastInput.right).takeWhile Option.isSome).length + 1))
    (GuardedCompiler.seekScratchInput_runs_from_anyTape lastInput {}) rfl
  let after := ((lastInput.current :: lastInput.right).takeWhile Option.isSome).reverse ++ lastInput.left
  have hLeft : finish.inputTape.left = none :: after := by
    rw [hInput]
    change (scanTape lastInput).left = none :: after
    simpa only [after, List.cons_append] using hLastLeft
  refine ⟨finish, used, after, finish.inputTape.right.length,
    hBound, run, hHalted, hOutput, ?_⟩
  cases hTape : finish.inputTape with
  | mk left current right =>
      simpa only [hTape, Tape.mk.injEq] using And.intro hLeft (And.intro hBlank hRightBlank)

/-- A bit head and a suffix of five retained blocks reach fresh scratch in
five native scans. The crossed blank remains immediately behind the head;
no cryptographic validity of the stored bitstrings is required. -/
theorem seekGuessInputScratch_terminates_with_separated_frontier
    (input output : Tape) (first second third fourth fifth : List Bool)
    (padding count : Nat) (bit : Bool) (hCurrent : input.current = some bit)
    (hRight : input.right =
      (first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: fifth.map some ++ none ::
          List.replicate padding none).drop count) :
    ∃ finish used after remaining,
      used ≤ 10000 * (input.cells + output.cells) + 10000 ∧
      RunsFor seekGuessInputScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape = { left := none :: after, right := List.replicate remaining none } := by
  apply seekGuessInputScratch_frontier_of_scanned_cells input output
  rw [scanTape_iterate_remaining input 5 (by decide)]
  apply paddedCurrent_blank
  rw [hCurrent, hRight]
  exact five_scans_suffix_blank first second third fourth fifth padding count bit

/-- A blank head before a suffix of four retained blocks uses its first
native scan to cross that blank and its other four scans to reach scratch.
This covers empty or truncated fields without replacing them by a bit head.
The actual saved cells and final separator are retained. -/
theorem seekGuessInputScratch_terminates_with_separated_frontier_of_blank
    (input output : Tape) (first second third fourth : List Bool)
    (padding count : Nat) (hCurrent : input.current = none)
    (hRight : input.right =
      (first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: List.replicate padding none).drop count) :
    ∃ finish used after remaining,
      used ≤ 10000 * (input.cells + output.cells) + 10000 ∧
      RunsFor seekGuessInputScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape = { left := none :: after, right := List.replicate remaining none } := by
  apply seekGuessInputScratch_frontier_of_scanned_cells input output
  rw [scanTape_iterate_remaining input 5 (by decide)]
  apply paddedCurrent_blank
  rw [hCurrent, hRight]
  exact five_scans_blank_head_suffix first second third fourth padding count

/-- The whole remaining input stream, including its current cell, may be
any suffix of the five retained blocks. A fully consumed represented stream
has one virtual blank current cell. Both bit and blank heads are covered
without requiring a successful parse of any block. -/
theorem seekGuessInputScratch_terminates_with_stream_frontier
    (input output : Tape) (first second third fourth fifth : List Bool)
    (padding count : Nat)
    (hStream : input.current :: input.right =
      let remaining :=
        (first.map some ++ none :: second.map some ++ none :: third.map some ++
          none :: fourth.map some ++ none :: fifth.map some ++ none ::
            List.replicate padding none).drop count
      if remaining = [] then [none] else remaining) :
    ∃ finish used after remaining,
      used ≤ 10000 * (input.cells + output.cells) + 10000 ∧
      RunsFor seekGuessInputScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape = { left := none :: after, right := List.replicate remaining none } := by
  let cells := first.map some ++ none :: second.map some ++ none :: third.map some ++
    none :: fourth.map some ++ none :: fifth.map some ++ none :: List.replicate padding none
  change input.current :: input.right = paddedCurrent (cells.drop count) at hStream
  apply seekGuessInputScratch_frontier_of_scanned_cells input output
  rw [scanTape_iterate_remaining input 5 (by decide), hStream]
  apply paddedCurrent_blank
  have hStrip : (pastBlank^[5]) (paddedCurrent (cells.drop count)) =
      (pastBlank^[5]) (cells.drop count) := by
    rw [show 5 = 4 + 1 from rfl, Function.iterate_succ_apply,
      pastBlank_paddedCurrent]
    rfl
  have hAligned : (pastBlank^[5]) cells = List.replicate padding none := by
    dsimp only [cells]
    simp only [List.append_assoc, List.cons_append, Function.iterate_succ_apply,
      pastBlank_block, Function.iterate_zero_apply]
  obtain ⟨shift, hShift⟩ := pastBlank_iterate_drop_suffix cells count 5
  rw [hStrip, hShift, hAligned]
  intro cell hCell
  exact (List.mem_replicate.mp ((List.drop_sublist _ _).subset hCell)).2

/-- The five-scan readiness certificate without exposing the retained
separator to callers that only need the blank current cell and right side. -/
theorem seekGuessInputScratch_terminates_with_suffix_frontier
    (input output : Tape) (first second third fourth fifth : List Bool)
    (padding count : Nat) (bit : Bool) (hCurrent : input.current = some bit)
    (hRight : input.right =
      (first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: fifth.map some ++ none ::
          List.replicate padding none).drop count) :
    ∃ finish used after remaining,
      used ≤ 10000 * (input.cells + output.cells) + 10000 ∧
      RunsFor seekGuessInputScratch
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, after, remaining, hBound, run, hHalted, hOutput, hInput⟩ :=
    seekGuessInputScratch_terminates_with_separated_frontier input output
      first second third fourth fifth padding count bit hCurrent hRight
  exact ⟨finish, used, none :: after, remaining, hBound, run, hHalted, hOutput, hInput⟩

end Machine
