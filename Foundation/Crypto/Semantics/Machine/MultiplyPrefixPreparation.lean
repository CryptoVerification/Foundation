import Foundation.Crypto.Semantics.Machine.SelectedInputRestoration
import Foundation.Crypto.Semantics.Machine.ContextualPrefix
import Foundation.Crypto.Semantics.Machine.StoredInputScratch

namespace Machine

/-- Begin assembling the certified multiplication input from stored cells.
Restore the DDH input, reserve a blank after the selected message, and copy
its public parameter/instance prefix into the new argument region. The
message and native challenge stay saved. This stage does not yet frame the
two element operands or invoke the multiplication certificate. -/
def prepareMultiplyPrefix : Program :=
  restoreStoredInput.asSubroutine 0 19 ++ [.moveRight .output] ++
    preparePublicPrefixContext.asSubroutine 20 63 ++ [.halt]

def prepareMultiplyPrefixStart (beforeInput beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply consumed selected : List Bool)
    (current : Option Bool) (right : List (Option Bool)) : Configuration :=
  restoreStoredInputStart beforeInput
    (encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail) reply consumed current right
    { left := selected.reverse.map some ++ beforeOutput, right := [none] }

def prepareMultiplyPrefixFinish (beforeInput beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply consumed selected : List Bool)
    (current : Option Bool) (right : List (Option Bool)) : Configuration :=
  { preparePublicPrefixContextFinish beforeInput (none :: selected.reverse.map some ++ beforeOutput)
      n instanceBits (tupleTail.map some ++ none :: reply.map some ++ none :: consumed.map some ++ current :: right)
      with pc := 63 }

def prepareMultiplyPrefixSteps (n : Nat) (instanceBits tupleTail reply consumed : List Bool) : Nat :=
  restoreStoredInputSteps (encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail) reply consumed + 1 +
    preparePublicPrefixContextSteps n instanceBits + 1

/-- Full native trace: retained DDH cells are reached by charged rewinds and
then copied by the existing contextual prefix routine. Every saved tape cell
and the fresh argument region occur in the complete resulting configuration. -/
theorem prepareMultiplyPrefix_runs (beforeInput beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply consumed selected : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    RunsFor prepareMultiplyPrefix
      (prepareMultiplyPrefixStart beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right)
      (prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right)
      (prepareMultiplyPrefixSteps n instanceBits tupleTail reply consumed) := by
  let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail
  let output : Tape := { left := selected.reverse.map some ++ beforeOutput, right := [none] }
  let restored := restoreStoredInputFinish beforeInput original reply consumed current right output
  let tail := tupleTail.map some ++ none :: reply.map some ++ none :: consumed.map some ++ current :: right
  let prefixStart := preparePublicPrefixContextStart beforeInput
    (none :: selected.reverse.map some ++ beforeOutput) n instanceBits tail
  have hRestore := (restoreStoredInput_runs beforeInput original reply consumed current right output).withSubroutine_halted_of_closed
    [] restoreStoredInput ([.moveRight .output] ++ preparePublicPrefixContext.asSubroutine 20 63 ++ [.halt]) 19
    (by change 0 < 18; decide) rfl rfl restoreStoredInput_control_closed
  change RunsFor prepareMultiplyPrefix
    (prepareMultiplyPrefixStart beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right)
    (restored.resumeAt 19) (restoreStoredInputSteps original reply consumed) at hRestore
  have hMove : Step prepareMultiplyPrefix (restored.resumeAt 19) (prefixStart.rebasePc 20) := by
    cases n <;> simp [Step, successors, next, prepareMultiplyPrefix, restoreStoredInput,
      rewindBitstring, Program.asSubroutine, Instruction.asSubroutine,
      restored, restoreStoredInputFinish, prefixStart, preparePublicPrefixContextStart,
      skipUnaryCellsStart_layout, Configuration.resumeAt, Configuration.rebasePc,
      Instruction.next, Configuration.updateTape, Configuration.advance,
      output, original, tail, encodeSecurityParameter, List.map_append, List.map_replicate,
      List.append_assoc, List.replicate_succ, Tape.moveRight]
  have hPrefix := (preparePublicPrefixContext_runs beforeInput
      (none :: selected.reverse.map some ++ beforeOutput) n instanceBits tail).withSubroutine_halted_of_closed
    (restoreStoredInput.asSubroutine 0 19 ++ [.moveRight .output]) preparePublicPrefixContext [.halt] 63
    (by change 0 < 42; decide) rfl rfl
    preparePublicPrefixContext_control_closed
  change RunsFor prepareMultiplyPrefix (prefixStart.rebasePc 20)
    ((prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right).resumeAt 63)
    (preparePublicPrefixContextSteps n instanceBits) at hPrefix
  have hHalt : Step prepareMultiplyPrefix
      ((prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right).resumeAt 63)
      (prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right) := by
    simp [Step, successors, next, prepareMultiplyPrefix, restoreStoredInput, preparePublicPrefixContext,
      rewindBitstring, skipUnary, skipFrame, savePublicPrefix, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, prepareMultiplyPrefixFinish,
      preparePublicPrefixContextFinish, savePublicPrefixContextFinish, Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ ((RunsFor.succ hRestore hMove).trans hPrefix) hHalt

theorem prepareMultiplyPrefix_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareMultiplyPrefix := by
  simp [prepareMultiplyPrefix, restoreStoredInput, preparePublicPrefixContext, rewindBitstring,
    skipUnary, skipFrame, savePublicPrefix, copyBitstring,
    Program.asSubroutine, Instruction.asSubroutine]

theorem prepareMultiplyPrefix_eval (beforeInput beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply consumed selected : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    evalConfigWithin prepareMultiplyPrefix
      (prepareMultiplyPrefixStart beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right)
      (prepareMultiplyPrefixSteps n instanceBits tupleTail reply consumed) =
      PMF.pure (prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right) :=
  (prepareMultiplyPrefix_runs beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right).evalConfigWithin_eq_pure_of_no_randomBit
    prepareMultiplyPrefix_no_randomBit


/-- The new arithmetic argument region contains the public prefix, while
its two reserved blanks separate it from the saved selected element code.
No bit of the stored native challenge or earlier caller scratch is erased. -/
theorem prepareMultiplyPrefixFinish_output (beforeInput beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply consumed selected : List Bool)
    (current : Option Bool) (right : List (Option Bool)) :
    (prepareMultiplyPrefixFinish beforeInput beforeOutput n instanceBits tupleTail reply consumed selected current right).outputTape =
      { left := (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++
          none :: none :: selected.reverse.map some ++ beforeOutput } := by
  simp only [prepareMultiplyPrefixFinish]
  rw [preparePublicPrefixContextFinish_layout]
  simp [List.append_assoc]

/-- Restoring and copying public input costs linearly many native steps in
all retained input blocks. This bound makes no assumption about monotonicity
of a later group-operation budget. -/
theorem prepareMultiplyPrefix_steps_le (n : Nat) (instanceBits tupleTail reply consumed : List Bool) :
    prepareMultiplyPrefixSteps n instanceBits tupleTail reply consumed ≤
      22 * ((encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail).length +
        reply.length + consumed.length + 1) + 30 := by
  have hPrefix := preparePublicPrefixContextSteps_le n instanceBits
  have hLength : (encodeSecurityParameter n ++ frame instanceBits).length ≤
      (encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail).length := by
    simp
  simp only [prepareMultiplyPrefixSteps, restoreStoredInputSteps]
  omega

/-- The actual selected-message return is the caller input for this native
arithmetic-prefix stage. The selected message code is neither re-decoded nor
loaded onto another tape; it remains in its original copied cells. -/
theorem selectedMessage_multiplyPrefix_layout (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply first second state : List Bool) (blanks : Nat) (bit : Bool) :
    let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail
    let saved := reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
    let returned := prepareSelectedMessageFinish saved beforeOutput first second state blanks bit
    returned.resumeAt 0 = prepareMultiplyPrefixStart before (none :: some bit :: beforeOutput)
      n instanceBits tupleTail reply (selectedMessageConsumed first second bit) (if bit then second else first)
      returned.inputTape.current returned.inputTape.right := by
  dsimp only
  rw [prepareSelectedMessageFinish_restore_layout]
  simp only [prepareMultiplyPrefixStart, prepareSelectedMessageFinish_output]

/-- Restore and copy the public prefix without assuming valid DDH input or
a canonical choose response. The caller supplies only a fresh output
frontier. Native restoration may reach an unintended malformed block, but
the contextual parser still stops and produces a fresh request frontier. -/
theorem prepareMultiplyPrefix_terminates_with_input_output_layout (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat) :
    ∃ (finish : Configuration) (used : Nat) (after : List (Option Bool))
      (remaining : Nat) (first second third : List Bool),
      used ≤ 200000 * (input.cells +
        ({ left := savedOutput, right := List.replicate blanks none } : Tape).cells) + 200000 ∧
      RunsFor prepareMultiplyPrefix
        ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } ∧
      finish.inputTape.current = some true ∧
      first.length + second.length + third.length ≤ input.cells +
        ({ left := savedOutput, right := List.replicate blanks none } : Tape).cells + used ∧
      ∃ count, finish.inputTape.right =
        (first.map some ++ none :: second.map some ++ none :: third.map some ++
          input.current :: input.right).tail.drop count := by
  let output : Tape := { left := savedOutput, right := List.replicate blanks none }
  obtain ⟨restored, restoreTime, first, second, third, _restoreBefore,
    hRestoreTime, restoreRun, restoreHalt, restoreOutput, restoreInput⟩ :=
    restoreStoredInput_terminates_with_block_layout input output
  obtain ⟨copied, copyTime, _savedInput, after, remaining, hCopyTime, copyRun,
    copyHalt, hInput, _hLeft, copyOutput, hSuffix⟩ :=
    preparePublicPrefixContext_terminates_with_suffix_layout restored.inputTape
      (none :: savedOutput) (blanks - 1)
  have hAdvance : output.moveRight =
      { left := none :: savedOutput, right := List.replicate (blanks - 1) none } := by
    cases blanks <;> simp [output, Tape.moveRight, List.replicate_succ]
  have hRestore := restoreRun.withSubroutine_halted_of_closed
    [] restoreStoredInput ([.moveRight .output] ++ preparePublicPrefixContext.asSubroutine 20 63 ++ [.halt]) 19
    (by change 0 < 18; decide) rfl restoreHalt restoreStoredInput_control_closed
  change RunsFor prepareMultiplyPrefix
    ({ inputTape := input, outputTape := output } : Configuration)
    (restored.resumeAt 19) restoreTime at hRestore
  let start : Configuration :=
    { pc := 20, inputTape := restored.inputTape, outputTape := output.moveRight }
  have hMove : Step prepareMultiplyPrefix (restored.resumeAt 19) start := by
    simp [Step, successors, next, prepareMultiplyPrefix, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, start, Configuration.resumeAt,
      restoreOutput, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hCopy := copyRun.withSubroutine_halted_of_closed
    (restoreStoredInput.asSubroutine 0 19 ++ [.moveRight .output]) preparePublicPrefixContext [.halt] 63
    (by change 0 < 42; decide) rfl copyHalt preparePublicPrefixContext_control_closed
  change RunsFor prepareMultiplyPrefix
    ({ pc := 20, inputTape := restored.inputTape,
       outputTape := { left := none :: savedOutput, right := List.replicate (blanks - 1) none } } : Configuration)
    (copied.resumeAt 63) copyTime at hCopy
  rw [← hAdvance] at hCopy
  change RunsFor prepareMultiplyPrefix start (copied.resumeAt 63) copyTime at hCopy
  let finish : Configuration := { copied with pc := 63, halted := true }
  have hStop : Step prepareMultiplyPrefix (copied.resumeAt 63) finish := by
    simp [Step, successors, next, prepareMultiplyPrefix, restoreStoredInput,
      preparePublicPrefixContext, rewindBitstring, skipUnary, skipFrame, savePublicPrefix,
      copyBitstring, Program.asSubroutine, Instruction.asSubroutine,
      Configuration.resumeAt, finish, Instruction.next]
  have hRestoredRight : restored.inputTape.right =
      (first.map some ++ none :: second.map some ++ none :: third.map some ++
        input.current :: input.right).tail := by
    rw [restoreInput]
    cases first <;> simp [Tape.moveRight, List.cons_append]
  have hRestoredLength : first.length + second.length + third.length ≤ restored.inputTape.cells := by
    rw [restoreInput]
    cases first <;> simp [Tape.cells, Tape.moveRight, List.cons_append] <;> omega
  refine ⟨finish, restoreTime + 1 + copyTime + 1, after, remaining, first, second, third, ?_,
    RunsFor.succ ((RunsFor.succ hRestore hMove).trans hCopy) hStop, rfl, copyOutput, hInput, ?_, ?_⟩
  · have hStorage := GuardedCompiler.sourceStorage_le_of_run restoreRun
    have hMoved := Tape.cells_moveRight_le output
    rw [← hAdvance] at hCopyTime
    change restored.inputTape.cells + restored.outputTape.cells ≤ input.cells + output.cells + restoreTime at hStorage
    change copyTime ≤ 1000 * (restored.inputTape.cells + output.moveRight.cells) + 1000 at hCopyTime
    rw [restoreOutput] at hStorage
    change _ ≤ 200000 * (input.cells + output.cells) + 200000
    omega
  · have hStorage := GuardedCompiler.sourceStorage_le_of_run restoreRun
    change restored.inputTape.cells + restored.outputTape.cells ≤ input.cells + output.cells + restoreTime at hStorage
    change _ ≤ input.cells + output.cells + (restoreTime + 1 + copyTime + 1)
    omega
  · obtain ⟨count, hRight⟩ := hSuffix
    exact ⟨count, hRight.trans (congrArg (fun cells => cells.drop count) hRestoredRight)⟩

/-- The public fresh-output statement remains available without exposing
its retained raw input blocks. -/
theorem prepareMultiplyPrefix_terminates_with_output_layout (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 200000 * (input.cells +
        ({ left := savedOutput, right := List.replicate blanks none } : Tape).cells) + 200000 ∧
      RunsFor prepareMultiplyPrefix
        ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, after, remaining, _first, _second, _third,
    hTime, run, hHalt, hOutput, _hCurrent, _hLength, _hSuffix⟩ :=
    prepareMultiplyPrefix_terminates_with_input_output_layout input savedOutput blanks
  exact ⟨finish, used, after, remaining, hTime, run, hHalt, hOutput⟩


private theorem cells_append_blank_getD (cells : List (Option Bool)) (count i : Nat) :
    (cells ++ none :: List.replicate count none).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> simp
  | cons cell rest ih => cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem cells_drop_getD (cells : List (Option Bool)) (count i : Nat) :
    (cells.drop count).getD i none = cells.getD (count + i) none := by
  induction count generalizing cells with
  | zero => simp
  | succ count ih => cases cells with
    | nil => simp
    | cons cell rest => simpa only [List.drop_succ_cons, Nat.succ_add, List.getD_cons_succ] using ih rest

private theorem three_blocks_drop_layout (first second third : List Bool) (blanks count : Nat) :
    ∃ (a b c : List Bool), a.length + b.length + c.length ≤ first.length + second.length + third.length ∧
      ∀ i, ((first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: List.replicate blanks none).drop count).getD i none =
        (a.map some ++ none :: b.map some ++ none :: c.map some ++ [none]).getD i none := by
  induction count generalizing first second third with
  | zero =>
      refine ⟨first, second, third, Nat.le_refl _, ?_⟩
      intro i
      rw [List.drop_zero]
      have hLeft := cells_append_blank_getD (first.map some ++ none :: second.map some ++ none :: third.map some) blanks i
      have hRight := cells_append_blank_getD (first.map some ++ none :: second.map some ++ none :: third.map some) 0 i
      simpa only [List.append_assoc, List.cons_append, List.replicate_zero] using hLeft.trans hRight.symm
  | succ count ih =>
      cases first with
      | cons bit rest =>
          obtain ⟨a, b, c, hLength, hCells⟩ := ih rest second third
          refine ⟨a, b, c, ?_, ?_⟩
          · simp only [List.length_cons]
            omega
          · intro i
            simpa only [List.map_cons, List.cons_append, List.drop_succ_cons] using hCells i
      | nil =>
          obtain ⟨a, b, c, hLength, hCells⟩ := ih second third []
          refine ⟨a, b, c, by simpa only [List.length_nil, Nat.zero_add, Nat.add_zero] using hLength, ?_⟩
          intro i
          simp only [List.map_nil, List.nil_append, List.cons_append, List.drop_succ_cons]
          apply Eq.trans _ (hCells i)
          rw [cells_drop_getD, cells_drop_getD]
          have hLeft := cells_append_blank_getD (second.map some ++ none :: third.map some) blanks (count + i)
          have hRight := cells_append_blank_getD (second.map some ++ none :: third.map some) (blanks + 1) (count + i)
          simpa only [List.map_nil, List.nil_append, List.append_assoc, List.cons_append,
            List.replicate_succ] using hLeft.trans hRight.symm

private theorem left_cells_split (cells : List (Option Bool)) :
    ∃ (bits : List Bool) (before : List (Option Bool)),
      cells ++ [none] = bits.map some ++ none :: before := by
  induction cells with
  | nil => exact ⟨[], [], rfl⟩
  | cons cell rest ih =>
      cases cell with
      | none => exact ⟨[], rest ++ [none], rfl⟩
      | some bit =>
          obtain ⟨bits, before, h⟩ := ih
          exact ⟨bit :: bits, before, by simpa only [List.cons_append, List.map_cons] using congrArg (List.cons (some bit)) h⟩



/-- An arbitrary finite raw response ahead of the input head leaves at most
three raw blocks after restoration and contextual prefix parsing. The
comparison fixture adds only redundant outer blanks, never machine writes;
its retained prefix and its size come from the actual charged trace. -/
theorem prepareMultiplyPrefix_terminates_with_retained_frontiers
    (input : Tape) (savedOutput : List (Option Bool)) (outputBlanks : Nat)
    (raw : List Bool) (inputBlanks : Nat)
    (hForward : input.current :: input.right = raw.map some ++ none :: List.replicate inputBlanks none) :
    ∃ (finish : Configuration) (used : Nat) (before : List (Option Bool))
      (originalPrefix original reply canonical : List Bool)
      (after : List (Option Bool)) (remaining : Nat),
      used ≤ 200000 * (input.cells +
        ({ left := savedOutput, right := List.replicate outputBlanks none } : Tape).cells) + 200000 ∧
      RunsFor prepareMultiplyPrefix
        ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate outputBlanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      (finish.resumeAt 0).Equivalent
        (seekStoredInputScratchStart
          (originalPrefix.reverse.map some ++ none :: before) original reply canonical 0
          { left := after, right := List.replicate remaining none }) ∧
      GuardedCompiler.sourceStorage
        (seekStoredInputScratchStart
          (originalPrefix.reverse.map some ++ none :: before) original reply canonical 0
          { left := after, right := List.replicate remaining none }) ≤
        10000000 * (input.cells +
          ({ left := savedOutput, right := List.replicate outputBlanks none } : Tape).cells + 1) := by
  let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
  obtain ⟨finish, used, after, remaining, first, second, third,
    hTime, run, hHalt, hOutput, hCurrent, hLength, count, hRight⟩ :=
    prepareMultiplyPrefix_terminates_with_input_output_layout input savedOutput outputBlanks
  have hRawLength : raw.length ≤ input.cells := by
    have h := congrArg List.length hForward
    simp only [List.length_cons, List.length_append, List.length_map, List.length_replicate] at h
    dsimp only [Tape.cells]
    omega
  have hJoined : finish.inputTape.right =
      (first.map some ++ none :: second.map some ++ none :: (third ++ raw).map some ++
        none :: List.replicate inputBlanks none).drop (count + 1) := by
    rw [hRight, hForward]
    cases first <;> simp [List.map_append, List.append_assoc, List.cons_append]
  obtain ⟨a, b, c, hBlocks, hCells⟩ :=
    three_blocks_drop_layout first second (third ++ raw) inputBlanks (count + 1)
  obtain ⟨prefixBits, before, hLeft⟩ := left_cells_split finish.inputTape.left
  have hLeftLength := congrArg List.length hLeft
  simp only [List.length_append, List.length_cons, List.length_map, List.length_nil] at hLeftLength
  let fixture := seekStoredInputScratchStart
    (prefixBits.map some ++ none :: before) (true :: a) b c 0
    { left := after, right := List.replicate remaining none }
  have hFixture : fixture.inputTape = {
      left := prefixBits.map some ++ none :: before, current := some true,
      right := a.map some ++ none :: b.map some ++ none :: c.map some ++ [none] } := by
    dsimp only [fixture, seekStoredInputScratchStart]
    rw [seekBitstringNextStart_layout]
    simp [Tape.moveRight, List.cons_append]
  have hEquivalent : (finish.resumeAt 0).Equivalent fixture := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · change finish.inputTape.Equivalent fixture.inputTape
      rw [hFixture]
      refine ⟨hCurrent, ?_, ?_⟩
      · intro i
        have h := cells_append_blank_getD finish.inputTape.left 0 i
        simpa only [List.replicate_zero, hLeft] using h.symm
      · intro i
        rw [hJoined]
        exact hCells i
    · change finish.outputTape.Equivalent { left := after, right := List.replicate remaining none }
      rw [hOutput]
      exact Tape.Equivalent.refl _
  have hStorage := GuardedCompiler.sourceStorage_le_of_run run
  change finish.inputTape.cells + finish.outputTape.cells ≤ input.cells + output.cells + used at hStorage
  have hFixtureStorage : GuardedCompiler.sourceStorage fixture ≤
      10000000 * (input.cells + output.cells + 1) := by
    change used ≤ 200000 * (input.cells + output.cells) + 200000 at hTime
    change first.length + second.length + third.length ≤ input.cells + output.cells + used at hLength
    simp only [List.length_append] at hBlocks
    rw [hOutput] at hStorage
    dsimp only [GuardedCompiler.sourceStorage, Tape.cells] at hStorage
    dsimp only [GuardedCompiler.sourceStorage]
    rw [hFixture]
    change (prefixBits.map some ++ none :: before).length + 1 +
      (a.map some ++ none :: b.map some ++ none :: c.map some ++ [none]).length +
      ({ left := after, right := List.replicate remaining none } : Tape).cells ≤ _
    simp only [List.length_append, List.length_cons, List.length_map, List.length_nil, Tape.cells, List.length_replicate]
    dsimp only [output] at hTime hLength hStorage ⊢
    simp only [Tape.cells, List.length_replicate] at hTime hLength hRawLength hStorage ⊢
    omega
  refine ⟨finish, used, before, prefixBits.reverse, true :: a, b, c, after, remaining,
    hTime, run, hHalt, ?_, ?_⟩
  · simpa only [List.reverse_reverse] using hEquivalent
  · simpa only [List.reverse_reverse] using hFixtureStorage

end Machine
