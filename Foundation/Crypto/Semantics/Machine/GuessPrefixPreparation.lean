import Foundation.Crypto.Semantics.Machine.StoredGuessInputRestoration
import Foundation.Crypto.Semantics.Machine.ContextualPrefix

namespace Machine

/-- Append the saved public parameter/instance prefix after the complete
raw guess body. Five retained input blocks are rewound by real instructions;
two blank cells separate the new public prefix from the body. -/
def prepareGuessPrefix : Program :=
  restoreGuessInput.asSubroutine 0 40 ++ [.moveRight .output] ++
    preparePublicPrefixContext.asSubroutine 41 84 ++ [.halt]

def prepareGuessPrefixStart (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected product body : List Bool)
    (padding outputBlanks : Nat) : Configuration :=
  restoreGuessInputStart before
    (encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail)
    reply canonical selected product none (List.replicate padding none)
    { left := body.reverse.map some ++ none :: beforeOutput,
      right := List.replicate outputBlanks none }

def prepareGuessPrefixFinish (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected product body : List Bool)
    (padding : Nat) : Configuration :=
  { preparePublicPrefixContextFinish before
      (none :: body.reverse.map some ++ none :: beforeOutput) n instanceBits
      (tupleTail.map some ++ none :: reply.map some ++ none :: canonical.map some ++
        none :: selected.map some ++ none :: product.map some ++ none :: List.replicate padding none)
    with pc := 84 }

def prepareGuessPrefixSteps (n : Nat) (instanceBits tupleTail reply canonical selected product : List Bool) : Nat :=
  restoreGuessInputSteps (encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail)
    reply canonical selected product + 1 + preparePublicPrefixContextSteps n instanceBits + 1

theorem prepareGuessPrefix_runs (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected product body : List Bool)
    (padding outputBlanks : Nat) (hBlanks : outputBlanks ≤ instanceBits.length + 1) :
    RunsFor prepareGuessPrefix
      (prepareGuessPrefixStart before beforeOutput n instanceBits tupleTail reply canonical selected product body padding outputBlanks)
      (prepareGuessPrefixFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding)
      (prepareGuessPrefixSteps n instanceBits tupleTail reply canonical selected product) := by
  let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail
  let output : Tape := {
    left := body.reverse.map some ++ none :: beforeOutput
    right := List.replicate outputBlanks none }
  let restored := restoreGuessInputFinish before original reply canonical selected product none (List.replicate padding none) output
  let following := tupleTail.map some ++ none :: reply.map some ++ none :: canonical.map some ++
    none :: selected.map some ++ none :: product.map some ++ none :: List.replicate padding none
  let prefixStart := preparePublicPrefixContextPaddedStart before
    (none :: body.reverse.map some ++ none :: beforeOutput) n instanceBits following (outputBlanks - 1)
  have hRestore := (restoreGuessInput_runs before original reply canonical selected product none
    (List.replicate padding none) output).withSubroutine_halted_of_closed
    [] restoreGuessInput ([.moveRight .output] ++ preparePublicPrefixContext.asSubroutine 41 84 ++ [.halt]) 40
    (by change 0 < 39; decide) rfl rfl restoreGuessInput_control_closed
  change RunsFor prepareGuessPrefix
    (prepareGuessPrefixStart before beforeOutput n instanceBits tupleTail reply canonical selected product body padding outputBlanks)
    (restored.resumeAt 40) (restoreGuessInputSteps original reply canonical selected product) at hRestore
  have hMove : Step prepareGuessPrefix (restored.resumeAt 40) (prefixStart.rebasePc 41) := by
    cases n <;> cases outputBlanks <;>
      simp [Step, successors, next, prepareGuessPrefix, restoreGuessInput, restoreStoredInput,
        rewindBitstring, Program.asSubroutine, Instruction.asSubroutine, restored,
        restoreGuessInputFinish, prefixStart, preparePublicPrefixContextPaddedStart,
        skipUnaryCellsStart_layout, Configuration.resumeAt, Configuration.rebasePc,
        Instruction.next, Configuration.updateTape, Configuration.advance, output,
        original, following, encodeSecurityParameter, List.map_append, List.map_replicate,
        List.append_assoc, List.replicate_succ, Tape.moveRight]
  have hPrefix := (preparePublicPrefixContextPadded_runs before
      (none :: body.reverse.map some ++ none :: beforeOutput) n instanceBits following
      (outputBlanks - 1) (by omega)).withSubroutine_halted_of_closed
    (restoreGuessInput.asSubroutine 0 40 ++ [.moveRight .output]) preparePublicPrefixContext [.halt] 84
    (by change 0 < 42; decide) rfl rfl preparePublicPrefixContext_control_closed
  change RunsFor prepareGuessPrefix (prefixStart.rebasePc 41)
    ((prepareGuessPrefixFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding).resumeAt 84)
    (preparePublicPrefixContextSteps n instanceBits) at hPrefix
  have hLength : (restoreGuessInput.asSubroutine 0 40 ++ [Instruction.moveRight .output] ++
      preparePublicPrefixContext.asSubroutine 41 84).length = 84 := by
    simp only [List.length_append, List.length_singleton, Program.asSubroutine_length,
      show restoreGuessInput.length = 39 from rfl,
      show preparePublicPrefixContext.length = 42 from rfl]
  have hInstruction : prepareGuessPrefix[84]? = some Instruction.halt := by
    change (restoreGuessInput.asSubroutine 0 40 ++ [.moveRight .output] ++
      preparePublicPrefixContext.asSubroutine 41 84 ++ [Instruction.halt])[84]? = _
    rw [List.getElem?_append_right (by rw [hLength]), hLength]
    rfl
  have hHalt : Step prepareGuessPrefix
      ((prepareGuessPrefixFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding).resumeAt 84)
      (prepareGuessPrefixFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding) := by
    simp [Step, successors, next, hInstruction, prepareGuessPrefixFinish,
      preparePublicPrefixContextFinish, savePublicPrefixContextFinish, Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ ((RunsFor.succ hRestore hMove).trans hPrefix) hHalt

theorem prepareGuessPrefix_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareGuessPrefix := by
  simp [prepareGuessPrefix, restoreGuessInput, restoreStoredInput, preparePublicPrefixContext,
    rewindBitstring, skipUnary, skipFrame, savePublicPrefix, copyBitstring,
    Program.asSubroutine, Instruction.asSubroutine]

theorem prepareGuessPrefix_eval (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected product body : List Bool)
    (padding outputBlanks : Nat) (hBlanks : outputBlanks ≤ instanceBits.length + 1) :
    evalConfigWithin prepareGuessPrefix
      (prepareGuessPrefixStart before beforeOutput n instanceBits tupleTail reply canonical selected product body padding outputBlanks)
      (prepareGuessPrefixSteps n instanceBits tupleTail reply canonical selected product) =
      PMF.pure (prepareGuessPrefixFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding) :=
  (prepareGuessPrefix_runs _ _ _ _ _ _ _ _ _ _ _ _ hBlanks).evalConfigWithin_eq_pure_of_no_randomBit prepareGuessPrefix_no_randomBit

theorem prepareGuessPrefixFinish_output (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected product body : List Bool) (padding : Nat) :
    (prepareGuessPrefixFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding).outputTape =
      { left := (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++
          none :: none :: body.reverse.map some ++ none :: beforeOutput } := by
  simp only [prepareGuessPrefixFinish]
  rw [preparePublicPrefixContextFinish_layout]
  simp [List.append_assoc]

theorem prepareGuessPrefix_steps_le (n : Nat)
    (instanceBits tupleTail reply canonical selected product : List Bool) :
    prepareGuessPrefixSteps n instanceBits tupleTail reply canonical selected product ≤
      22*((encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail).length +
        reply.length + canonical.length + selected.length + product.length + 1) + 41 := by
  have hRestore := restoreGuessInput_steps_eq (encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail)
    reply canonical selected product
  have hPrefix := preparePublicPrefixContextSteps_le n instanceBits
  have hLength : (encodeSecurityParameter n ++ frame instanceBits).length ≤
      (encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail).length := by simp
  simp only [prepareGuessPrefixSteps]
  omega

set_option maxHeartbeats 1500000 in
theorem prepareGuessPrefix_control_closed (c d : Configuration)
    (hPc : c.pc < prepareGuessPrefix.length) (step : Step prepareGuessPrefix c d)
    (_hRunning : d.halted = false) : d.pc < prepareGuessPrefix.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 85 at hPc
  change d.pc < 85
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, prepareGuessPrefix,
    restoreGuessInput, restoreStoredInput, preparePublicPrefixContext, rewindBitstring,
    skipUnary, skipFrame, savePublicPrefix, copyBitstring, Program.asSubroutine,
    Instruction.asSubroutine, subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- Rewind the retained input and append its public prefix on arbitrary
finite tapes. The returned prefix need not be a valid cryptographic request;
the bound counts the actual restoration, separator move and native scans. -/
private theorem prepareGuessPrefix_terminates_core (input output : Tape) :
    ∃ finish used, used ≤ 1000000000000 * (input.cells + output.cells) + 1000000000000 ∧
      RunsFor prepareGuessPrefix
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      (∀ before blanks, output = { left := before, right := List.replicate blanks none } →
        finish.inputTape.current = some true ∧
        ∃ after remaining,
          finish.outputTape = { left := after, right := List.replicate remaining none }) := by
  obtain ⟨restored, restoreTime, hRestoreTime, restoreRun, restoreHalt, restoreOutput⟩ :=
    restoreGuessInput_terminates_from_anyTape input output
  obtain ⟨assembled, assembleTime, hAssembleTime, assembleRun, assembleHalt⟩ :=
    preparePublicPrefixContext_terminates_from_anyTape restored.inputTape restored.outputTape.moveRight
  have hRestore := restoreRun.withSubroutine_halted_of_closed
    [] restoreGuessInput ([.moveRight .output] ++ preparePublicPrefixContext.asSubroutine 41 84 ++ [.halt]) 40
    (by change 0 < 39; decide) rfl restoreHalt restoreGuessInput_control_closed
  change RunsFor prepareGuessPrefix
    ({ inputTape := input, outputTape := output } : Configuration) (restored.resumeAt 40) restoreTime at hRestore
  let moved : Configuration := { pc := 41, inputTape := restored.inputTape, outputTape := restored.outputTape.moveRight }
  have move : Step prepareGuessPrefix (restored.resumeAt 40) moved := by
    have code : prepareGuessPrefix[40]? = some (.moveRight .output) := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hAssemble := assembleRun.withSubroutine_halted_of_closed
    (restoreGuessInput.asSubroutine 0 40 ++ [.moveRight .output]) preparePublicPrefixContext [.halt] 84
    (by change 0 < 42; decide) rfl assembleHalt preparePublicPrefixContext_control_closed
  change RunsFor prepareGuessPrefix moved (assembled.resumeAt 84) assembleTime at hAssemble
  let finish : Configuration := { assembled with pc := 84, halted := true }
  have last : Step prepareGuessPrefix (assembled.resumeAt 84) finish := by
    have code : prepareGuessPrefix[84]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, restoreTime + 1 + assembleTime + 1, ?_,
    RunsFor.succ ((RunsFor.succ hRestore move).trans hAssemble) last, rfl, ?_⟩
  · have hStorage := GuardedCompiler.sourceStorage_le_of_run restoreRun
    change restored.inputTape.cells + restored.outputTape.cells ≤ input.cells + output.cells + restoreTime at hStorage
    have outputMove := Tape.cells_moveRight_le restored.outputTape
    omega
  · intro before blanks hOutput
    have hEntry : restored.outputTape.moveRight =
        { left := none :: before, right := List.replicate (blanks - 1) none } := by
      rw [restoreOutput, hOutput]
      cases blanks <;> simp [Tape.moveRight, List.replicate_succ]
    obtain ⟨assembledFresh, freshTime, savedInput, after, remaining,
      _hFreshTime, freshRun, freshHalt, freshCurrent, _freshLeft, freshOutput⟩ :=
      preparePublicPrefixContext_terminates_with_layout restored.inputTape (none :: before) (blanks - 1)
    rw [hEntry] at assembleRun
    have hEq := assembleRun.halted_finish_eq_of_no_randomBit freshRun
      assembleHalt freshHalt preparePublicPrefixContext_no_randomBit
    change assembled.inputTape.current = some true ∧
      ∃ after remaining, assembled.outputTape = { left := after, right := List.replicate remaining none }
    rw [hEq]
    exact ⟨freshCurrent, after, remaining, freshOutput⟩

theorem prepareGuessPrefix_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000000000 * (input.cells + output.cells) + 1000000000000 ∧
      RunsFor prepareGuessPrefix
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hBound, run, hHalted, _hLayout⟩ := prepareGuessPrefix_terminates_core input output
  exact ⟨finish, used, hBound, run, hHalted⟩

/-- Restoration and public-prefix copying retain fresh output scratch on
arbitrary finite input tapes. The restored input head is the actual true bit
used by the following retained-block scans, without a DDH validity premise. -/
theorem prepareGuessPrefix_terminates_with_output_layout (input : Tape)
    (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 1000000000000 * (input.cells +
        ({ left := before, right := List.replicate blanks none } : Tape).cells) + 1000000000000 ∧
      RunsFor prepareGuessPrefix
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧ finish.inputTape.current = some true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, hBound, run, hHalted, hLayout⟩ :=
    prepareGuessPrefix_terminates_core input { left := before, right := List.replicate blanks none }
  obtain ⟨hCurrent, after, remaining, hOutput⟩ := hLayout before blanks rfl
  exact ⟨finish, used, after, remaining, hBound, run, hHalted, hCurrent, hOutput⟩

theorem prepareGuessPrefix_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor prepareGuessPrefix
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (1000000000000 * (input.cells + output.cells) + 1000000000000)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ := prepareGuessPrefix_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted prepareGuessPrefix_no_randomBit hBound finish trace

/-- From fresh input/output frontiers, five-block restoration followed by
public-prefix assembly leaves a bit head and a suffix of those five blocks.
The saved input may contain arbitrary malformed cells. The blocks are those
exposed by native rewinds, not a decoded DDH tuple supplied by the caller. -/
theorem prepareGuessPrefix_terminates_from_fresh_tapes
    (savedInput savedOutput : List (Option Bool)) (inputBlanks outputBlanks : Nat) :
    let input : Tape := { left := savedInput, right := List.replicate inputBlanks none }
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    ∃ (finish : Configuration) (used : Nat) (a b c d e : List Bool)
      (after : List (Option Bool)) (remaining count : Nat),
      used ≤ 1000000000000 * (input.cells + output.cells) + 1000000000000 ∧
      RunsFor prepareGuessPrefix
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.inputTape.current = some true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } ∧
      finish.inputTape.right =
        (a.map some ++ none :: b.map some ++ none :: c.map some ++
          none :: d.map some ++ none :: e.map some ++ none :: List.replicate inputBlanks none).drop count := by
  dsimp only
  let input : Tape := { left := savedInput, right := List.replicate inputBlanks none }
  let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
  obtain ⟨restored, restoreTime, a, b, c, d, e, before, hRestoreTime,
    restoreRun, restoreHalt, restoreOutput, restoreInput⟩ :=
    restoreGuessInput_terminates_with_block_layout input output
  obtain ⟨assembled, assembleTime, _saved, after, remaining, hAssembleTime,
    assembleRun, assembleHalt, assembleCurrent, _assembleLeft, assembleOutput,
    offset, assembleRight⟩ :=
    preparePublicPrefixContext_terminates_with_suffix_layout restored.inputTape
      (none :: savedOutput) (outputBlanks - 1)
  have hEntry : restored.outputTape.moveRight =
      ({ left := none :: savedOutput, right := List.replicate (outputBlanks - 1) none } : Tape) := by
    rw [restoreOutput]
    cases outputBlanks <;> simp [output, Tape.moveRight, List.replicate_succ]
  have actualAssemble : RunsFor preparePublicPrefixContext
      ({ inputTape := restored.inputTape, outputTape := restored.outputTape.moveRight } : Configuration)
      assembled assembleTime := by
    rw [hEntry]
    exact assembleRun
  have hRestore := restoreRun.withSubroutine_halted_of_closed
    [] restoreGuessInput ([.moveRight .output] ++ preparePublicPrefixContext.asSubroutine 41 84 ++ [.halt]) 40
    (by change 0 < 39; decide) rfl restoreHalt restoreGuessInput_control_closed
  change RunsFor prepareGuessPrefix
    ({ inputTape := input, outputTape := output } : Configuration) (restored.resumeAt 40) restoreTime at hRestore
  let moved : Configuration := { pc := 41, inputTape := restored.inputTape, outputTape := restored.outputTape.moveRight }
  have move : Step prepareGuessPrefix (restored.resumeAt 40) moved := by
    have code : prepareGuessPrefix[40]? = some (.moveRight .output) := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hAssemble := actualAssemble.withSubroutine_halted_of_closed
    (restoreGuessInput.asSubroutine 0 40 ++ [.moveRight .output]) preparePublicPrefixContext [.halt] 84
    (by change 0 < 42; decide) rfl assembleHalt preparePublicPrefixContext_control_closed
  change RunsFor prepareGuessPrefix moved (assembled.resumeAt 84) assembleTime at hAssemble
  let finish : Configuration := { assembled with pc := 84, halted := true }
  have last : Step prepareGuessPrefix (assembled.resumeAt 84) finish := by
    have code : prepareGuessPrefix[84]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, restoreTime + 1 + assembleTime + 1, a, b, c, d, e, after, remaining,
    1 + offset, ?_, RunsFor.succ ((RunsFor.succ hRestore move).trans hAssemble) last,
    rfl, assembleCurrent, assembleOutput, ?_⟩
  · have hStorage := GuardedCompiler.sourceStorage_le_of_run restoreRun
    change restored.inputTape.cells + restored.outputTape.cells ≤ input.cells + output.cells + restoreTime at hStorage
    have outputMove := Tape.cells_moveRight_le restored.outputTape
    rw [← hEntry] at hAssembleTime
    change restoreTime ≤ 100000 * (input.cells + output.cells) + 100000 at hRestoreTime
    change restoreTime + 1 + assembleTime + 1 ≤ 1000000000000 * (input.cells + output.cells) + 1000000000000
    omega
  · have hStream : restored.inputTape.current :: restored.inputTape.right =
        a.map some ++ none :: b.map some ++ none :: c.map some ++
          none :: d.map some ++ none :: e.map some ++ none :: List.replicate inputBlanks none := by
      rw [restoreInput]
      cases a <;> simp [input, Tape.moveRight]
    have hRight := congrArg List.tail hStream
    change restored.inputTape.right = _ at hRight
    change assembled.inputTape.right = _
    rw [assembleRight, hRight, ← List.drop_one, List.drop_drop]

end Machine
