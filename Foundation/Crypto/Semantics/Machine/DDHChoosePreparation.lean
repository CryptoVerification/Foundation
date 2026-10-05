import Foundation.Crypto.Semantics.Machine.ChoosePreparation

namespace Machine

/-- Read the actual framed DDH input, save its public prefix, and assemble
its choose request from the first delimited element. The false terminator
of the outer tuple header is temporarily erased to reserve a separator.
The following tuple fields remain on the input tape. Restoring that header
and positioning the source-call tapes are separate, charged operations. -/
def prepareDDHChooseRequest : Program :=
  prepareDDHPublicPrefix.asSubroutine 0 41 ++ skipUnary.asSubroutine 41 48 ++
    [.moveLeft .input, .erase .input, .moveRight .input] ++
    assembleChooseField.asSubroutine 51 94 ++ [.halt]

def prepareDDHChooseSavedInput (n : Nat) (instanceBits tuple : List Bool) :
    List (Option Bool) :=
  List.replicate tuple.length (some true) ++
    (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ [none]

def prepareDDHChooseRequestFinish (n : Nat) (instanceBits key tail : List Bool) : Configuration :=
  { assembleChooseFieldFinish
      (prepareDDHChooseSavedInput n instanceBits (FiniteBitEncoding.delimit key ++ tail))
      ((encodeSecurityParameter n ++ frame instanceBits).reverse.map some) key tail 0 with pc := 94 }

def prepareDDHChooseRequestSteps (n : Nat) (instanceBits key tail : List Bool) : Nat :=
  prepareDDHPublicPrefixSteps n instanceBits +
    (3 * (FiniteBitEncoding.delimit key ++ tail).length + 3) + 3 +
    assembleChooseFieldSteps key tail + 1

/-- The complete trace starts on the standard current-input tape, rather
than on an externally assembled choose request. All scanning, temporary
separator writes, copying, status erasure, and the final halt are charged. -/
theorem prepareDDHChooseRequest_runs (n : Nat) (instanceBits key : List Bool)
    (nextBit : Bool) (tail : List Bool) :
    RunsFor prepareDDHChooseRequest
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail)))
      (prepareDDHChooseRequestFinish n instanceBits key (nextBit :: tail))
      (prepareDDHChooseRequestSteps n instanceBits key (nextBit :: tail)) := by
  let tuple := FiniteBitEncoding.delimit key ++ nextBit :: tail
  let publicBits := encodeSecurityParameter n ++ frame instanceBits
  let requestTail := List.replicate (tuple.length - 1) true ++ false :: tuple
  let a := prepareDDHPublicPrefix.asSubroutine 0 41
  let b := skipUnary.asSubroutine 41 48
  let k := assembleChooseField.asSubroutine 51 94
  let before := publicBits.reverse.map some ++ [none]
  let output : Tape := { left := publicBits.reverse.map some }
  have hFrame : frame tuple = true :: requestTail := by
    cases key <;> simp [tuple, requestTail, FiniteBitEncoding.delimit, frame,
      List.replicate_succ, List.append_assoc]
  have hPadding : instanceBits.length + 1 - publicBits.length = 0 := by
    simp [publicBits, encodeSecurityParameter, frame]
    omega
  have hPrefix := (prepareDDHPublicPrefix_runs n instanceBits requestTail).withSubroutine_halted_of_closed
    [] prepareDDHPublicPrefix (b ++ [.moveLeft .input, .erase .input, .moveRight .input] ++ k ++ [.halt]) 41
    (by change 0 < 40; decide) rfl rfl prepareDDHPublicPrefix_control_closed
  change RunsFor prepareDDHChooseRequest
    (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ true :: requestTail))
    ((prepareDDHPublicPrefixFinish n instanceBits requestTail).resumeAt 41)
    (prepareDDHPublicPrefixSteps n instanceBits) at hPrefix
  rw [← hFrame] at hPrefix
  have hScanStart : (prepareDDHPublicPrefixFinish n instanceBits requestTail).resumeAt 41 =
      (skipUnaryStart before tuple.length tuple output).rebasePc 41 := by
    have hHeader : encodeSecurityParameter tuple.length ++ tuple = frame tuple := rfl
    simp only [skipUnaryStart, hHeader, hFrame]
    simp [prepareDDHPublicPrefixFinish, savePublicPrefixFinish, Configuration.resumeAt,
      Configuration.rebasePc, Tape.ofBits, before, output, publicBits]
    simpa only [publicBits, List.length_append] using hPadding
  rw [hScanStart] at hPrefix
  have hScan := (skipUnary_runs before tuple.length tuple output).withSubroutine_halted_of_closed
    a skipUnary ([.moveLeft .input, .erase .input, .moveRight .input] ++ k ++ [.halt]) 48
    (by change 0 < 6; decide) rfl rfl skipUnary_control_closed
  change RunsFor prepareDDHChooseRequest
    ((skipUnaryStart before tuple.length tuple output).rebasePc 41)
    ((skipUnaryFinish before tuple.length tuple output).resumeAt 48)
    (3 * tuple.length + 3) at hScan
  let selected : Configuration :=
    { pc := 49,
      inputTape := {
        left := List.replicate tuple.length (some true) ++ before
        current := some false
        right := tuple.map some },
      outputTape := output }
  let erased : Configuration := { selected with pc := 50, inputTape := selected.inputTape.write none }
  have hBack : Step prepareDDHChooseRequest
      ((skipUnaryFinish before tuple.length tuple output).resumeAt 48) selected := by
    simp [Step, successors, next, prepareDDHChooseRequest, prepareDDHPublicPrefix,
      skipUnary, skipFrame, savePublicPrefix, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, skipUnaryFinish,
      Configuration.resumeAt, selected, Instruction.next, Configuration.updateTape,
      Configuration.advance, Tape.moveLeft, Tape.ofBits]
    cases key <;> rfl
  have hErase : Step prepareDDHChooseRequest selected erased := by
    simp [Step, successors, next, prepareDDHChooseRequest, prepareDDHPublicPrefix,
      skipUnary, skipFrame, savePublicPrefix, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, selected, erased,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hForward : Step prepareDDHChooseRequest erased
      ((assembleChooseFieldStart (prepareDDHChooseSavedInput n instanceBits tuple)
        (publicBits.reverse.map some) key (nextBit :: tail) 0).rebasePc 51) := by
    cases key <;>
      simp [Step, successors, next, prepareDDHChooseRequest, prepareDDHPublicPrefix,
        skipUnary, skipFrame, savePublicPrefix, rewindBitstring, copyBitstring,
        Program.asSubroutine, Instruction.asSubroutine, erased, selected,
        assembleChooseFieldStart_layout, prepareDDHChooseSavedInput,
        Configuration.rebasePc, Instruction.next, Configuration.updateTape, Configuration.advance,
        Tape.moveRight, Tape.write, Tape.ofBits, tuple, output, before, publicBits,
        FiniteBitEncoding.delimit, List.append_assoc]
  have hAssemble := (assembleChooseField_runs
      (prepareDDHChooseSavedInput n instanceBits tuple) (publicBits.reverse.map some) key nextBit tail 0).withSubroutine_halted_of_closed
    (a ++ b ++ [.moveLeft .input, .erase .input, .moveRight .input]) assembleChooseField [.halt] 94
    (by change 0 < 42; decide) rfl rfl assembleChooseField_control_closed
  change RunsFor prepareDDHChooseRequest
    ((assembleChooseFieldStart (prepareDDHChooseSavedInput n instanceBits tuple)
      (publicBits.reverse.map some) key (nextBit :: tail) 0).rebasePc 51)
    ((assembleChooseFieldFinish (prepareDDHChooseSavedInput n instanceBits tuple)
      (publicBits.reverse.map some) key (nextBit :: tail) 0).resumeAt 94)
    (assembleChooseFieldSteps key (nextBit :: tail)) at hAssemble
  have hHalt : Step prepareDDHChooseRequest
      ((assembleChooseFieldFinish (prepareDDHChooseSavedInput n instanceBits tuple)
        (publicBits.reverse.map some) key (nextBit :: tail) 0).resumeAt 94)
      (prepareDDHChooseRequestFinish n instanceBits key (nextBit :: tail)) := by
    simp [Step, successors, next, prepareDDHChooseRequest, prepareDDHPublicPrefix,
      skipUnary, skipFrame, savePublicPrefix, rewindBitstring, copyBitstring,
      assembleChooseField, writeChooseHeader, readDelimited,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt,
      assembleChooseFieldFinish, prepareDDHChooseRequestFinish, tuple, publicBits, Instruction.next]
  simpa only [prepareDDHChooseRequestSteps, tuple, Nat.add_assoc, Nat.reduceAdd] using
    RunsFor.succ ((RunsFor.succ (RunsFor.succ (RunsFor.succ
      (hPrefix.trans hScan) hBack) hErase) hForward).trans hAssemble) hHalt

theorem prepareDDHChooseRequest_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareDDHChooseRequest := by
  simp [prepareDDHChooseRequest, prepareDDHPublicPrefix, skipUnary, skipFrame,
    savePublicPrefix, rewindBitstring, copyBitstring, assembleChooseField,
    writeChooseHeader, readDelimited, Program.asSubroutine, Instruction.asSubroutine]

theorem prepareDDHChooseRequest_eval (n : Nat) (instanceBits key : List Bool)
    (nextBit : Bool) (tail : List Bool) :
    evalConfigWithin prepareDDHChooseRequest
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail)))
      (prepareDDHChooseRequestSteps n instanceBits key (nextBit :: tail)) =
      PMF.pure (prepareDDHChooseRequestFinish n instanceBits key (nextBit :: tail)) :=
  (prepareDDHChooseRequest_runs n instanceBits key nextBit tail).evalConfigWithin_eq_pure_of_no_randomBit
    prepareDDHChooseRequest_no_randomBit

/-- The second delimited element supplies a following bit even if its code
is empty. Thus the invocation law covers every canonical DDH triple. -/
theorem prepareDDHChooseRequest_triple_eval (n : Nat) (instanceBits key second third : List Bool) :
    evalConfigWithin prepareDDHChooseRequest
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ FiniteBitEncoding.delimit second ++ third)))
      (prepareDDHChooseRequestSteps n instanceBits key (FiniteBitEncoding.delimit second ++ third)) =
      PMF.pure (prepareDDHChooseRequestFinish n instanceBits key (FiniteBitEncoding.delimit second ++ third)) := by
  cases second with
  | nil => simpa [FiniteBitEncoding.delimit] using prepareDDHChooseRequest_eval n instanceBits key false third
  | cons bit rest =>
      simpa only [FiniteBitEncoding.delimit, List.cons_append, List.append_assoc] using
        prepareDDHChooseRequest_eval n instanceBits key true (bit :: (FiniteBitEncoding.delimit rest ++ third))

theorem prepareDDHChooseRequest_output (n : Nat) (instanceBits key tail : List Bool) :
    (prepareDDHChooseRequestFinish n instanceBits key tail).outputBits =
      encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key) := by
  simpa [prepareDDHChooseRequestFinish, Configuration.outputBits] using
    assembleChooseField_output
      (prepareDDHChooseSavedInput n instanceBits (FiniteBitEncoding.delimit key ++ tail))
      ((encodeSecurityParameter n ++ frame instanceBits).reverse.map some) key tail 0

/-- Linear native overhead in the actual finite DDH input, before any source
call. This does not assume a monotone source-program time bound. -/
theorem prepareDDHChooseRequestSteps_le (n : Nat) (instanceBits key tail : List Bool) :
    prepareDDHChooseRequestSteps n instanceBits key tail ≤
      40 * (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ tail)).length + 75 := by
  have hSave := savePublicPrefixSteps_le (encodeSecurityParameter n ++ frame instanceBits)
  have hAssemble := assembleChooseFieldSteps_le key tail
  simp only [prepareDDHChooseRequestSteps, prepareDDHPublicPrefixSteps,
    encodeSecurityParameter, frame, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil, FiniteBitEncoding.delimit_length] at *
  omega

/-- The full physical output layout is retained, including the erased status
cell and the following outer blank. This is not a tape normalization step. -/
theorem prepareDDHChooseRequest_output_layout (n : Nat) (instanceBits key tail : List Bool) :
    (prepareDDHChooseRequestFinish n instanceBits key tail).outputTape =
      { left := (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).reverse.map some,
        right := [none] } := by
  simp [prepareDDHChooseRequestFinish, assembleChooseFieldFinish, frame,
    List.reverse_append, List.map_append, List.append_assoc]

set_option maxHeartbeats 1000000 in
theorem prepareDDHChooseRequest_control_closed (c d : Configuration)
    (hPc : c.pc < prepareDDHChooseRequest.length) (step : Step prepareDDHChooseRequest c d)
    (_hRunning : d.halted = false) : d.pc < prepareDDHChooseRequest.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 95 at hPc
  change d.pc < 95
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, prepareDDHChooseRequest,
    prepareDDHPublicPrefix, skipUnary, skipFrame, savePublicPrefix, rewindBitstring,
    copyBitstring, assembleChooseField, writeChooseHeader, readDelimited,
    Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

private theorem erasePreviousCell (input : Tape) :
    (input.moveLeft.write none).moveRight = { input with left := none :: input.left.tail } := by
  cases input with
  | mk left current right => cases left <;> rfl

/-- All finite raw inputs stop while constructing the choose request.
The parser may encounter missing delimiters, internal blanks created by a
truncated frame, or an empty request. The bound follows actual retained
tapes through every stage; it does not require a valid DDH tuple. -/
theorem prepareDDHChooseRequest_terminates_with_layout (input : List Bool) :
    ∃ (finish : Configuration) (used : Nat) (savedInput : List (Option Bool))
      (rest : List Bool) (savedOutput : List (Option Bool)) (blanks : Nat),
      used ≤ 300000 * (input.length + 1) ∧
      RunsFor prepareDDHChooseRequest (Configuration.initial input) finish used ∧
      finish.halted = true ∧
      finish.inputTape.Equivalent { Tape.ofBits rest with left := savedInput } ∧
      finish.outputTape.Equivalent { left := savedOutput, right := List.replicate blanks none } := by
  obtain ⟨prefixFinish, prefixTime, prefixBefore, prefixRest, prefixOutput, prefixBlanks,
    hPrefixTime, hPrefixRun, hPrefixHalt, hPrefixInput, hPrefixOutput⟩ :=
    prepareDDHPublicPrefix_terminates_with_layout input
  obtain ⟨scanFinish, scanTime, scanBefore, scanRest, hScanTime, _hRestLength,
    hScanRun, hScanHalt, hScanInput, hScanOutput⟩ :=
    skipUnary_terminates_with_suffix prefixBefore (true :: prefixRest)
      ({ left := prefixOutput, right := List.replicate prefixBlanks none } : Tape)
  rw [← hPrefixInput, ← hPrefixOutput] at hScanRun
  let backed : Configuration :=
    { pc := 49, inputTape := scanFinish.inputTape.moveLeft, outputTape := scanFinish.outputTape }
  let erased : Configuration := { backed with pc := 50, inputTape := backed.inputTape.write none }
  let advanced : Configuration := { erased with pc := 51, inputTape := erased.inputTape.moveRight }
  have hAdvancedInput : advanced.inputTape =
      { Tape.ofBits scanRest with left := none :: scanBefore.tail } := by
    simp only [advanced, erased, backed, erasePreviousCell, hScanInput]
  have hAdvancedOutput : advanced.outputTape =
      { left := prefixOutput, right := List.replicate prefixBlanks none } := hScanOutput
  obtain ⟨assembleFinish, assembleTime, assembleBefore, assembleRest, assembleOutput,
    assembleBlanks, hAssembleTime, hAssembleRun, hAssembleHalt, hAssembleInput, hAssembleOutput⟩ :=
    assembleChooseField_terminates_with_layout (none :: scanBefore.tail) prefixOutput scanRest prefixBlanks
  rw [← hAdvancedInput, ← hAdvancedOutput] at hAssembleRun hAssembleTime
  let a := prepareDDHPublicPrefix.asSubroutine 0 41
  let b := skipUnary.asSubroutine 41 48
  let k := assembleChooseField.asSubroutine 51 94
  have hPrefix := hPrefixRun.withSubroutine_halted_of_closed
    [] prepareDDHPublicPrefix (b ++ [.moveLeft .input, .erase .input, .moveRight .input] ++ k ++ [.halt]) 41
    (by change 0 < 40; decide) rfl hPrefixHalt prepareDDHPublicPrefix_control_closed
  change RunsFor prepareDDHChooseRequest (Configuration.initial input)
    (prefixFinish.resumeAt 41) prefixTime at hPrefix
  have hScan := hScanRun.withSubroutine_halted_of_closed
    a skipUnary ([.moveLeft .input, .erase .input, .moveRight .input] ++ k ++ [.halt]) 48
    (by change 0 < 6; decide) rfl hScanHalt skipUnary_control_closed
  change RunsFor prepareDDHChooseRequest
    ({ pc := 41, inputTape := prefixFinish.inputTape, outputTape := prefixFinish.outputTape } : Configuration)
    (scanFinish.resumeAt 48) scanTime at hScan
  have hScanStart : prefixFinish.resumeAt 41 =
      ({ pc := 41, inputTape := prefixFinish.inputTape, outputTape := prefixFinish.outputTape } : Configuration) := rfl
  rw [← hScanStart] at hScan
  have hBack : Step prepareDDHChooseRequest (scanFinish.resumeAt 48) backed := by
    simp [Step, successors, next, prepareDDHChooseRequest, prepareDDHPublicPrefix, skipUnary,
      skipFrame, savePublicPrefix, rewindBitstring, copyBitstring, Program.asSubroutine,
      Instruction.asSubroutine, Configuration.resumeAt, backed, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hErase : Step prepareDDHChooseRequest backed erased := by
    simp [Step, successors, next, prepareDDHChooseRequest, prepareDDHPublicPrefix, skipUnary,
      skipFrame, savePublicPrefix, rewindBitstring, copyBitstring, Program.asSubroutine,
      Instruction.asSubroutine, backed, erased, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hForward : Step prepareDDHChooseRequest erased advanced := by
    simp [Step, successors, next, prepareDDHChooseRequest, prepareDDHPublicPrefix, skipUnary,
      skipFrame, savePublicPrefix, rewindBitstring, copyBitstring, Program.asSubroutine,
      Instruction.asSubroutine, backed, erased, advanced, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hUntilAssembly := RunsFor.succ (RunsFor.succ (RunsFor.succ
    (hPrefix.trans hScan) hBack) hErase) hForward
  have hAssemble := hAssembleRun.withSubroutine_halted_of_closed
    (a ++ b ++ [.moveLeft .input, .erase .input, .moveRight .input]) assembleChooseField [.halt] 94
    (by change 0 < 42; decide) rfl hAssembleHalt assembleChooseField_control_closed
  change RunsFor prepareDDHChooseRequest advanced (assembleFinish.resumeAt 94) assembleTime at hAssemble
  have hHalt : Step prepareDDHChooseRequest (assembleFinish.resumeAt 94)
      { assembleFinish.resumeAt 94 with halted := true } := by
    simp [Step, successors, next, prepareDDHChooseRequest, prepareDDHPublicPrefix, skipUnary,
      skipFrame, savePublicPrefix, rewindBitstring, copyBitstring, assembleChooseField,
      writeChooseHeader, readDelimited, Program.asSubroutine, Instruction.asSubroutine,
      Configuration.resumeAt, Instruction.next]
  refine ⟨{ assembleFinish.resumeAt 94 with halted := true },
    prefixTime + scanTime + 3 + assembleTime + 1,
    assembleBefore, assembleRest, assembleOutput, assembleBlanks, ?_, ?_, rfl,
    hAssembleInput, hAssembleOutput⟩
  · have hPrefixStorage := GuardedCompiler.sourceStorage_le_of_run hPrefix
    have hAssemblyStorage := GuardedCompiler.sourceStorage_le_of_run hUntilAssembly
    simp only [GuardedCompiler.sourceStorage, Configuration.resumeAt] at hPrefixStorage hAssemblyStorage
    have hInputCells : (Configuration.initial input).inputTape.cells ≤ input.length + 1 := by
      cases input
      · simp [Configuration.initial, Tape.ofBits, Tape.cells]
      · simp only [Configuration.initial, Tape.ofBits, Tape.cells, List.length_nil,
          List.length_map, List.length_cons]
        omega
    have hOutputCells : (Configuration.initial input).outputTape.cells = 1 := rfl
    have hScanLength : (true :: prefixRest).length ≤ prefixFinish.inputTape.cells := by
      rw [hPrefixInput]
      simp [Tape.ofBits, Tape.cells]
    omega
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using RunsFor.succ (hUntilAssembly.trans hAssemble) hHalt

/-- Forgetting the returned layout gives the original all-input stopping
certificate without duplicating the native preparation trace. -/
theorem prepareDDHChooseRequest_terminates (input : List Bool) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 300000 * (input.length + 1) ∧
      RunsFor prepareDDHChooseRequest (Configuration.initial input) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, _, _, _, _, hBound, hRun, hHalted, _, _⟩ :=
    prepareDDHChooseRequest_terminates_with_layout input
  exact ⟨finish, used, hBound, hRun, hHalted⟩

theorem prepareDDHChooseRequest_haltsWithin_anyInput (input : List Bool) :
    HaltsWithin prepareDDHChooseRequest input (300000 * (input.length + 1)) := by
  obtain ⟨finish, used, hBound, hRun, hHalted⟩ := prepareDDHChooseRequest_terminates input
  have hHalts : HaltsWith prepareDDHChooseRequest input finish.outputBits used := ⟨finish, hRun, hHalted, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit prepareDDHChooseRequest_no_randomBit).mono hBound

theorem prepareDDHChooseRequest_polynomialTime : PolynomialTime prepareDDHChooseRequest := by
  refine ⟨fun m => 300000 * (m + 1), ?_, prepareDDHChooseRequest_haltsWithin_anyInput⟩
  exact (PolynomiallyBounded.const 300000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))

end Machine
