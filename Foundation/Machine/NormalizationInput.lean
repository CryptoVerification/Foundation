import Foundation.Machine.ContextualPrefix
import Foundation.Machine.ContextualFrame
import Foundation.Machine.TapeSwap

namespace Machine

private theorem bitBlock_padding_getD (bits : List Bool) (blanks i : Nat) :
    (bits.map some ++ List.replicate blanks none).getD i none =
      (bits.map some).getD i none := by
  induction bits generalizing i with
  | nil => exact (Tape.blank_padding_equivalent [] blanks).2.2 i
  | cons bit bits ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [List.map_cons, List.cons_append, List.getD_cons_succ] using ih i

private theorem append_getD_congr (before first second : List (Option Bool))
    (h : ∀ i, first.getD i none = second.getD i none) :
    ∀ i, (before ++ first).getD i none = (before ++ second).getD i none := by
  induction before with
  | nil => exact h
  | cons cell before ih =>
      intro i
      cases i with
      | zero => rfl
      | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

private theorem bitBlock_drop_layout (bits : List Bool) (blanks count : Nat) :
    ∃ remaining : List Bool, ∀ i,
      ((bits.map some ++ List.replicate blanks none).drop count).getD i none =
        (remaining.map some ++ [none]).getD i none := by
  induction count generalizing bits with
  | zero =>
      refine ⟨bits, fun i => ?_⟩
      simp only [List.drop_zero]
      exact (bitBlock_padding_getD bits blanks i).trans
        (bitBlock_padding_getD bits 1 i).symm
  | succ count ih =>
      cases bits with
      | nil =>
          refine ⟨[], fun i => ?_⟩
          simp only [List.map_nil, List.nil_append, List.drop_replicate]
          exact ((Tape.blank_padding_equivalent [] (blanks - (count + 1))).2.2 i).trans
            ((Tape.blank_padding_equivalent [] 1).2.2 i).symm
      | cons bit bits =>
          simpa only [List.map_cons, List.cons_append, List.drop_succ_cons] using ih bits

/-- A suffix of two contiguous bit blocks separated by a blank still has
at most two such blocks. Only outer blank representation is ignored. -/
private theorem twoBitBlocks_drop_layout (first second : List Bool) (blanks count : Nat) :
    ∃ leading trailing : List Bool, ∀ i,
      ((first.map some ++ none :: (second.map some ++ List.replicate blanks none)).drop count).getD i none =
        (leading.map some ++ none :: trailing.map some).getD i none := by
  induction count generalizing first with
  | zero =>
      refine ⟨first, second, fun i => ?_⟩
      simp only [List.drop_zero]
      have h := append_getD_congr (first.map some ++ [none])
        (second.map some ++ List.replicate blanks none) (second.map some)
        (bitBlock_padding_getD second blanks) i
      simpa only [List.append_assoc, List.singleton_append] using h
  | succ count ih =>
      cases first with
      | nil =>
          obtain ⟨remaining, h⟩ := bitBlock_drop_layout second blanks count
          refine ⟨remaining, [], fun i => ?_⟩
          simpa only [List.map_nil, List.nil_append, List.drop_succ_cons] using h i
      | cons bit first =>
          simpa only [List.map_cons, List.cons_append, List.drop_succ_cons] using ih first

/-- Assemble the normalizer's actual finite input after a choose call.
The original DDH input and raw reply remain stored on the input tape.
The output tape receives the public prefix and a frame of the whole raw
reply, then native head movements position the normalizer input. Neither
malformed replies nor empty replies are decoded by this preparation code. -/
def prepareNormalizationInput : Program :=
  preparePublicPrefixContext.asSubroutine 0 43 ++
    GuardedCompiler.seekScratchInput.asSubroutine 43 49 ++
    writeFrame.asSubroutine 49 74 ++ [.moveRight .input] ++
    (Program.swapTapes rewindBitstring).asSubroutine 75 80 ++ [.halt]

def prepareNormalizationInputStart (savedInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (bit : Bool) (tupleTail reply : List Bool)
    (blanks : Nat) : Configuration :=
  preparePublicPrefixContextStart savedInput savedOutput n instanceBits
    (List.replicate tupleTail.length (some true) ++ some false ::
      ((bit :: tupleTail).map some ++ none :: (reply.map some ++ none :: List.replicate blanks none)))

def prepareNormalizationInputFinish (savedInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (bit : Bool) (tupleTail reply : List Bool)
    (blanks : Nat) : Configuration :=
  { pc := 80,
    inputTape := {
      left := none :: (reply.reverse.map some ++ none ::
        ((encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail)).reverse.map some ++ none :: savedInput))
      right := List.replicate (blanks - 1) none },
    outputTape := ({
      left := savedOutput
      right := (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).map some ++ [none] } : Tape).moveRight,
    halted := true }

def prepareNormalizationInputSteps (n : Nat) (instanceBits tuple reply : List Bool) : Nat :=
  preparePublicPrefixContextSteps n instanceBits + (3 * (frame tuple).length + 3) +
    writeFrameSteps reply + 1 +
    (2 * (encodeSecurityParameter n ++ frame instanceBits ++ frame reply).length + 4) + 1

private theorem normalizationRewind_control_closed (c d : Configuration)
    (hPc : c.pc < (Program.swapTapes rewindBitstring).length)
    (step : Step (Program.swapTapes rewindBitstring) c d)
    (_hRunning : d.halted = false) : d.pc < (Program.swapTapes rewindBitstring).length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 4 at hPc
  change d.pc < 4
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, Program.swapTapes,
    rewindBitstring, Instruction.swapTapes, TapeId.swap,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- Full configuration trace of preparation, with every count, copy,
separator crossing and rewind charged. The source response is framed
verbatim, so the certified normalizer sees exactly the adapter's raw output. -/
theorem prepareNormalizationInput_runs (savedInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (bit : Bool) (tupleTail reply : List Bool)
    (blanks : Nat) :
    RunsFor prepareNormalizationInput
      (prepareNormalizationInputStart savedInput savedOutput n instanceBits bit tupleTail reply blanks)
      (prepareNormalizationInputFinish savedInput savedOutput n instanceBits bit tupleTail reply blanks)
      (prepareNormalizationInputSteps n instanceBits (bit :: tupleTail) reply) := by
  let publicBits := encodeSecurityParameter n ++ frame instanceBits
  let tuple := bit :: tupleTail
  let ddhBits := publicBits ++ frame tuple
  let responseCells := reply.map some ++ none :: List.replicate blanks none
  let tupleCells := List.replicate tupleTail.length (some true) ++ some false ::
    (tuple.map some ++ none :: responseCells)
  let pre :=  preparePublicPrefixContext.asSubroutine 0 43
  let scan := GuardedCompiler.seekScratchInput.asSubroutine 43 49
  let framed := writeFrame.asSubroutine 49 74
  let other := (Program.swapTapes rewindBitstring).asSubroutine 75 80
  let output : Tape := { left := publicBits.reverse.map some ++ none :: savedOutput }
  let savedDDH := ddhBits.reverse.map some ++ none :: savedInput
  let framedOutput : Tape := { left := (publicBits ++ frame reply).reverse.map some ++ none :: savedOutput }
  let positioned : Configuration :=
    { inputTape := {
        left := none :: (reply.reverse.map some ++ none :: savedDDH)
        right := List.replicate (blanks - 1) none },
      outputTape := framedOutput }
  have hPrefix := (preparePublicPrefixContext_runs savedInput savedOutput n instanceBits tupleCells).withSubroutine_halted_of_closed
    [] preparePublicPrefixContext (scan ++ framed ++ [.moveRight .input] ++ other ++ [.halt]) 43
    (by change 0 < 42; decide) rfl rfl preparePublicPrefixContext_control_closed
  change RunsFor prepareNormalizationInput
    (prepareNormalizationInputStart savedInput savedOutput n instanceBits bit tupleTail reply blanks)
    ((preparePublicPrefixContextFinish savedInput savedOutput n instanceBits tupleCells).resumeAt 43)
    (preparePublicPrefixContextSteps n instanceBits) at hPrefix
  have hScanStart :
      (preparePublicPrefixContextFinish savedInput savedOutput n instanceBits tupleCells).resumeAt 43 =
      (seekBitstringNextStart (publicBits.reverse.map some ++ none :: savedInput)
        (frame tuple) responseCells output).rebasePc 43 := by
    rw [preparePublicPrefixContextFinish_layout, seekBitstringNextStart_layout]
    simp [publicBits, tupleCells, tuple, output, frame, Configuration.resumeAt,
      Configuration.rebasePc, Tape.moveRight, List.replicate_succ, List.map_append]
  rw [hScanStart] at hPrefix
  have hScan := (seekBitstringNext_runs (publicBits.reverse.map some ++ none :: savedInput)
      (frame tuple) responseCells output).withSubroutine_halted_of_closed
    pre GuardedCompiler.seekScratchInput (framed ++ [.moveRight .input] ++ other ++ [.halt]) 49
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareNormalizationInput
    ((seekBitstringNextStart (publicBits.reverse.map some ++ none :: savedInput)
      (frame tuple) responseCells output).rebasePc 43)
    ((seekBitstringNextFinish (publicBits.reverse.map some ++ none :: savedInput)
      (frame tuple) responseCells output).resumeAt 49)
    (3 * (frame tuple).length + 3) at hScan
  have hFrameStart :
      (seekBitstringNextFinish (publicBits.reverse.map some ++ none :: savedInput)
        (frame tuple) responseCells output).resumeAt 49 =
      (writeFrameContextStart savedDDH output.left (List.replicate blanks none) reply).rebasePc 49 := by
    cases reply with
    | nil =>
        rw [show responseCells = none :: List.replicate blanks none from rfl,
          seekBitstringNextFinish_layout, writeFrameContextStart_layout]
        simp [savedDDH, ddhBits, Configuration.resumeAt, Configuration.rebasePc,
          output, Tape.moveRight, List.reverse_append, List.map_append, List.append_assoc]
    | cons first rest =>
        rw [show responseCells = some first :: (rest.map some ++ none :: List.replicate blanks none) from rfl,
          seekBitstringNextFinish_layout, writeFrameContextStart_layout]
        simp [savedDDH, ddhBits, Configuration.resumeAt, Configuration.rebasePc,
          output, Tape.moveRight, List.reverse_append, List.map_append, List.append_assoc]
  rw [hFrameStart] at hScan
  have hFrame := (writeFrameContext_runs savedDDH output.left (List.replicate blanks none) reply).withSubroutine_halted_of_closed
    (pre ++ scan) writeFrame ([.moveRight .input] ++ other ++ [.halt]) 74
    (by change 0 < 24; decide) rfl rfl writeFrame_control_closed
  change RunsFor prepareNormalizationInput
    ((writeFrameContextStart savedDDH output.left (List.replicate blanks none) reply).rebasePc 49)
    ((writeFrameContextFinish savedDDH output.left (List.replicate blanks none) reply).resumeAt 74)
    (writeFrameSteps reply) at hFrame
  have hMove : Step prepareNormalizationInput
      ((writeFrameContextFinish savedDDH output.left (List.replicate blanks none) reply).resumeAt 74)
      (positioned.rebasePc 75) := by
    cases blanks <;> simp [Step, successors, next, prepareNormalizationInput,
      preparePublicPrefixContext, skipUnary, skipFrame, savePublicPrefix,
      GuardedCompiler.seekScratchInput, writeFrame, writeFrameHeader,
      rewindBitstring, copyBitstring, Program.asSubroutine, Instruction.asSubroutine,
      writeFrameContextFinish, positioned, framedOutput, output, Configuration.resumeAt,
      Configuration.rebasePc, Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveRight, List.replicate_succ, List.reverse_append, List.map_append, List.append_assoc]
  have hRewind := (rewindScratch_runs_from savedOutput (publicBits ++ frame reply) none []
      positioned.inputTape).swapTapes.withSubroutine_halted_of_closed
    (pre ++ scan ++ framed ++ [.moveRight .input]) (Program.swapTapes rewindBitstring) [.halt] 80
    (by change 0 < 4; decide) rfl rfl normalizationRewind_control_closed
  change RunsFor prepareNormalizationInput (positioned.rebasePc 75)
    ((prepareNormalizationInputFinish savedInput savedOutput n instanceBits bit tupleTail reply blanks).resumeAt 80)
    (2 * (publicBits ++ frame reply).length + 4) at hRewind
  have hHalt : Step prepareNormalizationInput
      ((prepareNormalizationInputFinish savedInput savedOutput n instanceBits bit tupleTail reply blanks).resumeAt 80)
      (prepareNormalizationInputFinish savedInput savedOutput n instanceBits bit tupleTail reply blanks) := by
    simp [Step, successors, next, prepareNormalizationInput, preparePublicPrefixContext,
      skipUnary, skipFrame, savePublicPrefix, GuardedCompiler.seekScratchInput,
      writeFrame, writeFrameHeader, rewindBitstring, copyBitstring, Program.swapTapes,
      Program.asSubroutine, Instruction.asSubroutine, prepareNormalizationInputFinish,
      Configuration.resumeAt, Instruction.next]
  simpa only [prepareNormalizationInputSteps, publicBits, tuple, Nat.add_assoc] using
    RunsFor.succ ((RunsFor.succ (((hPrefix.trans hScan).trans hFrame)) hMove).trans hRewind) hHalt

theorem prepareNormalizationInputStart_layout (savedInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (bit : Bool) (tupleTail reply : List Bool) (blanks : Nat) :
    prepareNormalizationInputStart savedInput savedOutput n instanceBits bit tupleTail reply blanks =
      ({ inputTape := {
          ({ right := (encodeSecurityParameter n ++ frame instanceBits ++ frame (bit :: tupleTail)).map some ++
              none :: (reply.map some ++ none :: List.replicate blanks none) } : Tape).moveRight with
          left := none :: savedInput }, outputTape := { left := savedOutput } } : Configuration) := by
  rw [prepareNormalizationInputStart, preparePublicPrefixContextStart, skipUnaryCellsStart_layout]
  cases n <;> simp [encodeSecurityParameter, frame, Tape.moveRight, List.map_append,
    List.replicate_succ, List.append_assoc]

theorem prepareNormalizationInput_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareNormalizationInput := by
  simp [prepareNormalizationInput, preparePublicPrefixContext, skipUnary, skipFrame,
    savePublicPrefix, GuardedCompiler.seekScratchInput, writeFrame, writeFrameHeader,
    rewindBitstring, copyBitstring, Program.swapTapes, Instruction.swapTapes,
    TapeId.swap, Program.asSubroutine, Instruction.asSubroutine]

theorem prepareNormalizationInput_eval (savedInput savedOutput : List (Option Bool))
    (n : Nat) (instanceBits : List Bool) (bit : Bool) (tupleTail reply : List Bool) (blanks : Nat) :
    evalConfigWithin prepareNormalizationInput
      (prepareNormalizationInputStart savedInput savedOutput n instanceBits bit tupleTail reply blanks)
      (prepareNormalizationInputSteps n instanceBits (bit :: tupleTail) reply) =
      PMF.pure (prepareNormalizationInputFinish savedInput savedOutput n instanceBits bit tupleTail reply blanks) :=
  (prepareNormalizationInput_runs savedInput savedOutput n instanceBits bit tupleTail reply blanks).evalConfigWithin_eq_pure_of_no_randomBit
    prepareNormalizationInput_no_randomBit

/-- The preparation bound charges both the saved current DDH input and the
actual raw response length. This says nothing about the execution budget
of the subsequent normalizer call. -/
theorem prepareNormalizationInputSteps_le (n : Nat) (instanceBits tuple reply : List Bool) :
    prepareNormalizationInputSteps n instanceBits tuple reply ≤
      40 * ((encodeSecurityParameter n ++ frame instanceBits ++ frame tuple).length + reply.length + 1) + 20 := by
  have hPrefix := preparePublicPrefixContextSteps_le n instanceBits
  have hFrame := writeFrameSteps_le reply
  simp only [prepareNormalizationInputSteps, List.length_append, frame,
    List.length_replicate, List.length_cons, List.length_nil] at *
  omega

set_option maxHeartbeats 2000000 in
theorem prepareNormalizationInput_control_closed (c d : Configuration)
    (hPc : c.pc < prepareNormalizationInput.length) (step : Step prepareNormalizationInput c d)
    (_hRunning : d.halted = false) : d.pc < prepareNormalizationInput.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 81 at hPc
  change d.pc < 81
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, prepareNormalizationInput,
    preparePublicPrefixContext, skipUnary, skipFrame, savePublicPrefix,
    GuardedCompiler.seekScratchInput, writeFrame, writeFrameHeader, rewindBitstring,
    copyBitstring, Program.swapTapes, Instruction.swapTapes, TapeId.swap,
    Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- The native normalizer-input assembler stops on arbitrary retained
input cells and produces a contiguous finite request on the opposite tape.
This theorem deliberately records only that request layout: on completely
arbitrary caller tapes it does not assert that the other tape is a fresh
guarded output region. The caller-specific separator invariant is separate. -/
theorem prepareNormalizationInput_terminates_with_request_layout (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat) :
    ∃ finish used request saved,
      used ≤ 5000000 * (input.cells +
        ({ left := savedOutput, right := List.replicate blanks none } : Tape).cells) + 5000000 ∧
      RunsFor prepareNormalizationInput
        ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape.Equivalent { Tape.ofBits request with left := none :: saved } ∧
      request.length ≤ finish.outputTape.cells := by
  let output : Tape := { left := savedOutput, right := List.replicate blanks none }
  obtain ⟨publicFinish, publicTime, _publicInput, publicOutput, publicBlanks,
    hPublicTime, hPublicRun, hPublicHalt, _hPublicCurrent, _hPublicLeft, hPublicOutput⟩ :=
    preparePublicPrefixContext_terminates_with_layout input savedOutput blanks
  obtain ⟨seek, seekTime, hSeekTime, hSeekRun, hSeekHalt, hSeekOutput⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape publicFinish.inputTape publicFinish.outputTape
  obtain ⟨framed, frameTime, frameSaved, frameBlanks,
    hFrameTime, hFrameRun, hFrameHalt, _hFrameBlank, hFrameOutput⟩ :=
    writeFrame_terminates_with_layout seek.inputTape publicOutput publicBlanks
  obtain ⟨canonicalRewind, request, saved, hRequestLength, hCanonicalRun, hCanonicalHalt,
    hCanonicalInput, _hCanonicalOutput⟩ :=
    rewindBitstring_terminates_from_suffix frameSaved [] framed.inputTape.moveRight
  have hRewindEntry :
      ({ inputTape := { Tape.ofBits [] with left := frameSaved },
         outputTape := framed.inputTape.moveRight } : Configuration).Equivalent
        { inputTape := framed.outputTape, outputTape := framed.inputTape.moveRight } := by
    refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
    rw [hFrameOutput]
    exact (Tape.blank_padding_equivalent frameSaved frameBlanks).symm
  obtain ⟨rewound, hRewindRun, hRewindEquivalent⟩ := hCanonicalRun.exists_equivalent hRewindEntry
  have hRewindHalt : rewound.halted = true := hRewindEquivalent.2.1.symm.trans hCanonicalHalt
  have hRequest : rewound.inputTape.Equivalent { Tape.ofBits request with left := none :: saved } := by
    simpa only [List.append_nil, List.singleton_append] using
      hRewindEquivalent.2.2.1.symm.trans hCanonicalInput
  let a := preparePublicPrefixContext.asSubroutine 0 43
  let b := GuardedCompiler.seekScratchInput.asSubroutine 43 49
  let k := writeFrame.asSubroutine 49 74
  let other := (Program.swapTapes rewindBitstring).asSubroutine 75 80
  have hPublic := hPublicRun.withSubroutine_halted_of_closed
    [] preparePublicPrefixContext (b ++ k ++ [.moveRight .input] ++ other ++ [.halt]) 43
    (by change 0 < 42; decide) rfl hPublicHalt preparePublicPrefixContext_control_closed
  change RunsFor prepareNormalizationInput
    ({ inputTape := input, outputTape := output } : Configuration) (publicFinish.resumeAt 43) publicTime at hPublic
  have hSeek := hSeekRun.withSubroutine_halted_of_closed
    a GuardedCompiler.seekScratchInput (k ++ [.moveRight .input] ++ other ++ [.halt]) 49
    (by change 0 < 5; decide) rfl hSeekHalt GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareNormalizationInput (publicFinish.resumeAt 43) (seek.resumeAt 49) seekTime at hSeek
  have hFrameEntry :
      ({ inputTape := seek.inputTape,
         outputTape := { left := publicOutput, right := List.replicate publicBlanks none } } : Configuration).rebasePc 49 =
      seek.resumeAt 49 := by
    simp only [Configuration.rebasePc, Configuration.resumeAt, hSeekOutput, hPublicOutput, Nat.add_zero]
  have hFrame := hFrameRun.withSubroutine_halted_of_closed
    (a ++ b) writeFrame ([.moveRight .input] ++ other ++ [.halt]) 74
    (by change 0 < 24; decide) rfl hFrameHalt writeFrame_control_closed
  change RunsFor prepareNormalizationInput
    (({ inputTape := seek.inputTape,
        outputTape := { left := publicOutput, right := List.replicate publicBlanks none } } : Configuration).rebasePc 49)
    (framed.resumeAt 74) frameTime at hFrame
  rw [hFrameEntry] at hFrame
  let moved : Configuration := { pc := 75, inputTape := framed.inputTape.moveRight, outputTape := framed.outputTape }
  have hMove : Step prepareNormalizationInput (framed.resumeAt 74) moved := by
    simp [Step, successors, next, prepareNormalizationInput, preparePublicPrefixContext,
      skipUnary, skipFrame, savePublicPrefix, GuardedCompiler.seekScratchInput,
      writeFrame, writeFrameHeader, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt,
      moved, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hRewind := hRewindRun.swapTapes.withSubroutine_halted_of_closed
    (a ++ b ++ k ++ [.moveRight .input]) (Program.swapTapes rewindBitstring) [.halt] 80
    (by change 0 < 4; decide) rfl hRewindHalt normalizationRewind_control_closed
  change RunsFor prepareNormalizationInput moved (rewound.swapTapes.resumeAt 80) (2 * request.length + 4) at hRewind
  let finish : Configuration := { rewound.swapTapes.resumeAt 80 with halted := true }
  have hHalt : Step prepareNormalizationInput (rewound.swapTapes.resumeAt 80) finish := by
    simp [Step, successors, next, prepareNormalizationInput, preparePublicPrefixContext,
      skipUnary, skipFrame, savePublicPrefix, GuardedCompiler.seekScratchInput,
      writeFrame, writeFrameHeader, rewindBitstring, copyBitstring, Program.swapTapes,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, finish, Instruction.next]
  have hUntilSeek := hPublic.trans hSeek
  have hUntilFrame := hUntilSeek.trans hFrame
  refine ⟨finish, publicTime + seekTime + frameTime + 1 + (2 * request.length + 4) + 1,
    request, saved, ?_, RunsFor.succ ((RunsFor.succ hUntilFrame hMove).trans hRewind) hHalt,
    rfl, hRequest, hRequest.contiguous_length_le_cells⟩
  have hPublicStorage := GuardedCompiler.sourceStorage_le_of_run hPublic
  have hSeekStorage := GuardedCompiler.sourceStorage_le_of_run hUntilSeek
  have hFrameStorage := GuardedCompiler.sourceStorage_le_of_run hUntilFrame
  simp only [GuardedCompiler.sourceStorage, Configuration.resumeAt] at hPublicStorage hSeekStorage hFrameStorage
  have hFrameLeft : frameSaved.length ≤ framed.outputTape.cells := by
    rw [hFrameOutput]
    simp only [Tape.cells, List.length_replicate]
    omega
  rw [← hPublicOutput, ← hSeekOutput] at hFrameTime
  change _ ≤ 5000000 * (input.cells + output.cells) + 5000000
  change publicTime ≤ 1000 * (input.cells + output.cells) + 1000 at hPublicTime
  omega

/-- The retained choose-result separator limits the remaining input to two
contiguous bit blocks. Native scanning and framing therefore leave an
actually blank destination for the guarded normalizer. This hypothesis is
stronger than arbitrary-input termination and is checked by the caller. -/
theorem prepareNormalizationInput_terminates_with_guarded_layout (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat)
    (first second : List Bool) (inputBlanks : Nat)
    (hRight : input.right = first.map some ++ none ::
      (second.map some ++ List.replicate inputBlanks none)) :
    ∃ finish used beforeInput beforeOutput request,
      used ≤ 5000000 * (input.cells +
        ({ left := savedOutput, right := List.replicate blanks none } : Tape).cells) + 5000000 ∧
      RunsFor prepareNormalizationInput
        ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      (finish.resumeAt 0).Equivalent
        (GuardedCompiler.packInputStart beforeInput beforeOutput request).swapTapes ∧
      request.length ≤ finish.outputTape.cells := by
  let output : Tape := { left := savedOutput, right := List.replicate blanks none }
  obtain ⟨publicFinish, publicTime, _publicInput, publicOutput, publicBlanks,
    _hPublicTime, hPublicRun, hPublicHalt, hPublicCurrent, _hPublicLeft,
    hPublicOutput, count, hSuffix⟩ :=
    preparePublicPrefixContext_terminates_with_suffix_layout input savedOutput blanks
  obtain ⟨leading, trailing, hBlocks⟩ := twoBitBlocks_drop_layout first second inputBlanks count
  have hRemaining (i : Nat) : publicFinish.inputTape.right.getD i none =
      (leading.map some ++ none :: trailing.map some).getD i none := by
    rw [hSuffix, hRight]
    exact hBlocks i
  let publicLeft := publicFinish.inputTape.left
  let scanned := true :: leading
  let savedInput := scanned.reverse.map some ++ publicLeft
  have hSeekEntry :
      (seekBitstringNextStart publicLeft scanned (trailing.map some) publicFinish.outputTape).Equivalent
        ({ inputTape := publicFinish.inputTape, outputTape := publicFinish.outputTape } : Configuration) := by
    rw [seekBitstringNextStart_layout]
    refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
    change ({ left := publicLeft, current := some true, right := leading.map some ++ none :: trailing.map some } : Tape).Equivalent publicFinish.inputTape
    exact ⟨hPublicCurrent.symm, fun _ => rfl, fun i => (hRemaining i).symm⟩
  obtain ⟨seek, hSeekRun, hSeekEq⟩ :=
    (seekBitstringNext_runs publicLeft scanned (trailing.map some) publicFinish.outputTape).exists_equivalent hSeekEntry
  have hSeekHalt : seek.halted = true := hSeekEq.2.1.symm
  have hPadding :
      ({ right := trailing.map some } : Tape).Equivalent
        { right := trailing.map some ++ [none] } :=
    ⟨rfl, fun _ => rfl, fun i => (bitBlock_padding_getD trailing 1 i).symm⟩
  have hFrameInput :
      (seekBitstringNextFinish publicLeft scanned (trailing.map some) publicFinish.outputTape).inputTape.Equivalent
        (writeFrameContextPaddedStart savedInput publicOutput [] trailing publicBlanks).inputTape := by
    rw [seekBitstringNextFinish_layout_cells, writeFrameContextPaddedStart_layout]
    refine ⟨hPadding.moveRight.1, fun _ => rfl, hPadding.moveRight.2.2⟩
  have hFrameEntry :
      (writeFrameContextPaddedStart savedInput publicOutput [] trailing publicBlanks).Equivalent
        ({ inputTape := seek.inputTape, outputTape := seek.outputTape } : Configuration) := by
    refine ⟨rfl, rfl, hFrameInput.symm.trans hSeekEq.2.2.1, ?_⟩
    simpa only [seekBitstringNextFinish, writeFrameContextPaddedStart, hPublicOutput] using hSeekEq.2.2.2
  obtain ⟨framed, hFrameRun, hFrameEq⟩ :=
    (writeFrameContextPadded_runs savedInput publicOutput [] trailing publicBlanks).exists_equivalent hFrameEntry
  have hFrameHalt : framed.halted = true := hFrameEq.2.1.symm
  let frameSaved := (frame trailing).reverse.map some ++ publicOutput
  let frameBlanks := publicBlanks - (2 * trailing.length + 1)
  let destinationSaved := none :: (trailing.reverse.map some ++ none :: savedInput)
  have hFrameOutput : framed.outputTape.Equivalent
      { left := frameSaved, right := List.replicate frameBlanks none } := hFrameEq.2.2.2.symm
  have hFresh : framed.inputTape.moveRight.Equivalent { left := destinationSaved } := by
    simpa only [writeFrameContextPaddedFinish, Tape.moveRight] using hFrameEq.2.2.1.symm.moveRight
  obtain ⟨canonicalRewind, request, saved, _hRequestLength, hCanonicalRun, hCanonicalHalt,
    hCanonicalInput, hCanonicalOutput⟩ :=
    rewindBitstring_terminates_from_suffix frameSaved [] framed.inputTape.moveRight
  have hRewindEntry :
      ({ inputTape := { Tape.ofBits [] with left := frameSaved },
         outputTape := framed.inputTape.moveRight } : Configuration).Equivalent
        { inputTape := framed.outputTape, outputTape := framed.inputTape.moveRight } := by
    refine ⟨rfl, rfl, ?_, Tape.Equivalent.refl _⟩
    exact ((Tape.blank_padding_equivalent frameSaved frameBlanks).symm.trans hFrameOutput.symm)
  obtain ⟨rewound, hRewindRun, hRewindEq⟩ := hCanonicalRun.exists_equivalent hRewindEntry
  have hRewindHalt : rewound.halted = true := hRewindEq.2.1.symm.trans hCanonicalHalt
  have hRequest : rewound.inputTape.Equivalent { Tape.ofBits request with left := none :: saved } := by
    simpa only [List.append_nil, List.singleton_append] using hRewindEq.2.2.1.symm.trans hCanonicalInput
  have hDestination : rewound.outputTape.Equivalent { left := destinationSaved } := by
    have hOther : rewound.outputTape.Equivalent framed.inputTape.moveRight := by
      rw [← hCanonicalOutput]
      exact hRewindEq.2.2.2.symm
    exact hOther.trans hFresh
  let a := preparePublicPrefixContext.asSubroutine 0 43
  let b := GuardedCompiler.seekScratchInput.asSubroutine 43 49
  let k := writeFrame.asSubroutine 49 74
  let other := (Program.swapTapes rewindBitstring).asSubroutine 75 80
  have hPublic := hPublicRun.withSubroutine_halted_of_closed
    [] preparePublicPrefixContext (b ++ k ++ [.moveRight .input] ++ other ++ [.halt]) 43
    (by change 0 < 42; decide) rfl hPublicHalt preparePublicPrefixContext_control_closed
  change RunsFor prepareNormalizationInput
    ({ inputTape := input, outputTape := output } : Configuration) (publicFinish.resumeAt 43) publicTime at hPublic
  have hSeek := hSeekRun.withSubroutine_halted_of_closed
    a GuardedCompiler.seekScratchInput (k ++ [.moveRight .input] ++ other ++ [.halt]) 49
    (by change 0 < 5; decide) rfl hSeekHalt GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareNormalizationInput (publicFinish.resumeAt 43) (seek.resumeAt 49)
    (3 * scanned.length + 3) at hSeek
  have hFrame := hFrameRun.withSubroutine_halted_of_closed
    (a ++ b) writeFrame ([.moveRight .input] ++ other ++ [.halt]) 74
    (by change 0 < 24; decide) rfl hFrameHalt writeFrame_control_closed
  change RunsFor prepareNormalizationInput (seek.resumeAt 49) (framed.resumeAt 74)
    (writeFrameSteps trailing) at hFrame
  let moved : Configuration := { pc := 75, inputTape := framed.inputTape.moveRight, outputTape := framed.outputTape }
  have hMove : Step prepareNormalizationInput (framed.resumeAt 74) moved := by
    simp [Step, successors, next, prepareNormalizationInput, preparePublicPrefixContext,
      skipUnary, skipFrame, savePublicPrefix, GuardedCompiler.seekScratchInput,
      writeFrame, writeFrameHeader, rewindBitstring, copyBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt,
      moved, Instruction.next, Configuration.updateTape, Configuration.advance]
  have hRewind := hRewindRun.swapTapes.withSubroutine_halted_of_closed
    (a ++ b ++ k ++ [.moveRight .input]) (Program.swapTapes rewindBitstring) [.halt] 80
    (by change 0 < 4; decide) rfl hRewindHalt normalizationRewind_control_closed
  change RunsFor prepareNormalizationInput moved (rewound.swapTapes.resumeAt 80)
    (2 * request.length + 4) at hRewind
  let nativeFinish : Configuration := { rewound.swapTapes.resumeAt 80 with halted := true }
  have hHalt : Step prepareNormalizationInput (rewound.swapTapes.resumeAt 80) nativeFinish := by
    simp [Step, successors, next, prepareNormalizationInput, preparePublicPrefixContext,
      skipUnary, skipFrame, savePublicPrefix, GuardedCompiler.seekScratchInput,
      writeFrame, writeFrameHeader, rewindBitstring, copyBitstring, Program.swapTapes,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, nativeFinish, Instruction.next]
  have hNativeRun : RunsFor prepareNormalizationInput
      ({ inputTape := input, outputTape := output } : Configuration) nativeFinish
      (publicTime + (3 * scanned.length + 3) + writeFrameSteps trailing + 1 + (2 * request.length + 4) + 1) :=
    RunsFor.succ ((RunsFor.succ ((hPublic.trans hSeek).trans hFrame) hMove).trans hRewind) hHalt
  have hLayout : (nativeFinish.resumeAt 0).Equivalent
      (GuardedCompiler.packInputStart (none :: saved) destinationSaved request).swapTapes :=
    ⟨rfl, rfl, hDestination, hRequest⟩
  obtain ⟨finish, used, _oldRequest, _oldSaved, hBound, hRun, hHalted, _hOldRequest, _hOldLength⟩ :=
    prepareNormalizationInput_terminates_with_request_layout input savedOutput blanks
  have hSame : finish = nativeFinish := hRun.halted_finish_eq_of_no_randomBit
    hNativeRun hHalted rfl prepareNormalizationInput_no_randomBit
  have hActualLayout : (finish.resumeAt 0).Equivalent
      (GuardedCompiler.packInputStart (none :: saved) destinationSaved request).swapTapes := by
    rw [hSame]
    exact hLayout
  exact ⟨finish, used, none :: saved, destinationSaved, request,
    hBound, hRun, hHalted, hActualLayout, hActualLayout.2.2.2.contiguous_length_le_cells⟩

end Machine
