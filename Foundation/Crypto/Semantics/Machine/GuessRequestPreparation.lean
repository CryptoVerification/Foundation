import Foundation.Crypto.Semantics.Machine.GuessPrefixPreparation
import Foundation.Crypto.Semantics.Machine.StoredGuessInputScratch
import Foundation.Crypto.Semantics.Machine.SavedMessageFraming

namespace Machine

/-- Construct the entire encoded guess request from retained native tape
cells. Restore and copy its public prefix, reach fresh input scratch after
five stored blocks, then append the frame of the already constructed body.
There is no high-level input-loading or framing instruction. -/
def prepareGuessRequest : Program :=
  prepareGuessPrefix.asSubroutine 0 86 ++ seekGuessInputScratch.asSubroutine 86 120 ++
    frameSavedMessage.asSubroutine 120 182 ++ [.halt]

def prepareGuessRequestStart (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected product body : List Bool)
    (padding outputBlanks : Nat) : Configuration :=
  prepareGuessPrefixStart before beforeOutput n instanceBits tupleTail reply canonical selected product body padding outputBlanks

def prepareGuessRequestFinish (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected product body : List Bool)
    (padding : Nat) : Configuration :=
  let original := encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail
  { frameSavedMessageFinish
      (product.reverse.map some ++ none :: selected.reverse.map some ++ none ::
        canonical.reverse.map some ++ none :: reply.reverse.map some ++ none ::
        original.reverse.map some ++ none :: before)
      beforeOutput (encodeSecurityParameter n ++ frame instanceBits) body (padding - 1) with pc := 182 }

def prepareGuessRequestSteps (n : Nat)
    (instanceBits tupleTail reply canonical selected product body : List Bool) : Nat :=
  prepareGuessPrefixSteps n instanceBits tupleTail reply canonical selected product +
    seekGuessInputScratchSteps (true :: tupleTail) reply canonical selected product +
    frameSavedMessageSteps (encodeSecurityParameter n ++ frame instanceBits) body + 1

set_option maxHeartbeats 1000000 in
theorem prepareGuessRequest_runs (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected product body : List Bool)
    (padding outputBlanks : Nat) (hBlanks : outputBlanks ≤ instanceBits.length + 1) :
    RunsFor prepareGuessRequest
      (prepareGuessRequestStart before beforeOutput n instanceBits tupleTail reply canonical selected product body padding outputBlanks)
      (prepareGuessRequestFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding)
      (prepareGuessRequestSteps n instanceBits tupleTail reply canonical selected product body) := by
  let publicBits := encodeSecurityParameter n ++ frame instanceBits
  let original := publicBits ++ true :: tupleTail
  let output : Tape := {
    left := publicBits.reverse.map some ++ none :: none :: body.reverse.map some ++ none :: beforeOutput }
  let beforeTuple := publicBits.reverse.map some ++ none :: before
  let saved := product.reverse.map some ++ none :: selected.reverse.map some ++ none ::
    canonical.reverse.map some ++ none :: reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before
  let prefixFinish := prepareGuessPrefixFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding
  let seekStart := seekGuessInputScratchStart beforeTuple (true :: tupleTail) reply canonical selected product padding output
  let seekFinish := seekGuessInputScratchFinish beforeTuple (true :: tupleTail) reply canonical selected product padding output
  let frameStart := frameSavedMessageStart saved beforeOutput publicBits body (padding - 1)
  have hPrefix := (prepareGuessPrefix_runs before beforeOutput n instanceBits tupleTail reply canonical selected product body
    padding outputBlanks hBlanks).withSubroutine_halted_of_closed
    [] prepareGuessPrefix (seekGuessInputScratch.asSubroutine 86 120 ++ frameSavedMessage.asSubroutine 120 182 ++ [.halt]) 86
    (by change 0 < 85; decide) rfl rfl prepareGuessPrefix_control_closed
  change RunsFor prepareGuessRequest
    (prepareGuessRequestStart before beforeOutput n instanceBits tupleTail reply canonical selected product body padding outputBlanks)
    (prefixFinish.resumeAt 86) (prepareGuessPrefixSteps n instanceBits tupleTail reply canonical selected product) at hPrefix
  have hSeekStart : prefixFinish.resumeAt 86 = seekStart.rebasePc 86 := by
    simp [prefixFinish, prepareGuessPrefixFinish, preparePublicPrefixContextFinish_layout,
      seekStart, seekGuessInputScratchStart, seekBitstringNextStart_layout, beforeTuple,
      publicBits, output, Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight, List.append_assoc]
  rw [hSeekStart] at hPrefix
  have hSeek := (seekGuessInputScratch_runs beforeTuple (true :: tupleTail) reply canonical selected product padding output).withSubroutine_halted_of_closed
    (prepareGuessPrefix.asSubroutine 0 86) seekGuessInputScratch
    (frameSavedMessage.asSubroutine 120 182 ++ [.halt]) 120
    (by change 0 < 33; decide) rfl rfl seekGuessInputScratch_control_closed
  change RunsFor prepareGuessRequest (seekStart.rebasePc 86) (seekFinish.resumeAt 120)
    (seekGuessInputScratchSteps (true :: tupleTail) reply canonical selected product) at hSeek
  have hFrameStart : seekFinish.resumeAt 120 = frameStart.rebasePc 120 := by
    simp [seekFinish, seekGuessInputScratchFinish, seekStoredInputScratchFinish, frameStart,
      frameSavedMessageStart, beforeTuple, saved, original, Configuration.resumeAt,
      Configuration.rebasePc, output, List.reverse_append, List.map_append, List.append_assoc]
  rw [hFrameStart] at hSeek
  have hFrame := (frameSavedMessage_runs saved beforeOutput publicBits body (padding - 1)).withSubroutine_halted_of_closed
    (prepareGuessPrefix.asSubroutine 0 86 ++ seekGuessInputScratch.asSubroutine 86 120)
    frameSavedMessage [.halt] 182 (by change 0 < 61; decide) rfl rfl frameSavedMessage_control_closed
  change RunsFor prepareGuessRequest (frameStart.rebasePc 120)
    ((prepareGuessRequestFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding).resumeAt 182)
    (frameSavedMessageSteps publicBits body) at hFrame
  have hLength : (prepareGuessPrefix.asSubroutine 0 86 ++ seekGuessInputScratch.asSubroutine 86 120 ++
      frameSavedMessage.asSubroutine 120 182).length = 182 := by
    simp only [List.length_append, Program.asSubroutine_length,
      show prepareGuessPrefix.length = 85 from rfl,
      show seekGuessInputScratch.length = 33 from rfl,
      show frameSavedMessage.length = 61 from rfl]
  have hInstruction : prepareGuessRequest[182]? = some Instruction.halt := by
    change (prepareGuessPrefix.asSubroutine 0 86 ++ seekGuessInputScratch.asSubroutine 86 120 ++
      frameSavedMessage.asSubroutine 120 182 ++ [Instruction.halt])[182]? = _
    rw [List.getElem?_append_right (by rw [hLength]), hLength]
    rfl
  have hHalt : Step prepareGuessRequest
      ((prepareGuessRequestFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding).resumeAt 182)
      (prepareGuessRequestFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding) := by
    simp [Step, successors, next, hInstruction, prepareGuessRequestFinish,
      frameSavedMessageFinish, Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ ((hPrefix.trans hSeek).trans hFrame) hHalt

private theorem guessRequestSubroutine_no_randomBit (source : Program) (base returnPc : Nat)
    (h : ∀ tape, Instruction.randomBit tape ∉ source) (tape : TapeId) :
    Instruction.randomBit tape ∉ source.asSubroutine base returnPc := by
  intro hm
  simp only [Program.asSubroutine, List.mem_append, List.mem_map, List.mem_singleton] at hm
  rcases hm with ⟨i, hi, heq⟩ | heq
  · have hOriginal : i = Instruction.randomBit tape := by
      cases i <;> simp_all [Instruction.asSubroutine]
    exact h tape (hOriginal ▸ hi)
  · cases heq

theorem prepareGuessRequest_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareGuessRequest := by
  simp only [prepareGuessRequest, List.mem_append, List.mem_singleton, not_or]
  exact ⟨⟨⟨guessRequestSubroutine_no_randomBit _ _ _ prepareGuessPrefix_no_randomBit tape,
    guessRequestSubroutine_no_randomBit _ _ _ seekGuessInputScratch_no_randomBit tape⟩,
    guessRequestSubroutine_no_randomBit _ _ _ frameSavedMessage_no_randomBit tape⟩, by simp⟩

theorem prepareGuessRequest_eval (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected product body : List Bool)
    (padding outputBlanks : Nat) (hBlanks : outputBlanks ≤ instanceBits.length + 1) :
    evalConfigWithin prepareGuessRequest
      (prepareGuessRequestStart before beforeOutput n instanceBits tupleTail reply canonical selected product body padding outputBlanks)
      (prepareGuessRequestSteps n instanceBits tupleTail reply canonical selected product body) =
      PMF.pure (prepareGuessRequestFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding) :=
  (prepareGuessRequest_runs _ _ _ _ _ _ _ _ _ _ _ _ hBlanks).evalConfigWithin_eq_pure_of_no_randomBit prepareGuessRequest_no_randomBit

/-- The complete encoded request is a contiguous bit block. Both the saved
body and original source-call data remain beyond actual blank separators. -/
theorem prepareGuessRequestFinish_output (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected product body : List Bool) (padding : Nat) :
    (prepareGuessRequestFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding).outputTape =
      { left := (encodeSecurityParameter n ++ frame instanceBits ++ frame body).reverse.map some ++
          none :: none :: body.reverse.map some ++ none :: beforeOutput } := by
  simp [prepareGuessRequestFinish, frameSavedMessageFinish, List.append_assoc]

theorem prepareGuessRequest_length : prepareGuessRequest.length = 183 := by
  simp only [prepareGuessRequest, List.length_append, List.length_singleton, Program.asSubroutine_length,
    show prepareGuessPrefix.length = 85 from rfl,
    show seekGuessInputScratch.length = 33 from rfl,
    show frameSavedMessage.length = 61 from rfl]

theorem prepareGuessRequest_steps_le (n : Nat)
    (instanceBits tupleTail reply canonical selected product body : List Bool) :
    prepareGuessRequestSteps n instanceBits tupleTail reply canonical selected product body ≤
      30*((encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail).length +
        reply.length + canonical.length + selected.length + product.length + body.length + 1) + 88 := by
  have hp := prepareGuessPrefix_steps_le n instanceBits tupleTail reply canonical selected product
  have hs := seekGuessInputScratch_steps_eq (true :: tupleTail) reply canonical selected product
  have hf := frameSavedMessage_steps_le (encodeSecurityParameter n ++ frame instanceBits) body
  have hLength : (encodeSecurityParameter n ++ frame instanceBits).length ≤
      (encodeSecurityParameter n ++ frame instanceBits ++ true :: tupleTail).length := by simp
  simp only [List.length_cons] at hs
  simp only [prepareGuessRequestSteps, List.length_append, List.length_cons]
  simp only [List.length_append, List.length_cons] at hp hf hLength
  omega

theorem prepareGuessRequest_haltsFrom (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected product body : List Bool)
    (padding outputBlanks : Nat) (hBlanks : outputBlanks ≤ instanceBits.length + 1)
    (finish : Configuration)
    (run : PaddedRunsFor prepareGuessRequest
      (prepareGuessRequestStart before beforeOutput n instanceBits tupleTail reply canonical selected product body padding outputBlanks)
      finish (prepareGuessRequestSteps n instanceBits tupleTail reply canonical selected product body)) :
    finish.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [prepareGuessRequest_eval _ _ _ _ _ _ _ _ _ _ _ _ hBlanks] at hMem
  have hEq : finish = prepareGuessRequestFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding := by
    simpa using hMem
  rw [hEq]
  rfl

/-- Full-configuration return when the request constructor is placed in a
larger simulator. The final caller jump is charged, and no tape is reloaded. -/
theorem prepareGuessRequest_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ prepareGuessRequest.length → pre.length + pc ≠ returnPc)
    (before beforeOutput : List (Option Bool))
    (n : Nat) (instanceBits tupleTail reply canonical selected product body : List Bool)
    (padding outputBlanks : Nat) (hBlanks : outputBlanks ≤ instanceBits.length + 1) :
    evalReturnWithin (Program.withSubroutine pre prepareGuessRequest suffix returnPc) returnPc
      ((prepareGuessRequestStart before beforeOutput n instanceBits tupleTail reply canonical selected product body padding outputBlanks).rebasePc pre.length)
      (prepareGuessRequestSteps n instanceBits tupleTail reply canonical selected product body) =
      PMF.pure ((prepareGuessRequestFinish before beforeOutput n instanceBits tupleTail reply canonical selected product body padding).resumeAt returnPc) := by
  rw [Program.evalReturnWithin_configuration_eq_of_halted pre prepareGuessRequest suffix returnPc hLayout
      (prepareGuessRequestStart before beforeOutput n instanceBits tupleTail reply canonical selected product body padding outputBlanks)
      (by change 0 ≤ prepareGuessRequest.length; exact Nat.zero_le _) rfl
      (prepareGuessRequestSteps n instanceBits tupleTail reply canonical selected product body)
      (prepareGuessRequest_haltsFrom before beforeOutput n instanceBits tupleTail reply canonical selected product body padding outputBlanks hBlanks),
    prepareGuessRequest_eval _ _ _ _ _ _ _ _ _ _ _ _ hBlanks, PMF.pure_map]

/-- The complete request constructor stops on arbitrary finite caller tapes.
Each subsequent subroutine receives the actual tapes returned by the prior
one. Malformed fields do not imply successful protocol serialization or
readiness for a source invocation; those are separate layout obligations. -/
theorem prepareGuessRequest_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000000000000000000000 * (input.cells + output.cells) + 1000000000000000000000000 ∧
      RunsFor prepareGuessRequest
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨prefixed, prefixTime, hPrefixTime, prefixRun, prefixHalt⟩ :=
    prepareGuessPrefix_terminates_from_anyTape input output
  obtain ⟨positioned, positionTime, hPositionTime, positionRun, positionHalt, _positionOutput⟩ :=
    seekGuessInputScratch_terminates_from_anyTape prefixed.inputTape prefixed.outputTape
  obtain ⟨framed, frameTime, hFrameTime, frameRun, frameHalt⟩ :=
    frameSavedMessage_terminates_from_anyTape positioned.inputTape positioned.outputTape
  have hPrefix := prefixRun.withSubroutine_halted_of_closed
    [] prepareGuessPrefix (seekGuessInputScratch.asSubroutine 86 120 ++ frameSavedMessage.asSubroutine 120 182 ++ [.halt]) 86
    (by change 0 < 85; decide) rfl prefixHalt prepareGuessPrefix_control_closed
  change RunsFor prepareGuessRequest
    ({ inputTape := input, outputTape := output } : Configuration) (prefixed.resumeAt 86) prefixTime at hPrefix
  have hPosition := positionRun.withSubroutine_halted_of_closed
    (prepareGuessPrefix.asSubroutine 0 86) seekGuessInputScratch
    (frameSavedMessage.asSubroutine 120 182 ++ [.halt]) 120
    (by change 0 < 33; decide) rfl positionHalt seekGuessInputScratch_control_closed
  change RunsFor prepareGuessRequest (prefixed.resumeAt 86) (positioned.resumeAt 120) positionTime at hPosition
  have leading := hPrefix.trans hPosition
  have hFrame := frameRun.withSubroutine_halted_of_closed
    (prepareGuessPrefix.asSubroutine 0 86 ++ seekGuessInputScratch.asSubroutine 86 120)
    frameSavedMessage [.halt] 182
    (by change 0 < 61; decide) rfl frameHalt frameSavedMessage_control_closed
  change RunsFor prepareGuessRequest (positioned.resumeAt 120) (framed.resumeAt 182) frameTime at hFrame
  let finish : Configuration := { framed with pc := 182, halted := true }
  have last : Step prepareGuessRequest (framed.resumeAt 182) finish := by
    have code : prepareGuessRequest[182]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, prefixTime + positionTime + frameTime + 1, ?_,
    RunsFor.succ (leading.trans hFrame) last, rfl⟩
  have prefixStorage := GuardedCompiler.sourceStorage_le_of_run prefixRun
  have positionStorage := GuardedCompiler.sourceStorage_le_of_run leading
  change prefixed.inputTape.cells + prefixed.outputTape.cells ≤ input.cells + output.cells + prefixTime at prefixStorage
  change positioned.inputTape.cells + positioned.outputTape.cells ≤ input.cells + output.cells + (prefixTime + positionTime) at positionStorage
  omega

theorem prepareGuessRequest_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor prepareGuessRequest
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (1000000000000000000000000 * (input.cells + output.cells) + 1000000000000000000000000)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ := prepareGuessRequest_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted prepareGuessRequest_no_randomBit hBound finish trace


/-- Actual public-prefix preparation, even on malformed frames, retains a
suffix of the saved five bit blocks. The subsequent five native scans reach
blank input scratch and preserve the prepared output frontier. -/
theorem seekGuessInputScratch_separated_frontier_after_publicPrefix
    (input : Tape) (beforeOutput : List (Option Bool)) (outputBlanks : Nat)
    (prefixFinish : Configuration) (prefixTime : Nat)
    (prefixRun : RunsFor preparePublicPrefixContext
      ({ inputTape := input,
         outputTape := { left := beforeOutput, right := List.replicate outputBlanks none } } : Configuration)
      prefixFinish prefixTime)
    (prefixHalt : prefixFinish.halted = true)
    (first second third fourth fifth : List Bool) (padding count : Nat)
    (hRight : input.right =
      (first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: fifth.map some ++ none ::
          List.replicate padding none).drop count) :
    ∃ finish used afterInput inputRemaining afterOutput outputRemaining,
      used ≤ 10000 * (prefixFinish.inputTape.cells + prefixFinish.outputTape.cells) + 10000 ∧
      RunsFor seekGuessInputScratch
        ({ inputTape := prefixFinish.inputTape, outputTape := prefixFinish.outputTape } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := none :: afterInput, right := List.replicate inputRemaining none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate outputRemaining none } := by
  obtain ⟨target, targetTime, savedInput, afterOutput, outputRemaining,
    _hBound, targetRun, targetHalt, targetCurrent, _targetLeft, targetOutput, offset, targetRight⟩ :=
    preparePublicPrefixContext_terminates_with_suffix_layout input beforeOutput outputBlanks
  have hFinish := prefixRun.halted_finish_eq_of_no_randomBit
    targetRun prefixHalt targetHalt preparePublicPrefixContext_no_randomBit
  subst prefixFinish
  have hSuffix : target.inputTape.right =
      (first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: fifth.map some ++ none ::
          List.replicate padding none).drop (count + offset) := by
    rw [targetRight, hRight, List.drop_drop]
  obtain ⟨finish, used, afterInput, inputRemaining, hBound, run, hHalted, hOutput, hInput⟩ :=
    seekGuessInputScratch_terminates_with_separated_frontier target.inputTape target.outputTape
      first second third fourth fifth padding (count + offset) true targetCurrent hSuffix
  exact ⟨finish, used, afterInput, inputRemaining, afterOutput, outputRemaining,
    hBound, run, hHalted, hInput, hOutput.trans targetOutput⟩

/-- The same continuation certificate for callers that do not need to
inspect the retained blank separator immediately behind the input head. -/
theorem seekGuessInputScratch_frontier_after_publicPrefix
    (input : Tape) (beforeOutput : List (Option Bool)) (outputBlanks : Nat)
    (prefixFinish : Configuration) (prefixTime : Nat)
    (prefixRun : RunsFor preparePublicPrefixContext
      ({ inputTape := input,
         outputTape := { left := beforeOutput, right := List.replicate outputBlanks none } } : Configuration)
      prefixFinish prefixTime)
    (prefixHalt : prefixFinish.halted = true)
    (first second third fourth fifth : List Bool) (padding count : Nat)
    (hRight : input.right =
      (first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: fifth.map some ++ none ::
          List.replicate padding none).drop count) :
    ∃ finish used afterInput inputRemaining afterOutput outputRemaining,
      used ≤ 10000 * (prefixFinish.inputTape.cells + prefixFinish.outputTape.cells) + 10000 ∧
      RunsFor seekGuessInputScratch
        ({ inputTape := prefixFinish.inputTape, outputTape := prefixFinish.outputTape } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate inputRemaining none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate outputRemaining none } := by
  obtain ⟨finish, used, afterInput, inputRemaining, afterOutput, outputRemaining,
    hBound, run, hHalted, hInput, hOutput⟩ :=
    seekGuessInputScratch_separated_frontier_after_publicPrefix input beforeOutput outputBlanks
      prefixFinish prefixTime prefixRun prefixHalt first second third fourth fifth padding count hRight
  exact ⟨finish, used, none :: afterInput, inputRemaining, afterOutput, outputRemaining,
    hBound, run, hHalted, hInput, hOutput⟩

/-- Saved-message framing can continue from the actual five-scan return
after public-prefix assembly. Both tapes end at fresh blank frontiers, even
when the five retained bit blocks contain malformed fields or replies. The
explicit suffix premise is a caller invariant, not an assumption that the
input has a valid cryptographic encoding. -/
theorem frameSavedMessage_frontier_after_guessScratch
    (input : Tape) (beforeOutput : List (Option Bool)) (outputBlanks : Nat)
    (prefixFinish : Configuration) (prefixTime : Nat)
    (prefixRun : RunsFor preparePublicPrefixContext
      ({ inputTape := input,
         outputTape := { left := beforeOutput, right := List.replicate outputBlanks none } } : Configuration)
      prefixFinish prefixTime)
    (prefixHalt : prefixFinish.halted = true)
    (first second third fourth fifth : List Bool) (padding count : Nat)
    (hRight : input.right =
      (first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: fifth.map some ++ none ::
          List.replicate padding none).drop count)
    (scratchFinish : Configuration) (scratchTime : Nat)
    (scratchRun : RunsFor seekGuessInputScratch
      ({ inputTape := prefixFinish.inputTape, outputTape := prefixFinish.outputTape } : Configuration)
      scratchFinish scratchTime)
    (scratchHalt : scratchFinish.halted = true) :
    ∃ finish used afterInput inputRemaining afterOutput outputRemaining,
      used ≤ 1000000 * (scratchFinish.inputTape.cells + scratchFinish.outputTape.cells) + 1000000 ∧
      RunsFor frameSavedMessage
        ({ inputTape := scratchFinish.inputTape, outputTape := scratchFinish.outputTape } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate inputRemaining none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate outputRemaining none } := by
  obtain ⟨positioned, positionedTime, savedInput, inputBlanks, savedOutput, outputBlanks',
    _hBound, positionedRun, positionedHalt, hInput, hOutput⟩ :=
    seekGuessInputScratch_separated_frontier_after_publicPrefix input beforeOutput outputBlanks
      prefixFinish prefixTime prefixRun prefixHalt first second third fourth fifth padding count hRight
  have hFinish := scratchRun.halted_finish_eq_of_no_randomBit positionedRun
    scratchHalt positionedHalt seekGuessInputScratch_no_randomBit
  subst scratchFinish
  obtain ⟨finish, used, afterInput, inputRemaining, afterOutput, outputRemaining,
    hBound, run, hHalted, hFinishInput, hFinishOutput⟩ :=
    frameSavedMessage_terminates_with_fresh_tapes savedInput savedOutput inputBlanks outputBlanks'
  refine ⟨finish, used, afterInput, inputRemaining, afterOutput, outputRemaining,
    ?_, ?_, hHalted, hFinishInput, hFinishOutput⟩
  · simpa only [hInput, hOutput] using hBound
  · simpa only [hInput, hOutput] using run

/-- Fresh physical input/output frontiers suffice for the entire native
guess-request constructor. The saved cells may be malformed: restoration
exposes five blocks, public-prefix preparation retains their suffix, the
five scans supply a reserved scratch separator, and saved-body framing
returns both heads to fresh blank frontiers. -/
theorem prepareGuessRequest_terminates_from_fresh_tapes
    (savedInput savedOutput : List (Option Bool)) (inputBlanks outputBlanks : Nat) :
    let input : Tape := { left := savedInput, right := List.replicate inputBlanks none }
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    ∃ finish used afterInput remainingInput afterOutput remainingOutput,
      used ≤ 1000000000000000000000000 * (input.cells + output.cells) + 1000000000000000000000000 ∧
      RunsFor prepareGuessRequest
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate remainingInput none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate remainingOutput none } := by
  dsimp only
  let input : Tape := { left := savedInput, right := List.replicate inputBlanks none }
  let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
  obtain ⟨prefixReady, prefixTime, a, b, c, d, e, prefixAfter, prefixBlanks, count,
    hPrefixTime, prefixRun, prefixHalt, prefixCurrent, prefixOutput, prefixRight⟩ :=
    prepareGuessPrefix_terminates_from_fresh_tapes savedInput savedOutput inputBlanks outputBlanks
  obtain ⟨scratchReady, scratchTime, scratchAfter, scratchBlanks,
    hScratchTime, scratchRun, scratchHalt, scratchOutput, scratchInput⟩ :=
    seekGuessInputScratch_terminates_with_separated_frontier prefixReady.inputTape prefixReady.outputTape
      a b c d e inputBlanks count true prefixCurrent prefixRight
  have hScratchOutput := scratchOutput.trans prefixOutput
  obtain ⟨framed, frameTime, afterInput, remainingInput, afterOutput, remainingOutput,
    hFrameTime, frameRun, frameHalt, frameInput, frameOutput⟩ :=
    frameSavedMessage_terminates_with_fresh_tapes scratchAfter prefixAfter scratchBlanks prefixBlanks
  have actualFrame : RunsFor frameSavedMessage
      ({ inputTape := scratchReady.inputTape, outputTape := scratchReady.outputTape } : Configuration)
      framed frameTime := by
    rw [scratchInput, hScratchOutput]
    exact frameRun
  have hPrefix := prefixRun.withSubroutine_halted_of_closed
    [] prepareGuessPrefix (seekGuessInputScratch.asSubroutine 86 120 ++
      frameSavedMessage.asSubroutine 120 182 ++ [.halt]) 86
    (by change 0 < 85; decide) rfl prefixHalt prepareGuessPrefix_control_closed
  change RunsFor prepareGuessRequest
    ({ inputTape := input, outputTape := output } : Configuration) (prefixReady.resumeAt 86) prefixTime at hPrefix
  have hScratch := scratchRun.withSubroutine_halted_of_closed
    (prepareGuessPrefix.asSubroutine 0 86) seekGuessInputScratch
    (frameSavedMessage.asSubroutine 120 182 ++ [.halt]) 120
    (by change 0 < 33; decide) rfl scratchHalt seekGuessInputScratch_control_closed
  change RunsFor prepareGuessRequest (prefixReady.resumeAt 86) (scratchReady.resumeAt 120) scratchTime at hScratch
  have toFrame := hPrefix.trans hScratch
  have hFrame := actualFrame.withSubroutine_halted_of_closed
    (prepareGuessPrefix.asSubroutine 0 86 ++ seekGuessInputScratch.asSubroutine 86 120)
    frameSavedMessage [.halt] 182
    (by change 0 < 61; decide) rfl frameHalt frameSavedMessage_control_closed
  change RunsFor prepareGuessRequest (scratchReady.resumeAt 120) (framed.resumeAt 182) frameTime at hFrame
  let finish : Configuration := { framed with pc := 182, halted := true }
  have last : Step prepareGuessRequest (framed.resumeAt 182) finish := by
    have code : prepareGuessRequest[182]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, prefixTime + scratchTime + frameTime + 1, afterInput, remainingInput,
    afterOutput, remainingOutput, ?_, RunsFor.succ (toFrame.trans hFrame) last, rfl, frameInput, frameOutput⟩
  have prefixStorage := GuardedCompiler.sourceStorage_le_of_run prefixRun
  change prefixReady.inputTape.cells + prefixReady.outputTape.cells ≤
    input.cells + output.cells + prefixTime at prefixStorage
  have scratchStorage := GuardedCompiler.sourceStorage_le_of_run toFrame
  change scratchReady.inputTape.cells + scratchReady.outputTape.cells ≤
    input.cells + output.cells + (prefixTime + scratchTime) at scratchStorage
  change prefixTime ≤ 1000000000000 * (input.cells + output.cells) + 1000000000000 at hPrefixTime
  rw [← scratchInput, ← hScratchOutput] at hFrameTime
  change prefixTime + scratchTime + frameTime + 1 ≤
    1000000000000000000000000 * (input.cells + output.cells) + 1000000000000000000000000
  omega

end Machine
