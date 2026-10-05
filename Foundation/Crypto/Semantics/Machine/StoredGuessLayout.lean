import Foundation.Crypto.Semantics.Machine.StoredGuessCompletion
import Foundation.Crypto.Semantics.Machine.ReturnedResultInvocation

namespace Machine.GuardedCompiler

open VirtualCell

/-- Bit cells of the retained guarded input region and original request.
This describes existing cells for a subsequent charged erasure; it is not
an instruction which materializes a virtual region in one transition. -/
def storedSourceScratchBits (request : List Bool) (input : Tape) : List Bool :=
  request ++ [false, true] ++ ((encodedLeftCells input.left).filterMap id).reverse ++ encodedRightBits input

private theorem encodedLeftCells_map_some (cells : List (Option Bool)) :
    ((encodedLeftCells cells).filterMap id).map some = encodedLeftCells cells := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp only [id_eq] at ih
      simp only [encodedLeftCells, List.filterMap_cons, id_eq, List.map_cons]
      rw [ih]

/-- A retained guarded source region is one contiguous physical bit block,
even when its logical source cells are blanks. The explicit caller blank
following the original request is the block's protected boundary. -/
theorem scratchPrefix_as_storedBlock (request : List Bool) (before : List (Option Bool)) (input : Tape) :
    scratchPrefix (request.reverse.map some ++ none :: before) input =
      none :: (storedSourceScratchBits request input).reverse.map some ++ none :: before := by
  simp [scratchPrefix, storedSourceScratchBits, encodeTape, VirtualCell.pairTape,
    List.reverse_append, List.map_append, List.map_reverse,
    List.append_assoc]
  simpa only [id_eq] using (encodedLeftCells_map_some input.left).symm

theorem storedSourceScratchBits_length (request : List Bool) (input : Tape) :
    (storedSourceScratchBits request input).length = request.length + 2 * input.cells + 2 := by
  have hLength := congrArg List.length (encodedLeftCells_map_some input.left)
  simp only [List.length_map, encodedLeftCells_length] at hLength
  simp only [storedSourceScratchBits, List.length_append, List.length_cons, List.length_nil,
    List.length_reverse, hLength, encodedRightBits_length, Tape.cells]
  omega

theorem rawResultFrom_output_storedBlocks (source : Program) (request : List Bool)
    (before savedInput : List (Option Bool)) (c : Configuration) :
    ((rawResultFrom source request (none :: before) savedInput c).swapTapes).outputTape.left =
      savedOutputBlocks [c.outputBits, storedSourceScratchBits request c.inputTape] ++ before := by
  change c.outputBits.reverse.map some ++ scratchPrefix (request.reverse.map some ++ none :: before) c.inputTape = _
  rw [scratchPrefix_as_storedBlock]
  simp [savedOutputBlocks, List.append_assoc]

/-- The four scratch blocks preceding the challenge on the selected-message
tape: canonical normalizer output, its guarded region, the choose response,
and the guarded choose region. All are actual returned source cells. -/
def storedGuessBackBlocks (chooseRequest normalizeRequest : List Bool)
    (chooseResult normalizeResult : Configuration) : List (List Bool) :=
  [normalizeResult.outputBits, storedSourceScratchBits normalizeRequest normalizeResult.inputTape,
   chooseResult.outputBits, storedSourceScratchBits chooseRequest chooseResult.inputTape]

theorem normalizerResult_stored_back_layout (chooseSource normalizeSource : Program)
    (chooseRequest normalizeRequest : List Bool) (chooseSaved normalizeSaved : List (Option Bool))
    (chooseResult normalizeResult : Configuration) :
    let chooseReturn := (rawResultFrom chooseSource chooseRequest [none] chooseSaved chooseResult).swapTapes
    ((rawResultFrom normalizeSource normalizeRequest (none :: chooseReturn.outputTape.left)
      normalizeSaved normalizeResult).swapTapes).outputTape.left =
      savedOutputBlocks (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult) := by
  dsimp only
  rw [rawResultFrom_output_storedBlocks, rawResultFrom_output_storedBlocks]
  simp [savedOutputBlocks, storedGuessBackBlocks, List.append_assoc]

/-- The eight physical blocks between the already erased guess copy and
the challenge. Empty entries represent two consecutive actual separators;
they are scanned and charged rather than silently normalized away. -/
def storedGuessFrontBlocks (guessRequest multiplyRequest body selected : List Bool)
    (multiplyResult guessResult : Configuration) : List (List Bool) :=
  [storedSourceScratchBits guessRequest guessResult.inputTape, [], body,
   frame multiplyResult.outputBits, multiplyResult.outputBits,
   storedSourceScratchBits multiplyRequest multiplyResult.inputTape, [], selected]

/-- Actual multiply and guess results expose precisely the fixed eight
block layout used by the native challenge locator. Both results are the
configurations returned by the real guarded calls, not supplied reply bits. -/
theorem rawGuessResult_stored_layout (multiplySource guessSource : Program)
    (multiplyRequest guessRequest body selected : List Bool)
    (beforeInput savedInput : List (Option Bool)) (boundary : Option Bool)
    (back : List (List Bool)) (challenge : Bool) (multiplyResult guessResult : Configuration) :
    let productReturn := returnedFrameResult multiplySource multiplyRequest
      (none :: none :: selected.reverse.map some ++ none :: some challenge :: savedOutputBlocks back)
      savedInput multiplyResult
    ((rawResultFrom guessSource guessRequest
      (none :: none :: body.reverse.map some ++ none :: productReturn.outputTape.left)
      (boundary :: beforeInput) guessResult).swapTapes).resumeAt 0 =
      prepareStoredGuessStart beforeInput boundary
        (storedGuessFrontBlocks guessRequest multiplyRequest body selected multiplyResult guessResult)
        back challenge guessResult.outputBits
        (2 * guessResult.outputTape.cells + 2 - guessResult.outputBits.length) 0 := by
  dsimp only
  rw [rawResultFrom_rewindStoredGuessStart]
  simp only [returnedFrameResult, frameReturnedResultFinish]
  rw [show multiplyRequest.reverse.map some ++
      (none :: none :: selected.reverse.map some ++ none :: some challenge :: savedOutputBlocks back) =
      multiplyRequest.reverse.map some ++ none ::
        (none :: selected.reverse.map some ++ none :: some challenge :: savedOutputBlocks back) by rfl,
    scratchPrefix_as_storedBlock]
  rw [show guessRequest.reverse.map some ++
      (none :: none :: body.reverse.map some ++ none ::
        ((frame multiplyResult.outputBits).reverse.map some ++ none ::
          (multiplyResult.outputBits.reverse.map some ++
            (none :: (storedSourceScratchBits multiplyRequest multiplyResult.inputTape).reverse.map some ++
              none :: (none :: selected.reverse.map some ++ none :: some challenge :: savedOutputBlocks back))))) =
      guessRequest.reverse.map some ++ none ::
        (none :: body.reverse.map some ++ none ::
          ((frame multiplyResult.outputBits).reverse.map some ++ none ::
            (multiplyResult.outputBits.reverse.map some ++ none ::
              (storedSourceScratchBits multiplyRequest multiplyResult.inputTape).reverse.map some ++
                none :: none :: selected.reverse.map some ++ none :: some challenge :: savedOutputBlocks back))) by
      simp [List.append_assoc]]
  -- The erased reply's boundary is the leading blank of this scratch prefix.
  have hScratch := scratchPrefix_as_storedBlock guessRequest
    (none :: body.reverse.map some ++ none ::
      (frame multiplyResult.outputBits).reverse.map some ++ none ::
      multiplyResult.outputBits.reverse.map some ++ none ::
      (storedSourceScratchBits multiplyRequest multiplyResult.inputTape).reverse.map some ++
      none :: none :: selected.reverse.map some ++ none :: some challenge :: savedOutputBlocks back) guessResult.inputTape
  simp only [scratchPrefix] at hScratch
  have hTail := congrArg List.tail hScratch
  simpa [prepareStoredGuessStart, storedGuessFrontBlocks, savedOutputBlocks, List.append_assoc] using
    congrArg (fun saved => rewindStoredGuessStart beforeInput saved boundary guessResult.outputBits
      (2 * guessResult.outputTape.cells + 2 - guessResult.outputBits.length) 0) hTail

/-- Apply the complete native terminal code to the actual guarded guess
result. The protected challenge and multiplication scratch are carried
through the physical caller prefixes; no fresh loading step supplies them. -/
theorem rawGuessResult_finishStoredGuess_eval (multiplySource guessSource : Program)
    (multiplyRequest guessRequest body selected : List Bool)
    (beforeInput savedInput : List (Option Bool)) (boundary : Option Bool)
    (back : List (List Bool)) (challenge : Bool) (multiplyResult guessResult : Configuration) :
    let productReturn := returnedFrameResult multiplySource multiplyRequest
      (none :: none :: selected.reverse.map some ++ none :: some challenge :: savedOutputBlocks back)
      savedInput multiplyResult
    (evalConfigWithin (finishStoredGuess 8 back.length)
      (((rawResultFrom guessSource guessRequest
        (none :: none :: body.reverse.map some ++ none :: productReturn.outputTape.left)
        (boundary :: beforeInput) guessResult).swapTapes).resumeAt 0)
      (finishStoredGuessSteps
        (storedGuessFrontBlocks guessRequest multiplyRequest body selected multiplyResult guessResult)
        back guessResult.outputBits)).map (fun c => (c.halted, c.outputBits)) =
      PMF.pure (true, [taggedGuessValue guessResult.outputBits == challenge]) := by
  dsimp only
  rw [rawGuessResult_stored_layout]
  have h := finishStoredGuess_evalResult beforeInput boundary
    (storedGuessFrontBlocks guessRequest multiplyRequest body selected multiplyResult guessResult)
    back challenge guessResult.outputBits (2 * guessResult.outputTape.cells + 2 - guessResult.outputBits.length) 0
  simpa only [storedGuessFrontBlocks, List.length_cons, List.length_nil] using h

theorem finishStoredGuess_protocol_length : (finishStoredGuess 8 4).length = 157 := by
  rw [finishStoredGuess_length]

/-- The same actual raw-return layout at a common budget, including branches
whose reply lengths and exact terminal times differ. -/
theorem rawGuessResult_finishStoredGuess_eval_of_le (multiplySource guessSource : Program)
    (multiplyRequest guessRequest body selected : List Bool)
    (beforeInput savedInput : List (Option Bool)) (boundary : Option Bool)
    (back : List (List Bool)) (challenge : Bool) (multiplyResult guessResult : Configuration)
    (budget : Nat)
    (hFits : finishStoredGuessSteps
      (storedGuessFrontBlocks guessRequest multiplyRequest body selected multiplyResult guessResult)
      back guessResult.outputBits ≤ budget) :
    let productReturn := returnedFrameResult multiplySource multiplyRequest
      (none :: none :: selected.reverse.map some ++ none :: some challenge :: savedOutputBlocks back)
      savedInput multiplyResult
    (evalConfigWithin (finishStoredGuess 8 back.length)
      (((rawResultFrom guessSource guessRequest
        (none :: none :: body.reverse.map some ++ none :: productReturn.outputTape.left)
        (boundary :: beforeInput) guessResult).swapTapes).resumeAt 0) budget).map
          (fun c => (c.halted, c.outputBits)) =
      PMF.pure (true, [taggedGuessValue guessResult.outputBits == challenge]) := by
  dsimp only
  rw [rawGuessResult_stored_layout]
  have h := finishStoredGuess_evalResult_of_le beforeInput boundary
    (storedGuessFrontBlocks guessRequest multiplyRequest body selected multiplyResult guessResult)
    back challenge guessResult.outputBits (2 * guessResult.outputTape.cells + 2 - guessResult.outputBits.length) 0 budget hFits
  simpa only [storedGuessFrontBlocks, List.length_cons, List.length_nil] using h

/-- A linear upper bound in the actual retained payloads and logical source
storage. Source storage itself has the charged trace bound proved for guarded
calls. Thus neither arbitrary scratch lengths nor replies are free inputs. -/
theorem finishStoredGuess_steps_le_sourceStorage
    (guessRequest multiplyRequest chooseRequest normalizeRequest body selected : List Bool)
    (chooseResult normalizeResult multiplyResult guessResult : Configuration) :
    finishStoredGuessSteps
      (storedGuessFrontBlocks guessRequest multiplyRequest body selected multiplyResult guessResult)
      (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult) guessResult.outputBits ≤
      20 * (guessRequest.length + multiplyRequest.length + chooseRequest.length + normalizeRequest.length +
        body.length + selected.length + sourceStorage chooseResult + sourceStorage normalizeResult +
        sourceStorage multiplyResult + sourceStorage guessResult + 1) + 200 := by
  have h := finishStoredGuess_steps_le
    (storedGuessFrontBlocks guessRequest multiplyRequest body selected multiplyResult guessResult)
    (storedGuessBackBlocks chooseRequest normalizeRequest chooseResult normalizeResult) guessResult.outputBits
  have hg := Tape.bits_length_le_cells guessResult.outputTape
  have hm := Tape.bits_length_le_cells multiplyResult.outputTape
  have hn := Tape.bits_length_le_cells normalizeResult.outputTape
  have hc := Tape.bits_length_le_cells chooseResult.outputTape
  simp only [storedGuessFrontBlocks, storedGuessBackBlocks, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    storedSourceScratchBits_length, frame, List.length_append,
    List.length_replicate, sourceStorage] at h ⊢
  simp only [Configuration.outputBits] at h ⊢
  omega

end Machine.GuardedCompiler
