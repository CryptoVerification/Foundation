import Foundation.Machine.GuessPrefixPreparation
import Foundation.Machine.StoredGuessInputScratch
import Foundation.Machine.SavedMessageFraming

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

end Machine
