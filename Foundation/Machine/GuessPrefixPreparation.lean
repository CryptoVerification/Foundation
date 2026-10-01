import Foundation.Machine.StoredGuessInputRestoration
import Foundation.Machine.ContextualPrefix

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

end Machine
