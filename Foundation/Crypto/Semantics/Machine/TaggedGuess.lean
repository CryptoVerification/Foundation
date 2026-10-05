import Foundation.Crypto.Semantics.Machine.Adversary
import Foundation.Crypto.Semantics.Machine.PolynomialTime
import Foundation.Crypto.Semantics.Machine.SubroutineProbability

namespace Machine

/-- Decode the IND-CPA guess response format `true :: [bit]`. All other
finite raw outputs, including a choose response or extra trailing bits,
produce false. Validation reads at most three input cells and uses ordinary
one-cell machine instructions. No group-element decoder is evaluated. -/
def readTaggedGuess : Program :=
  [.branch .input 11 11 1,
   .moveRight .input,
   .branch .input 11 3 7,
   .moveRight .input, .branch .input 5 11 11,
   .write .output false, .halt,
   .moveRight .input, .branch .input 9 11 11,
   .write .output true, .halt,
   .write .output false, .halt]

/-- Mathematical specification of the native tagged-bit parser. -/
def taggedGuessValue : List Bool → Bool
  | [true, bit] => bit
  | _ => false

def readTaggedGuessBudget : List Bool → Nat
  | [] | false :: _ => 3
  | [true] => 5
  | true :: _ :: _ => 7

def readTaggedGuessStart (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits bits with left := beforeInput },
    outputTape := { left := beforeOutput } }

/-- Explicit final head position and all retained caller data. The output
head remains on the one written result bit. No surrounding tape is reset. -/
def readTaggedGuessFinish (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) : Configuration :=
  let input := (readTaggedGuessStart beforeInput beforeOutput bits).inputTape
  { pc := match bits with
      | [true, false] => 6
      | [true, true] => 10
      | _ => 12,
    inputTape := match bits with
      | [true] => input.moveRight
      | true :: _ :: _ => input.moveRight.moveRight
      | _ => input,
    outputTape := { left := beforeOutput, current := some (taggedGuessValue bits) },
    halted := true }

theorem readTaggedGuess_budget_le (bits : List Bool) :
    readTaggedGuessBudget bits ≤ 7 := by
  match bits with
  | [] => decide
  | false :: _ => simp [readTaggedGuessBudget]
  | [true] => decide
  | true :: _ :: _ => simp [readTaggedGuessBudget]

theorem readTaggedGuess_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ readTaggedGuess := by simp [readTaggedGuess]

/-- The state immediately before the explicit halt. It is still active,
so the inspected transition budget contains no post-halt padding. -/
theorem readTaggedGuess_eval_before_halt (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) :
    evalConfigWithin readTaggedGuess (readTaggedGuessStart beforeInput beforeOutput bits)
      (readTaggedGuessBudget bits - 1) =
      PMF.pure { readTaggedGuessFinish beforeInput beforeOutput bits with halted := false } := by
  match bits with
  | [] =>
      simp [evalConfigWithin, readTaggedGuessBudget, readTaggedGuessStart,
        readTaggedGuessFinish, taggedGuessValue, stepPMF, next, readTaggedGuess,
        Tape.ofBits, Instruction.next, Configuration.tape,
        Configuration.updateTape, Configuration.advance, Tape.write]
  | false :: rest =>
      simp [evalConfigWithin, readTaggedGuessBudget, readTaggedGuessStart,
        readTaggedGuessFinish, taggedGuessValue, stepPMF, next, readTaggedGuess,
        Tape.ofBits, Instruction.next, Configuration.tape,
        Configuration.updateTape, Configuration.advance, Tape.write]
  | [true] =>
      simp [evalConfigWithin, readTaggedGuessBudget, readTaggedGuessStart,
        readTaggedGuessFinish, taggedGuessValue, stepPMF, next, readTaggedGuess,
        Tape.ofBits, Instruction.next, Configuration.tape,
        Configuration.updateTape, Configuration.advance, Tape.write, Tape.moveRight]
  | true :: bit :: rest =>
      cases bit <;> cases rest with
      | nil =>
          simp [evalConfigWithin, readTaggedGuessBudget, readTaggedGuessStart,
            readTaggedGuessFinish, taggedGuessValue, stepPMF, next, readTaggedGuess,
            Tape.ofBits, Instruction.next, Configuration.tape,
            Configuration.updateTape, Configuration.advance, Tape.write, Tape.moveRight]
      | cons first tail =>
          cases first <;>
            simp [evalConfigWithin, readTaggedGuessBudget, readTaggedGuessStart,
              readTaggedGuessFinish, taggedGuessValue, stepPMF, next, readTaggedGuess,
              Tape.ofBits, Instruction.next, Configuration.tape,
              Configuration.updateTape, Configuration.advance, Tape.write, Tape.moveRight]

/-- Exact native transition trace, including the final halt. The shorter
three- and five-step rejection paths do not receive hidden padding. -/
theorem readTaggedGuess_runs (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) :
    RunsFor readTaggedGuess (readTaggedGuessStart beforeInput beforeOutput bits)
      (readTaggedGuessFinish beforeInput beforeOutput bits) (readTaggedGuessBudget bits) := by
  let finish := readTaggedGuessFinish beforeInput beforeOutput bits
  let before : Configuration := { finish with halted := false }
  have hPrefix : PaddedRunsFor readTaggedGuess
      (readTaggedGuessStart beforeInput beforeOutput bits) before (readTaggedGuessBudget bits - 1) := by
    apply (mem_support_evalConfigWithin_iff _ _ _ _).mp
    rw [readTaggedGuess_eval_before_halt]
    simp [before, finish]
  have hInstruction : readTaggedGuess[finish.pc]? = some .halt := by
    dsimp only [finish]
    match bits with
    | [] => rfl
    | false :: _ => rfl
    | [true] => rfl
    | true :: bit :: rest => cases bit <;> cases rest <;> rfl
  have hHalt : Step readTaggedGuess before finish := by
    simp only [Step, successors, next, before, Bool.false_eq_true, ↓reduceIte,
      hInstruction, Instruction.next, List.mem_singleton]
    simp [finish, readTaggedGuessFinish]
  have hPositive : 0 < readTaggedGuessBudget bits := by
    match bits with
    | [] => decide
    | false :: _ => simp [readTaggedGuessBudget]
    | [true] => decide
    | true :: _ :: _ => simp [readTaggedGuessBudget]
  convert RunsFor.succ (hPrefix.toRunsFor_of_running rfl) hHalt using 1
  omega

/-- Complete native configuration semantics on every finite input. The
small constant bounds include the bit write and explicit halt on each path. -/
theorem readTaggedGuess_eval (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) :
    evalConfigWithin readTaggedGuess (readTaggedGuessStart beforeInput beforeOutput bits)
      (readTaggedGuessBudget bits) =
      PMF.pure (readTaggedGuessFinish beforeInput beforeOutput bits) :=
  (readTaggedGuess_runs beforeInput beforeOutput bits).evalConfigWithin_eq_pure_of_no_randomBit
    readTaggedGuess_no_randomBit

theorem readTaggedGuess_haltsFrom (beforeInput beforeOutput : List (Option Bool))
    (bits : List Bool) :
    ∀ finish, PaddedRunsFor readTaggedGuess
      (readTaggedGuessStart beforeInput beforeOutput bits) finish (readTaggedGuessBudget bits) →
        finish.halted = true := by
  intro finish run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [readTaggedGuess_eval] at hMem
  have hFinish : finish = readTaggedGuessFinish beforeInput beforeOutput bits := by
    simpa using hMem
  rw [hFinish]
  rfl

theorem readTaggedGuess_haltsWithin (bits : List Bool) :
    HaltsWithin readTaggedGuess bits 7 := by
  have hStart : readTaggedGuessStart [] [] bits = Configuration.initial bits := by
    cases bits <;> rfl
  have hHalts := readTaggedGuess_haltsFrom [] [] bits
  rw [hStart] at hHalts
  exact HaltsWithin.mono hHalts (readTaggedGuess_budget_le bits)

theorem readTaggedGuessFinish_outputBits (bits : List Bool) :
    (readTaggedGuessFinish [] [] bits).outputBits = [taggedGuessValue bits] := by
  simp [readTaggedGuessFinish, Configuration.outputBits, Tape.bits]

theorem readTaggedGuess_evalWithin (bits : List Bool) :
    evalWithin readTaggedGuess bits 7 = PMF.pure (some [taggedGuessValue bits]) := by
  have hStart : readTaggedGuessStart [] [] bits = Configuration.initial bits := by
    cases bits <;> rfl
  have hHalts := readTaggedGuess_haltsFrom [] [] bits
  rw [hStart] at hHalts
  rw [evalWithin_eq_of_haltsWithin readTaggedGuess bits 7 (readTaggedGuessBudget bits)
    (readTaggedGuess_haltsWithin bits) hHalts]
  change (evalConfigWithin readTaggedGuess (Configuration.initial bits)
    (readTaggedGuessBudget bits)).map _ = _
  rw [← hStart, readTaggedGuess_eval]
  simp only [PMF.map, PMF.pure_bind]
  simp only [readTaggedGuessFinish]
  exact congrArg (fun value => PMF.pure (some value)) (readTaggedGuessFinish_outputBits bits)

/-- A constant worst-case step bound in total input length, covering
malformed and excessively long outputs as well as the two valid bit codes. -/
theorem readTaggedGuess_polynomialTime : PolynomialTime readTaggedGuess :=
  ⟨fun _ => 7, PolynomiallyBounded.const 7, readTaggedGuess_haltsWithin⟩

theorem readTaggedGuess_control_closed (c d : Configuration)
    (hPc : c.pc < readTaggedGuess.length) (step : Step readTaggedGuess c d)
    (_hRunning : d.halted = false) : d.pc < readTaggedGuess.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 13 at hPc
  change d.pc < 13
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, readTaggedGuess,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

theorem readTaggedGuess_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (bits : List Bool) :
    evalConfigWithin (Program.withSubroutine pre readTaggedGuess suffix returnPc)
      ((readTaggedGuessStart beforeInput beforeOutput bits).rebasePc pre.length)
      (readTaggedGuessBudget bits) =
      PMF.pure ((readTaggedGuessFinish beforeInput beforeOutput bits).resumeAt returnPc) :=
  (readTaggedGuess_runs beforeInput beforeOutput bits).evalConfigWithin_withSubroutine_halted_of_closed
    pre readTaggedGuess suffix returnPc (by simp [readTaggedGuessStart, readTaggedGuess])
    rfl rfl readTaggedGuess_control_closed readTaggedGuess_no_randomBit

/-- Compare the current output bit with the bit immediately to its left.
The old guess cell is explicitly erased before moving left. The previous
bit is then overwritten with the equality result. Thus a saved challenge
and fresh guess become one DDH result without an uncharged tape reset. -/
def matchPreviousOutputBit : Program :=
  [.branch .output 9 1 4,
   .erase .output, .moveLeft .output, .branch .output 9 7 9,
   .erase .output, .moveLeft .output, .branch .output 9 9 7,
   .write .output true, .halt,
   .write .output false, .halt]

def matchPreviousOutputBitStart (input : Tape) (beforeOutput : List (Option Bool))
    (challenge guess : Bool) : Configuration :=
  { inputTape := input,
    outputTape := { left := some challenge :: beforeOutput, current := some guess } }

def matchPreviousOutputBitFinish (input : Tape) (beforeOutput : List (Option Bool))
    (challenge guess : Bool) : Configuration :=
  { pc := if guess == challenge then 8 else 10,
    inputTape := input,
    outputTape := { left := beforeOutput, current := some (guess == challenge), right := [none] },
    halted := true }

theorem matchPreviousOutputBit_runs (input : Tape) (beforeOutput : List (Option Bool))
    (challenge guess : Bool) :
    RunsFor matchPreviousOutputBit
      (matchPreviousOutputBitStart input beforeOutput challenge guess)
      (matchPreviousOutputBitFinish input beforeOutput challenge guess) 6 := by
  let start := matchPreviousOutputBitStart input beforeOutput challenge guess
  let selected : Configuration := { start with pc := if guess then 4 else 1 }
  let erased : Configuration :=
    { selected with
      pc := if guess then 5 else 2,
      outputTape := selected.outputTape.write none }
  let shifted : Configuration :=
    { erased with
      pc := if guess then 6 else 3,
      outputTape := erased.outputTape.moveLeft }
  let chosen : Configuration := { shifted with pc := if guess == challenge then 7 else 9 }
  let written : Configuration :=
    { chosen with
      pc := if guess == challenge then 8 else 10,
      outputTape := chosen.outputTape.write (some (guess == challenge)) }
  have hSelect : Step matchPreviousOutputBit start selected := by
    cases guess <;> simp [Step, successors, next, matchPreviousOutputBit, start, selected,
      matchPreviousOutputBitStart, Instruction.next, Configuration.tape]
  have hErase : Step matchPreviousOutputBit selected erased := by
    cases guess <;> simp [Step, successors, next, matchPreviousOutputBit, start, selected,
      erased, matchPreviousOutputBitStart, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hShift : Step matchPreviousOutputBit erased shifted := by
    cases guess <;> simp [Step, successors, next, matchPreviousOutputBit, start, selected,
      erased, shifted, matchPreviousOutputBitStart, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hChoose : Step matchPreviousOutputBit shifted chosen := by
    cases challenge <;> cases guess <;>
      simp [Step, successors, next, matchPreviousOutputBit, start, selected, erased, shifted,
        chosen, matchPreviousOutputBitStart, Instruction.next, Configuration.tape,
        Tape.write, Tape.moveLeft]
  have hWrite : Step matchPreviousOutputBit chosen written := by
    cases challenge <;> cases guess <;>
      simp [Step, successors, next, matchPreviousOutputBit, start, selected, erased, shifted,
        chosen, written, matchPreviousOutputBitStart, Instruction.next,
        Configuration.updateTape, Configuration.advance]
  have hHalt : Step matchPreviousOutputBit written
      (matchPreviousOutputBitFinish input beforeOutput challenge guess) := by
    cases challenge <;> cases guess <;>
      simp [Step, successors, next, matchPreviousOutputBit, start, selected, erased, shifted,
        chosen, written, matchPreviousOutputBitStart, matchPreviousOutputBitFinish,
        Instruction.next, Tape.write, Tape.moveLeft]
  exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
    (RunsFor.succ (RunsFor.succ (RunsFor.zero _) hSelect) hErase) hShift) hChoose) hWrite) hHalt

theorem matchPreviousOutputBit_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ matchPreviousOutputBit := by simp [matchPreviousOutputBit]

theorem matchPreviousOutputBit_control_closed (c d : Configuration)
    (hPc : c.pc < matchPreviousOutputBit.length) (step : Step matchPreviousOutputBit c d)
    (_hRunning : d.halted = false) : d.pc < matchPreviousOutputBit.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 11 at hPc
  change d.pc < 11
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, matchPreviousOutputBit,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- The last stage of an ElGamal-to-DDH simulation: normalize the source
guess output, compare it with a previously stored challenge bit, erase the
temporary guess cell, and halt with the single DDH bit. This does not invoke
the choose stage or group arithmetic. -/
def finishTaggedGuess : Program :=
  readTaggedGuess.asSubroutine 0 14 ++ matchPreviousOutputBit.asSubroutine 14 26 ++ [.halt]

def finishTaggedGuessStart (beforeInput beforeOutput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) : Configuration :=
  readTaggedGuessStart beforeInput (some challenge :: beforeOutput) bits

def finishTaggedGuessFinish (beforeInput beforeOutput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) : Configuration :=
  { pc := 26,
    inputTape := (readTaggedGuessFinish beforeInput (some challenge :: beforeOutput) bits).inputTape,
    outputTape := {
      left := beforeOutput
      current := some (taggedGuessValue bits == challenge)
      right := [none] },
    halted := true }

theorem finishTaggedGuess_runs (beforeInput beforeOutput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) :
    RunsFor finishTaggedGuess (finishTaggedGuessStart beforeInput beforeOutput challenge bits)
      (finishTaggedGuessFinish beforeInput beforeOutput challenge bits)
      (readTaggedGuessBudget bits + 7) := by
  have reader := (readTaggedGuess_runs beforeInput (some challenge :: beforeOutput) bits).withSubroutine_halted_of_closed [] readTaggedGuess
      (matchPreviousOutputBit.asSubroutine 14 26 ++ [.halt]) 14
      (by simp [readTaggedGuessStart, readTaggedGuess]) rfl rfl readTaggedGuess_control_closed
  change RunsFor finishTaggedGuess (finishTaggedGuessStart beforeInput beforeOutput challenge bits)
    ((readTaggedGuessFinish beforeInput (some challenge :: beforeOutput) bits).resumeAt 14)
    (readTaggedGuessBudget bits) at reader
  let input := (readTaggedGuessFinish beforeInput (some challenge :: beforeOutput) bits).inputTape
  have matcher := (matchPreviousOutputBit_runs input beforeOutput challenge (taggedGuessValue bits)).withSubroutine_halted_of_closed (readTaggedGuess.asSubroutine 0 14)
      matchPreviousOutputBit [.halt] 26
      (by simp [matchPreviousOutputBitStart, matchPreviousOutputBit]) rfl rfl
      matchPreviousOutputBit_control_closed
  have hProgram : Program.withSubroutine (readTaggedGuess.asSubroutine 0 14)
      matchPreviousOutputBit [.halt] 26 = finishTaggedGuess := by
    simp [Program.withSubroutine, Program.asSubroutine_length, finishTaggedGuess, readTaggedGuess]
  rw [hProgram] at matcher
  change RunsFor finishTaggedGuess
    ((readTaggedGuessFinish beforeInput (some challenge :: beforeOutput) bits).resumeAt 14)
    ((finishTaggedGuessFinish beforeInput beforeOutput challenge bits).resumeAt 26) 6 at matcher
  have hHalt : Step finishTaggedGuess
      ((finishTaggedGuessFinish beforeInput beforeOutput challenge bits).resumeAt 26)
      (finishTaggedGuessFinish beforeInput beforeOutput challenge bits) := by
    simp [Step, successors, next, finishTaggedGuess, readTaggedGuess, matchPreviousOutputBit,
      Program.asSubroutine, Instruction.asSubroutine, finishTaggedGuessFinish,
      Configuration.resumeAt, Instruction.next]
  simpa [Nat.add_assoc] using RunsFor.succ (reader.trans matcher) hHalt

theorem finishTaggedGuess_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ finishTaggedGuess := by
  simp [finishTaggedGuess, readTaggedGuess, matchPreviousOutputBit,
    Program.asSubroutine, Instruction.asSubroutine]

theorem finishTaggedGuess_eval (beforeInput beforeOutput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) :
    evalConfigWithin finishTaggedGuess (finishTaggedGuessStart beforeInput beforeOutput challenge bits)
      (readTaggedGuessBudget bits + 7) =
      PMF.pure (finishTaggedGuessFinish beforeInput beforeOutput challenge bits) :=
  (finishTaggedGuess_runs beforeInput beforeOutput challenge bits).evalConfigWithin_eq_pure_of_no_randomBit
    finishTaggedGuess_no_randomBit

theorem finishTaggedGuess_steps_le (bits : List Bool) :
    readTaggedGuessBudget bits + 7 ≤ 14 := by
  have h := readTaggedGuess_budget_le bits
  omega

theorem finishTaggedGuessFinish_outputBits (beforeInput : List (Option Bool))
    (challenge : Bool) (bits : List Bool) :
    (finishTaggedGuessFinish beforeInput [] challenge bits).outputBits =
      [taggedGuessValue bits == challenge] := by
  simp [finishTaggedGuessFinish, Configuration.outputBits, Tape.bits]

theorem finishTaggedGuess_control_closed (c d : Configuration)
    (hPc : c.pc < finishTaggedGuess.length) (step : Step finishTaggedGuess c d)
    (_hRunning : d.halted = false) : d.pc < finishTaggedGuess.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 27 at hPc
  change d.pc < 27
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, finishTaggedGuess,
    readTaggedGuess, matchPreviousOutputBit, Program.asSubroutine,
    Instruction.asSubroutine, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- The complete final-stage call preserves the surrounding tapes and
returns after exactly the charged native steps, even inside a randomized caller. -/
theorem finishTaggedGuess_withSubroutine_eval (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (challenge : Bool) (bits : List Bool) :
    evalConfigWithin (Program.withSubroutine pre finishTaggedGuess suffix returnPc)
      ((finishTaggedGuessStart beforeInput beforeOutput challenge bits).rebasePc pre.length)
      (readTaggedGuessBudget bits + 7) =
      PMF.pure ((finishTaggedGuessFinish beforeInput beforeOutput challenge bits).resumeAt returnPc) :=
  (finishTaggedGuess_runs beforeInput beforeOutput challenge bits).evalConfigWithin_withSubroutine_halted_of_closed
    pre finishTaggedGuess suffix returnPc
    (by simp [finishTaggedGuessStart, readTaggedGuessStart, finishTaggedGuess,
      Program.asSubroutine_length, readTaggedGuess, matchPreviousOutputBit])
    rfl rfl finishTaggedGuess_control_closed finishTaggedGuess_no_randomBit

/-- The tagged-bit parser halts on arbitrary physical tapes, including
internal blanks and malformed suffixes. It inspects at most three input
cells. The seven-step bound uses the actual native branch/write/halt code. -/
theorem readTaggedGuess_haltsFrom_anyTape (input output : Tape) :
    ∀ finish, PaddedRunsFor readTaggedGuess
      ({ inputTape := input, outputTape := output } : Configuration) finish 7 → finish.halted = true := by
  have hLaw : (evalConfigWithin readTaggedGuess
      ({ inputTape := input, outputTape := output } : Configuration) 7).map Configuration.halted = PMF.pure true := by
    rcases input with ⟨left, current, right⟩
    cases current with
    | none =>
        simp [PMF.pure_map, evalConfigWithin, stepPMF, next, readTaggedGuess, Instruction.next,
          Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.write]
    | some tag =>
        cases tag with
        | false =>
            simp [PMF.pure_map, evalConfigWithin, stepPMF, next, readTaggedGuess, Instruction.next,
              Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.write]
        | true =>
            cases right with
            | nil =>
                simp [PMF.pure_map, evalConfigWithin, stepPMF, next, readTaggedGuess, Instruction.next,
                  Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveRight, Tape.write]
            | cons cell tail =>
                cases cell with
                | none =>
                    simp [PMF.pure_map, evalConfigWithin, stepPMF, next, readTaggedGuess, Instruction.next,
                      Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveRight, Tape.write]
                | some bit =>
                    cases bit <;> cases tail with
                    | nil =>
                        simp [PMF.pure_map, evalConfigWithin, stepPMF, next, readTaggedGuess, Instruction.next,
                          Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveRight, Tape.write]
                    | cons cell tail =>
                        cases cell with
                        | none =>
                            simp [PMF.pure_map, evalConfigWithin, stepPMF, next, readTaggedGuess, Instruction.next,
                              Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveRight, Tape.write]
                        | some further =>
                            cases further <;>
                              simp [PMF.pure_map, evalConfigWithin, stepPMF, next, readTaggedGuess, Instruction.next,
                                Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveRight, Tape.write]
  intro finish run
  have hMem : finish.halted ∈ ((evalConfigWithin readTaggedGuess
      ({ inputTape := input, outputTape := output } : Configuration) 7).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  simpa only [hLaw, PMF.support_pure, Set.mem_singleton_iff] using hMem

/-- A malformed saved challenge is also handled by the finite matcher.
Its longest path has six actual native transitions; every path writes a
Boolean comparison/default bit before halting. -/
theorem matchPreviousOutputBit_haltsFrom_anyTape (input output : Tape) :
    ∀ finish, PaddedRunsFor matchPreviousOutputBit
      ({ inputTape := input, outputTape := output } : Configuration) finish 6 → finish.halted = true := by
  have hLaw : (evalConfigWithin matchPreviousOutputBit
      ({ inputTape := input, outputTape := output } : Configuration) 6).map Configuration.halted = PMF.pure true := by
    rcases output with ⟨left, current, right⟩
    cases current with
    | none =>
        simp [PMF.pure_map, evalConfigWithin, stepPMF, next, matchPreviousOutputBit, Instruction.next,
          Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.write]
    | some bit =>
        cases bit <;> cases left with
        | nil =>
            simp [PMF.pure_map, evalConfigWithin, stepPMF, next, matchPreviousOutputBit, Instruction.next,
              Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveLeft, Tape.write]
        | cons cell tail =>
            cases cell with
            | none =>
                simp [PMF.pure_map, evalConfigWithin, stepPMF, next, matchPreviousOutputBit, Instruction.next,
                  Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveLeft, Tape.write]
            | some previous =>
                cases previous <;>
                  simp [PMF.pure_map, evalConfigWithin, stepPMF, next, matchPreviousOutputBit, Instruction.next,
                    Configuration.tape, Configuration.updateTape, Configuration.advance, Tape.moveLeft, Tape.write]
  intro finish run
  have hMem : finish.halted ∈ ((evalConfigWithin matchPreviousOutputBit
      ({ inputTape := input, outputTape := output } : Configuration) 6).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  simpa only [hLaw, PMF.support_pure, Set.mem_singleton_iff] using hMem

/-- Native parsing and comparison also compose on arbitrary physical
tapes. Malformed guesses and missing saved challenge cells still follow
one of the bounded native branches; both tapes are passed unchanged between
the subroutines except for their actual machine transitions. -/
theorem finishTaggedGuess_haltsFrom_anyTape (input output : Tape) :
    ∀ finish, PaddedRunsFor finishTaggedGuess
      ({ inputTape := input, outputTape := output } : Configuration) finish 14 → finish.halted = true := by
  let start : Configuration := { inputTape := input, outputTape := output }
  have hSecond (c : Configuration) (_hc : c ∈ (evalConfigWithin readTaggedGuess start 7).support)
      (finish : Configuration)
      (run : PaddedRunsFor matchPreviousOutputBit (c.resumeAt 0) finish 6) : finish.halted = true :=
    matchPreviousOutputBit_haltsFrom_anyTape c.inputTape c.outputTape finish run
  have hLaw := Program.evalConfigWithin_twoStages_configuration readTaggedGuess matchPreviousOutputBit
    start rfl rfl 7 6 (readTaggedGuess_haltsFrom_anyTape input output) hSecond
  change evalConfigWithin finishTaggedGuess start 14 = _ at hLaw
  intro finish run
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [hLaw, PMF.mem_support_bind_iff] at hMem
  obtain ⟨middle, _hMiddle, hFinish⟩ := hMem
  rw [PMF.mem_support_map_iff] at hFinish
  obtain ⟨target, _hTarget, rfl⟩ := hFinish
  rfl

theorem finishTaggedGuess_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 14 ∧
      RunsFor finishTaggedGuess ({ inputTape := input, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true :=
  exists_halted_run_of_haltsFrom _ _ 14 (finishTaggedGuess_haltsFrom_anyTape input output)

end Machine
