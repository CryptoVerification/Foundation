import Foundation.Machine.DDHChoosePreparation
import Foundation.Machine.OppositeCall
import Foundation.Machine.TapeEquivalence

namespace Machine

/-- Rewind the copied public-key field and restore the temporarily erased
outer DDH-frame terminator. Every head move and the restoring write is a
native transition. The assembled choose request remains on the other tape. -/
def restoreDDHTuple : Program :=
  rewindBitstring.asSubroutine 0 5 ++
    [.moveLeft .input, .write .input false, .moveRight .input, .halt]

def restoreDDHTupleFinish (savedInput publicInput : List (Option Bool))
    (key tail : List Bool) : Configuration :=
  { pc := 8,
    inputTape := { Tape.ofBits (FiniteBitEncoding.delimit key ++ tail) with
      left := some false :: savedInput },
    outputTape := (assembleChooseFieldFinish savedInput publicInput key tail 0).outputTape,
    halted := true }

theorem restoreDDHTuple_runs (savedInput publicInput : List (Option Bool))
    (key : List Bool) (nextBit : Bool) (tail : List Bool) :
    RunsFor restoreDDHTuple
      ((assembleChooseFieldFinish savedInput publicInput key (nextBit :: tail) 0).resumeAt 0)
      (restoreDDHTupleFinish savedInput publicInput key (nextBit :: tail))
      (2 * (FiniteBitEncoding.delimit key).length + 8) := by
  let output := (assembleChooseFieldFinish savedInput publicInput key (nextBit :: tail) 0).outputTape
  let rewound : Configuration :=
    { pc := 3,
      inputTape := ({
        left := savedInput
        right := (FiniteBitEncoding.delimit key).map some ++ some nextBit :: tail.map some } : Tape).moveRight,
      outputTape := output, halted := true }
  let selected : Configuration :=
    { pc := 6,
      inputTape := { left := savedInput, right := (FiniteBitEncoding.delimit key ++ nextBit :: tail).map some },
      outputTape := output }
  let written : Configuration :=
    { selected with pc := 7, inputTape := selected.inputTape.write (some false) }
  let advanced : Configuration :=
    { restoreDDHTupleFinish savedInput publicInput key (nextBit :: tail) with halted := false }
  have hRewind := (rewindScratch_runs_from savedInput (FiniteBitEncoding.delimit key)
      (some nextBit) (tail.map some) output).withSubroutine_halted_of_closed
    [] rewindBitstring [.moveLeft .input, .write .input false, .moveRight .input, .halt] 5
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  change RunsFor restoreDDHTuple
    ((assembleChooseFieldFinish savedInput publicInput key (nextBit :: tail) 0).resumeAt 0)
    (rewound.resumeAt 5) (2 * (FiniteBitEncoding.delimit key).length + 4) at hRewind
  have hBack : Step restoreDDHTuple (rewound.resumeAt 5) selected := by
    cases key <;> simp [Step, successors, next, restoreDDHTuple, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt,
      rewound, selected, Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveRight, Tape.moveLeft, FiniteBitEncoding.delimit]
  have hWrite : Step restoreDDHTuple selected written := by
    simp [Step, successors, next, restoreDDHTuple, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, selected, written,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have hAdvance : Step restoreDDHTuple written advanced := by
    cases key <;> simp [Step, successors, next, restoreDDHTuple, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, written, selected, advanced,
      restoreDDHTupleFinish, Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveRight, Tape.write, Tape.ofBits, FiniteBitEncoding.delimit, output]
  have hHalt : Step restoreDDHTuple advanced
      (restoreDDHTupleFinish savedInput publicInput key (nextBit :: tail)) := by
    simp [Step, successors, next, restoreDDHTuple, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, advanced, restoreDDHTupleFinish,
      Instruction.next]
  convert RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ hRewind hBack) hWrite) hAdvance) hHalt using 1

theorem restoreDDHTuple_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ restoreDDHTuple := by
  simp [restoreDDHTuple, rewindBitstring, Program.asSubroutine, Instruction.asSubroutine]

theorem restoreDDHTuple_eval (savedInput publicInput : List (Option Bool))
    (key : List Bool) (nextBit : Bool) (tail : List Bool) :
    evalConfigWithin restoreDDHTuple
      ((assembleChooseFieldFinish savedInput publicInput key (nextBit :: tail) 0).resumeAt 0)
      (2 * (FiniteBitEncoding.delimit key).length + 8) =
      PMF.pure (restoreDDHTupleFinish savedInput publicInput key (nextBit :: tail)) :=
  (restoreDDHTuple_runs savedInput publicInput key nextBit tail).evalConfigWithin_eq_pure_of_no_randomBit
    restoreDDHTuple_no_randomBit

theorem restoreDDHTuple_control_closed (c d : Configuration)
    (hPc : c.pc < restoreDDHTuple.length) (step : Step restoreDDHTuple c d)
    (_hRunning : d.halted = false) : d.pc < restoreDDHTuple.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 9 at hPc
  change d.pc < 9
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, restoreDDHTuple,
    rewindBitstring, Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

private theorem rewindOutput_control_closed (c d : Configuration)
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

/-- Prepare an actual choose-source call. Restore and retain the entire DDH
input, reserve a physical blank after it, and rewind the generated choose
input on the opposite tape. This fixed native code does not invoke the
source yet, nor assume a free reset or an externally assembled input. -/
def prepareDDHChooseCall : Program :=
  prepareDDHChooseRequest.asSubroutine 0 96 ++ restoreDDHTuple.asSubroutine 96 106 ++
    GuardedCompiler.seekScratchInput.asSubroutine 106 112 ++
    (Program.swapTapes rewindBitstring).asSubroutine 112 117 ++ [.halt]

def prepareDDHChooseCallFinish (n : Nat) (instanceBits key tail : List Bool) : Configuration :=
  { pc := 117,
    inputTape := {
      left := none :: (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ tail)).reverse.map some ++ [none] },
    outputTape := ({
      right := (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).map some ++ [none, none]
    } : Tape).moveRight,
    halted := true }

def prepareDDHChooseCallSteps (n : Nat) (instanceBits key tail : List Bool) : Nat :=
  prepareDDHChooseRequestSteps n instanceBits key tail +
    (2 * (FiniteBitEncoding.delimit key).length + 8) +
    (3 * (FiniteBitEncoding.delimit key ++ tail).length + 3) +
    (2 * (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length + 4) + 1

theorem prepareDDHChooseCall_runs (n : Nat) (instanceBits key : List Bool)
    (nextBit : Bool) (tail : List Bool) :
    RunsFor prepareDDHChooseCall
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail)))
      (prepareDDHChooseCallFinish n instanceBits key (nextBit :: tail))
      (prepareDDHChooseCallSteps n instanceBits key (nextBit :: tail)) := by
  let tuple := FiniteBitEncoding.delimit key ++ nextBit :: tail
  let publicBits := encodeSecurityParameter n ++ frame instanceBits
  let saved := prepareDDHChooseSavedInput n instanceBits tuple
  let chooseInput := publicBits ++ frame (false :: key)
  let output := (assembleChooseFieldFinish saved (publicBits.reverse.map some) key (nextBit :: tail) 0).outputTape
  let before := some false :: saved
  let a := prepareDDHChooseRequest.asSubroutine 0 96
  let b := restoreDDHTuple.asSubroutine 96 106
  let k := GuardedCompiler.seekScratchInput.asSubroutine 106 112
  let r := (Program.swapTapes rewindBitstring).asSubroutine 112 117
  have hPrepare := (prepareDDHChooseRequest_runs n instanceBits key nextBit tail).withSubroutine_halted_of_closed
    [] prepareDDHChooseRequest (b ++ k ++ r ++ [.halt]) 96
    (by change 0 < 95; decide) rfl rfl prepareDDHChooseRequest_control_closed
  change RunsFor prepareDDHChooseCall
    (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++ frame tuple))
    ((prepareDDHChooseRequestFinish n instanceBits key (nextBit :: tail)).resumeAt 96)
    (prepareDDHChooseRequestSteps n instanceBits key (nextBit :: tail)) at hPrepare
  have hRestore := (restoreDDHTuple_runs saved (publicBits.reverse.map some) key nextBit tail).withSubroutine_halted_of_closed
    a restoreDDHTuple (k ++ r ++ [.halt]) 106
    (by simp [assembleChooseFieldFinish, Configuration.resumeAt, restoreDDHTuple]) rfl rfl
    restoreDDHTuple_control_closed
  change RunsFor prepareDDHChooseCall
    ((prepareDDHChooseRequestFinish n instanceBits key (nextBit :: tail)).resumeAt 96)
    ((restoreDDHTupleFinish saved (publicBits.reverse.map some) key (nextBit :: tail)).resumeAt 106)
    (2 * (FiniteBitEncoding.delimit key).length + 8) at hRestore
  have hSeekStart : (restoreDDHTupleFinish saved (publicBits.reverse.map some) key (nextBit :: tail)).resumeAt 106 =
      (GuardedCompiler.seekScratchInputStart before tuple output).rebasePc 106 := rfl
  rw [hSeekStart] at hRestore
  have hSeek := (GuardedCompiler.seekScratchInput_runs before tuple output).withSubroutine_halted_of_closed
    (a ++ b) GuardedCompiler.seekScratchInput (r ++ [.halt]) 112
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareDDHChooseCall
    ((GuardedCompiler.seekScratchInputStart before tuple output).rebasePc 106)
    ((GuardedCompiler.seekScratchInputFinish before tuple output).resumeAt 112)
    (3 * tuple.length + 3) at hSeek
  let savedTape := (GuardedCompiler.seekScratchInputFinish before tuple output).inputTape
  let rewindStart : Configuration :=
    { inputTape := { left := chooseInput.reverse.map some, right := [none] }, outputTape := savedTape }
  let rewindFinish : Configuration :=
    { pc := 3,
      inputTape := ({ right := chooseInput.map some ++ [none, none] } : Tape).moveRight,
      outputTape := savedTape, halted := true }
  have hOutput : output = ({ left := chooseInput.reverse.map some, right := [none] } : Tape) := by
    exact prepareDDHChooseRequest_output_layout n instanceBits key (nextBit :: tail)
  have hRewindStart : (GuardedCompiler.seekScratchInputFinish before tuple output).resumeAt 112 =
      rewindStart.swapTapes.rebasePc 112 := by
    simp [GuardedCompiler.seekScratchInputFinish, Configuration.resumeAt,
      Configuration.rebasePc, Configuration.swapTapes, rewindStart, savedTape, hOutput]
  rw [hRewindStart] at hSeek
  have hRewind := ((rewindBitstring_runs_from chooseInput none [none] savedTape).swapTapes).withSubroutine_halted_of_closed
    (a ++ b ++ k) (Program.swapTapes rewindBitstring) [.halt] 117
    (by change 0 < 4; decide) rfl rfl rewindOutput_control_closed
  change RunsFor prepareDDHChooseCall (rewindStart.swapTapes.rebasePc 112)
    (rewindFinish.swapTapes.resumeAt 117) (2 * chooseInput.length + 4) at hRewind
  have hSaved : savedTape = (prepareDDHChooseCallFinish n instanceBits key (nextBit :: tail)).inputTape := by
    simp [savedTape, GuardedCompiler.seekScratchInputFinish, before, saved,
      prepareDDHChooseSavedInput, prepareDDHChooseCallFinish, tuple, frame,
      List.reverse_append, List.map_append, List.append_assoc]
  have hHalt : Step prepareDDHChooseCall (rewindFinish.swapTapes.resumeAt 117)
      (prepareDDHChooseCallFinish n instanceBits key (nextBit :: tail)) := by
    simp [Step, successors, next, prepareDDHChooseCall, prepareDDHChooseRequest,
      prepareDDHPublicPrefix, skipUnary, skipFrame, savePublicPrefix, rewindBitstring,
      copyBitstring, assembleChooseField, writeChooseHeader, readDelimited,
      restoreDDHTuple, GuardedCompiler.seekScratchInput, Program.swapTapes,
      Instruction.swapTapes, TapeId.swap, Program.asSubroutine, Instruction.asSubroutine,
      rewindFinish, Configuration.swapTapes, Configuration.resumeAt,
      prepareDDHChooseCallFinish, chooseInput, publicBits, Instruction.next, hSaved]
  simpa only [prepareDDHChooseCallSteps, tuple, chooseInput, publicBits, Nat.add_assoc] using
    RunsFor.succ (((hPrepare.trans hRestore).trans hSeek).trans hRewind) hHalt

theorem prepareDDHChooseCall_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareDDHChooseCall := by
  simp [prepareDDHChooseCall, prepareDDHChooseRequest, prepareDDHPublicPrefix,
    skipUnary, skipFrame, savePublicPrefix, rewindBitstring, copyBitstring,
    assembleChooseField, writeChooseHeader, readDelimited, restoreDDHTuple,
    GuardedCompiler.seekScratchInput, Program.swapTapes, Instruction.swapTapes,
    TapeId.swap, Program.asSubroutine, Instruction.asSubroutine]

theorem prepareDDHChooseCall_eval (n : Nat) (instanceBits key : List Bool)
    (nextBit : Bool) (tail : List Bool) :
    evalConfigWithin prepareDDHChooseCall
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail)))
      (prepareDDHChooseCallSteps n instanceBits key (nextBit :: tail)) =
      PMF.pure (prepareDDHChooseCallFinish n instanceBits key (nextBit :: tail)) :=
  (prepareDDHChooseCall_runs n instanceBits key nextBit tail).evalConfigWithin_eq_pure_of_no_randomBit
    prepareDDHChooseCall_no_randomBit

theorem prepareDDHChooseCall_triple_eval (n : Nat) (instanceBits key second third : List Bool) :
    evalConfigWithin prepareDDHChooseCall
      (Configuration.initial (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ FiniteBitEncoding.delimit second ++ third)))
      (prepareDDHChooseCallSteps n instanceBits key (FiniteBitEncoding.delimit second ++ third)) =
      PMF.pure (prepareDDHChooseCallFinish n instanceBits key (FiniteBitEncoding.delimit second ++ third)) := by
  cases second with
  | nil => simpa [FiniteBitEncoding.delimit] using prepareDDHChooseCall_eval n instanceBits key false third
  | cons bit rest =>
      simpa only [FiniteBitEncoding.delimit, List.cons_append, List.append_assoc] using
        prepareDDHChooseCall_eval n instanceBits key true (bit :: (FiniteBitEncoding.delimit rest ++ third))

theorem prepareDDHChooseCallSteps_le (n : Nat) (instanceBits key tail : List Bool) :
    prepareDDHChooseCallSteps n instanceBits key tail ≤
      60 * (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ tail)).length + 100 := by
  have hPrepare := prepareDDHChooseRequestSteps_le n instanceBits key tail
  simp only [prepareDDHChooseCallSteps, encodeSecurityParameter, frame,
    List.length_append, List.length_replicate, List.length_cons, List.length_nil,
    FiniteBitEncoding.delimit_length] at *
  omega

/-- Every random branch reaches the explicit native halt on this canonical
invocation. The source call and its subsequent phases are not included. -/
theorem prepareDDHChooseCall_haltsWithin (n : Nat) (instanceBits key : List Bool)
    (nextBit : Bool) (tail : List Bool) :
    HaltsWithin prepareDDHChooseCall
      (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail))
      (60 * (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail)).length + 100) := by
  have hHalts : HaltsWith prepareDDHChooseCall
      (encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ nextBit :: tail))
      (prepareDDHChooseCallFinish n instanceBits key (nextBit :: tail)).outputBits
      (prepareDDHChooseCallSteps n instanceBits key (nextBit :: tail)) :=
    ⟨_, prepareDDHChooseCall_runs n instanceBits key nextBit tail, rfl, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit prepareDDHChooseCall_no_randomBit).mono
    (prepareDDHChooseCallSteps_le n instanceBits key (nextBit :: tail))

private theorem getD_append_two_blanks (bits : List (Option Bool)) (i : Nat) :
    (bits ++ [none, none]).getD i none = bits.getD i none := by
  induction bits generalizing i with
  | nil => cases i with
      | zero => rfl
      | succ i => cases i <;> rfl
  | cons bit rest ih => cases i with
      | zero => rfl
      | succ i => exact ih i

private theorem rewound_input_equivalent (bits : List Bool) :
    (({ right := bits.map some ++ [none, none] } : Tape).moveRight).Equivalent
      { Tape.ofBits bits with left := [none] } := by
  cases bits with
  | nil =>
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro i
      cases i <;> rfl
  | cons bit rest =>
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro i
      exact getD_append_two_blanks (rest.map some) i

/-- The charged preparation reaches the guarded opposite-source-call
layout. Its physical outer blanks are retained, rather than cleared for
free. They describe exactly the same cells as the proven call fixture. -/
theorem prepareDDHChooseCall_source_layout (n : Nat) (instanceBits key tail : List Bool) :
    ((prepareDDHChooseCallFinish n instanceBits key tail).resumeAt 0).Equivalent
      (GuardedCompiler.packInputStart [none]
        (none :: (encodeSecurityParameter n ++ frame instanceBits ++
          frame (FiniteBitEncoding.delimit key ++ tail)).reverse.map some ++ [none])
        (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key))).swapTapes := by
  refine ⟨rfl, rfl, Tape.Equivalent.refl _, ?_⟩
  exact rewound_input_equivalent _

/-- The actual prepared tapes can invoke the guarded source without removing
physical blank padding. All original source random branches are retained.
The observation includes both the saved DDH input and the raw choose
response, on their actual physical tape. The source budget is evaluated at
its own choose-input length, never at a longer wrapper input. -/
theorem prepareDDHChooseCall_source_eval (source : Program) (n : Nat)
    (instanceBits key tail : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key))
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length)) :
    (evalConfigWithin (GuardedCompiler.rawCompileOpposite source)
      ((prepareDDHChooseCallFinish n instanceBits key tail).resumeAt 0)
      (GuardedCompiler.rawTraceBudget q
        (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length)).map
      (fun c => (c.halted, c.inputTape.bits)) =
    (evalConfigWithin source
      (GuardedCompiler.preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)))
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length)).map
      (fun c => (true, encodeSecurityParameter n ++ frame instanceBits ++
        frame (FiniteBitEncoding.delimit key ++ tail) ++ c.outputBits)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
      (prepareDDHChooseCall_source_layout n instanceBits key tail) _
      (fun c => (c.halted, c.inputTape.bits))
      (fun _ _ h => congrArg₂ Prod.mk h.2.1 h.2.2.1.bits),
    GuardedCompiler.rawCompileOpposite_configuration_eval _ _ _ _ q halts, PMF.map_comp]
  apply congrArg (fun f => (evalConfigWithin source
    (GuardedCompiler.preparedSource (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)))
    (q (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length)).map f)
  funext c
  change (true, ((GuardedCompiler.rawResultFrom source
    (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)) [none]
    (none :: (encodeSecurityParameter n ++ frame instanceBits ++
      frame (FiniteBitEncoding.delimit key ++ tail)).reverse.map some ++ [none]) c).swapTapes).inputTape.bits) = _
  rw [GuardedCompiler.rawCompileOpposite_result_bits]
  simp [List.reverse_append, List.filterMap_append, List.append_assoc]

/-- The source-call budget applies to every native random branch on the
physically prepared tapes, including branches returning malformed responses. -/
theorem prepareDDHChooseCall_source_haltsFrom (source : Program) (n : Nat)
    (instanceBits key tail : List Bool) (q : Nat → Nat)
    (halts : HaltsWithin source
      (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key))
      (q (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length))
    (finish : Configuration)
    (run : PaddedRunsFor (GuardedCompiler.rawCompileOpposite source)
      ((prepareDDHChooseCallFinish n instanceBits key tail).resumeAt 0) finish
      (GuardedCompiler.rawTraceBudget q
        (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length)) :
    finish.halted = true := by
  have hMem : (finish.halted, finish.inputTape.bits) ∈
      ((evalConfigWithin (GuardedCompiler.rawCompileOpposite source)
        ((prepareDDHChooseCallFinish n instanceBits key tail).resumeAt 0)
        (GuardedCompiler.rawTraceBudget q
          (encodeSecurityParameter n ++ frame instanceBits ++ frame (false :: key)).length)).map
        (fun c => (c.halted, c.inputTape.bits))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [prepareDDHChooseCall_source_eval source n instanceBits key tail q halts,
    PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, hEq⟩ := hMem
  exact (congrArg Prod.fst hEq).symm

set_option maxHeartbeats 2000000 in
theorem prepareDDHChooseCall_control_closed (c d : Configuration)
    (hPc : c.pc < prepareDDHChooseCall.length) (step : Step prepareDDHChooseCall c d)
    (_hRunning : d.halted = false) : d.pc < prepareDDHChooseCall.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 118 at hPc
  change d.pc < 118
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, prepareDDHChooseCall,
    prepareDDHChooseRequest, prepareDDHPublicPrefix, skipUnary, skipFrame,
    savePublicPrefix, rewindBitstring, copyBitstring, assembleChooseField,
    writeChooseHeader, readDelimited, restoreDDHTuple, GuardedCompiler.seekScratchInput,
    Program.swapTapes, Instruction.swapTapes, TapeId.swap, Program.asSubroutine,
    Instruction.asSubroutine, subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- The native tuple-boundary restoration stops on arbitrary finite caller
tapes. Restoring a valid tuple still requires the earlier layout theorem;
this bound only ensures that malformed parser results cannot loop here. -/
theorem restoreDDHTuple_terminates_from_anyTape (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 2 * input.cells + 8 ∧
      RunsFor restoreDDHTuple ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨rewound, rewindTime, hRewindTime, hRewindRun, hRewindHalt, _⟩ :=
    rewindBitstring_terminates_from input output
  have hRewind := hRewindRun.withSubroutine_halted_of_closed
    [] rewindBitstring [.moveLeft .input, .write .input false, .moveRight .input, .halt] 5
    (by change 0 < 4; decide) rfl hRewindHalt rewindBitstring_control_closed
  change RunsFor restoreDDHTuple ({ inputTape := input, outputTape := output } : Configuration)
    (rewound.resumeAt 5) rewindTime at hRewind
  let backed : Configuration :=
    { pc := 6, inputTape := rewound.inputTape.moveLeft, outputTape := rewound.outputTape }
  let written : Configuration := { backed with pc := 7, inputTape := backed.inputTape.write (some false) }
  let advanced : Configuration := { written with pc := 8, inputTape := written.inputTape.moveRight }
  have hBack : Step restoreDDHTuple (rewound.resumeAt 5) backed := by
    simp [Step, successors, next, restoreDDHTuple, rewindBitstring, Program.asSubroutine,
      Instruction.asSubroutine, Configuration.resumeAt, backed, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hWrite : Step restoreDDHTuple backed written := by
    simp [Step, successors, next, restoreDDHTuple, rewindBitstring, Program.asSubroutine,
      Instruction.asSubroutine, backed, written, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hForward : Step restoreDDHTuple written advanced := by
    simp [Step, successors, next, restoreDDHTuple, rewindBitstring, Program.asSubroutine,
      Instruction.asSubroutine, backed, written, advanced, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hHalt : Step restoreDDHTuple advanced { advanced with halted := true } := by
    simp [Step, successors, next, restoreDDHTuple, rewindBitstring, Program.asSubroutine,
      Instruction.asSubroutine, backed, written, advanced, Instruction.next]
  refine ⟨{ advanced with halted := true }, rewindTime + 4, ?_, ?_, rfl⟩
  · simp only [Tape.cells]
    omega
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using
      RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ hRewind hBack) hWrite) hForward) hHalt

/-- Restoring the temporary delimiter before a contiguous suffix preserves
a contiguous suffix, even when the preceding field was malformed. The output
tape is untouched. Extra outer blanks remain part of the physical tapes. -/
theorem restoreDDHTuple_terminates_from_suffix (before : List (Option Bool))
    (rest : List Bool) (output : Tape) :
    ∃ (finish : Configuration) (leading : List Bool) (saved : List (Option Bool)),
      leading.length ≤ before.length ∧
      RunsFor restoreDDHTuple
        ({ inputTape := { Tape.ofBits rest with left := before }, outputTape := output } : Configuration)
        finish (2 * leading.length + 8) ∧ finish.halted = true ∧
      finish.inputTape.Equivalent { Tape.ofBits (leading ++ rest) with left := some false :: saved } ∧
      finish.outputTape = output := by
  obtain ⟨rewound, leading, saved, hLeading, hRewindRun, hRewindHalt, hRewindInput, hRewindOutput⟩ :=
    rewindBitstring_terminates_from_suffix before rest output
  have hRewind := hRewindRun.withSubroutine_halted_of_closed
    [] rewindBitstring [.moveLeft .input, .write .input false, .moveRight .input, .halt] 5
    (by change 0 < 4; decide) rfl hRewindHalt rewindBitstring_control_closed
  change RunsFor restoreDDHTuple
    ({ inputTape := { Tape.ofBits rest with left := before }, outputTape := output } : Configuration)
    (rewound.resumeAt 5) (2 * leading.length + 4) at hRewind
  let backed : Configuration :=
    { pc := 6, inputTape := rewound.inputTape.moveLeft, outputTape := rewound.outputTape }
  let written : Configuration := { backed with pc := 7, inputTape := backed.inputTape.write (some false) }
  let advanced : Configuration := { written with pc := 8, inputTape := written.inputTape.moveRight }
  have hBack : Step restoreDDHTuple (rewound.resumeAt 5) backed := by
    simp [Step, successors, next, restoreDDHTuple, rewindBitstring, Program.asSubroutine,
      Instruction.asSubroutine, Configuration.resumeAt, backed, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hWrite : Step restoreDDHTuple backed written := by
    simp [Step, successors, next, restoreDDHTuple, rewindBitstring, Program.asSubroutine,
      Instruction.asSubroutine, backed, written, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hForward : Step restoreDDHTuple written advanced := by
    simp [Step, successors, next, restoreDDHTuple, rewindBitstring, Program.asSubroutine,
      Instruction.asSubroutine, backed, written, advanced, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have hHalt : Step restoreDDHTuple advanced { advanced with halted := true } := by
    simp [Step, successors, next, restoreDDHTuple, rewindBitstring, Program.asSubroutine,
      Instruction.asSubroutine, backed, written, advanced, Instruction.next]
  refine ⟨{ advanced with halted := true }, leading, saved, hLeading, ?_, rfl, ?_, hRewindOutput⟩
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using
      RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ hRewind hBack) hWrite) hForward) hHalt
  · simpa only [advanced, written, backed, List.singleton_append, Tape.moveLeft, Tape.write, Tape.moveRight] using
      (hRewindInput.moveLeft.write (some false)).moveRight

/-- All-input stopping bound for the complete native choose-call front end.
Both physical tapes, including malformed parser artifacts, are retained
through request assembly, tuple-boundary restoration, scratch seeking, and
the opposite-tape rewind. This is not a valid guarded-source entry-layout
assertion on malformed inputs. -/
theorem prepareDDHChooseCall_terminates (input : List Bool) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 20000000 * (input.length + 1) ∧
      RunsFor prepareDDHChooseCall (Configuration.initial input) finish used ∧
      finish.halted = true := by
  obtain ⟨prepareFinish, prepareTime, hPrepareTime, hPrepareRun, hPrepareHalt⟩ :=
    prepareDDHChooseRequest_terminates input
  obtain ⟨restoreFinish, restoreTime, hRestoreTime, hRestoreRun, hRestoreHalt⟩ :=
    restoreDDHTuple_terminates_from_anyTape prepareFinish.inputTape prepareFinish.outputTape
  obtain ⟨seekFinish, seekTime, hSeekTime, hSeekRun, hSeekHalt, _⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape restoreFinish.inputTape restoreFinish.outputTape
  obtain ⟨rewindFinish, rewindTime, hRewindTime, hRewindRun, hRewindHalt, _⟩ :=
    rewindBitstring_terminates_from seekFinish.outputTape seekFinish.inputTape
  let a := prepareDDHChooseRequest.asSubroutine 0 96
  let b := restoreDDHTuple.asSubroutine 96 106
  let c := GuardedCompiler.seekScratchInput.asSubroutine 106 112
  let d := (Program.swapTapes rewindBitstring).asSubroutine 112 117
  have hPrepare := hPrepareRun.withSubroutine_halted_of_closed
    [] prepareDDHChooseRequest (b ++ c ++ d ++ [.halt]) 96
    (by change 0 < 95; decide) rfl hPrepareHalt prepareDDHChooseRequest_control_closed
  change RunsFor prepareDDHChooseCall (Configuration.initial input)
    (prepareFinish.resumeAt 96) prepareTime at hPrepare
  have hRestore := hRestoreRun.withSubroutine_halted_of_closed
    a restoreDDHTuple (c ++ d ++ [.halt]) 106
    (by change 0 < 9; decide) rfl hRestoreHalt restoreDDHTuple_control_closed
  change RunsFor prepareDDHChooseCall
    ({ pc := 96, inputTape := prepareFinish.inputTape, outputTape := prepareFinish.outputTape } : Configuration)
    (restoreFinish.resumeAt 106) restoreTime at hRestore
  have hRestoreStart : prepareFinish.resumeAt 96 =
      ({ pc := 96, inputTape := prepareFinish.inputTape, outputTape := prepareFinish.outputTape } : Configuration) := rfl
  rw [← hRestoreStart] at hRestore
  have hSeek := hSeekRun.withSubroutine_halted_of_closed
    (a ++ b) GuardedCompiler.seekScratchInput (d ++ [.halt]) 112
    (by change 0 < 5; decide) rfl hSeekHalt GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareDDHChooseCall
    ({ pc := 106, inputTape := restoreFinish.inputTape, outputTape := restoreFinish.outputTape } : Configuration)
    (seekFinish.resumeAt 112) seekTime at hSeek
  have hSeekStart : restoreFinish.resumeAt 106 =
      ({ pc := 106, inputTape := restoreFinish.inputTape, outputTape := restoreFinish.outputTape } : Configuration) := rfl
  rw [← hSeekStart] at hSeek
  have hRewindSwap := hRewindRun.swapTapes
  have hRewind := hRewindSwap.withSubroutine_halted_of_closed
    (a ++ b ++ c) (Program.swapTapes rewindBitstring) [.halt] 117
    (by change 0 < 4; decide) rfl hRewindHalt rewindOutput_control_closed
  change RunsFor prepareDDHChooseCall
    ({ pc := 112, inputTape := seekFinish.inputTape, outputTape := seekFinish.outputTape } : Configuration)
    (rewindFinish.swapTapes.resumeAt 117) rewindTime at hRewind
  have hRewindStart : seekFinish.resumeAt 112 =
      ({ pc := 112, inputTape := seekFinish.inputTape, outputTape := seekFinish.outputTape } : Configuration) := rfl
  rw [← hRewindStart] at hRewind
  have hHalt : Step prepareDDHChooseCall (rewindFinish.swapTapes.resumeAt 117)
      { rewindFinish.swapTapes.resumeAt 117 with halted := true } := by
    simp [Step, successors, next, prepareDDHChooseCall, prepareDDHChooseRequest,
      prepareDDHPublicPrefix, skipUnary, skipFrame, savePublicPrefix, rewindBitstring,
      copyBitstring, assembleChooseField, writeChooseHeader, readDelimited,
      restoreDDHTuple, GuardedCompiler.seekScratchInput, Program.swapTapes,
      Instruction.swapTapes, TapeId.swap, Program.asSubroutine, Instruction.asSubroutine,
      Configuration.resumeAt, Configuration.swapTapes, Instruction.next]
  have hUntilRestore := hPrepare.trans hRestore
  have hUntilSeek := hUntilRestore.trans hSeek
  refine ⟨{ rewindFinish.swapTapes.resumeAt 117 with halted := true },
    prepareTime + restoreTime + seekTime + rewindTime + 1, ?_,
    RunsFor.succ (hUntilSeek.trans hRewind) hHalt, rfl⟩
  have hPrepareStorage := GuardedCompiler.sourceStorage_le_of_run hPrepare
  have hRestoreStorage := GuardedCompiler.sourceStorage_le_of_run hUntilRestore
  have hSeekStorage := GuardedCompiler.sourceStorage_le_of_run hUntilSeek
  simp only [GuardedCompiler.sourceStorage, Configuration.resumeAt] at hPrepareStorage hRestoreStorage hSeekStorage
  have hInputCells : (Configuration.initial input).inputTape.cells ≤ input.length + 1 := by
    cases input
    · simp [Configuration.initial, Tape.ofBits, Tape.cells]
    · simp only [Configuration.initial, Tape.ofBits, Tape.cells, List.length_nil,
        List.length_map, List.length_cons]
      omega
  have hOutputCells : (Configuration.initial input).outputTape.cells = 1 := rfl
  have hLeft : seekFinish.outputTape.left.length ≤ seekFinish.outputTape.cells := by
    simp only [Tape.cells]
    omega
  omega

/-- Every raw DDH bitstring prepares a genuine guarded source-call entry.
The generated source request may be malformed, but it is a contiguous finite
bitstring and the destination output region is blank. All caller data and
parser artifacts remain in their actual tape cells; no reset is performed.
The independent all-input stopping trace supplies the displayed runtime. -/
theorem prepareDDHChooseCall_terminates_with_separated_layout (input : List Bool) :
    ∃ (finish : Configuration) (used : Nat) (beforeInput beforeOutput : List (Option Bool))
      (sourceInput : List Bool),
      used ≤ 20000000 * (input.length + 1) ∧
      RunsFor prepareDDHChooseCall (Configuration.initial input) finish used ∧
      finish.halted = true ∧
      (finish.resumeAt 0).Equivalent
        (GuardedCompiler.packInputStart beforeInput (none :: beforeOutput) sourceInput).swapTapes ∧
      sourceInput.length ≤ finish.outputTape.cells := by
  obtain ⟨prepareFinish, prepareTime, prepareBefore, prepareRest, prepareOutput, prepareBlanks,
    _hPrepareTime, hPrepareRun, hPrepareHalt, hPrepareInput, hPrepareOutput⟩ :=
    prepareDDHChooseRequest_terminates_with_layout input
  let output : Tape := { left := prepareOutput, right := List.replicate prepareBlanks none }
  obtain ⟨canonicalRestore, restoredPrefix, restoredSaved, _hPrefixLength,
    hCanonicalRestoreRun, hCanonicalRestoreHalt, hCanonicalRestoreInput, hCanonicalRestoreOutput⟩ :=
    restoreDDHTuple_terminates_from_suffix prepareBefore prepareRest output
  have hRestoreEntry :
      ({ inputTape := { Tape.ofBits prepareRest with left := prepareBefore }, outputTape := output } : Configuration).Equivalent ({ inputTape := prepareFinish.inputTape, outputTape := prepareFinish.outputTape } : Configuration) :=
    ⟨rfl, rfl, hPrepareInput.symm, hPrepareOutput.symm⟩
  obtain ⟨restoreFinish, hRestoreRun, hRestoreEq⟩ := hCanonicalRestoreRun.exists_equivalent hRestoreEntry
  have hRestoreHalt : restoreFinish.halted = true := hRestoreEq.2.1.symm.trans hCanonicalRestoreHalt
  let restoredBits := restoredPrefix ++ prepareRest
  let restoredBefore := some false :: restoredSaved
  have hRestoreInput : restoreFinish.inputTape.Equivalent
      { Tape.ofBits restoredBits with left := restoredBefore } :=
    hRestoreEq.2.2.1.symm.trans hCanonicalRestoreInput
  have hRestoreOutput : restoreFinish.outputTape.Equivalent output := by
    rw [← hCanonicalRestoreOutput]
    exact hRestoreEq.2.2.2.symm
  have hSeekEntry :
      (GuardedCompiler.seekScratchInputStart restoredBefore restoredBits output).Equivalent
        ({ inputTape := restoreFinish.inputTape, outputTape := restoreFinish.outputTape } : Configuration) := by
    refine ⟨rfl, rfl, ?_, hRestoreOutput.symm⟩
    change ({ Tape.ofBits restoredBits with left := restoredBefore } : Tape).Equivalent restoreFinish.inputTape
    exact hRestoreInput.symm
  obtain ⟨seekFinish, hSeekRun, hSeekEq⟩ :=
    (GuardedCompiler.seekScratchInput_runs restoredBefore restoredBits output).exists_equivalent hSeekEntry
  have hSeekHalt : seekFinish.halted = true := hSeekEq.2.1.symm
  let scratchBefore := none :: restoredBits.reverse.map some ++ restoredBefore
  have hSeekInput : seekFinish.inputTape.Equivalent { left := scratchBefore } := hSeekEq.2.2.1.symm
  have hSeekOutput : seekFinish.outputTape.Equivalent { left := prepareOutput } :=
    hSeekEq.2.2.2.symm.trans (Tape.blank_padding_equivalent prepareOutput prepareBlanks)
  obtain ⟨canonicalRewind, sourceBits, sourceSaved, _hSourceLength,
    hCanonicalRewindRun, hCanonicalRewindHalt, hCanonicalRewindInput, hCanonicalRewindOutput⟩ :=
    rewindBitstring_terminates_from_suffix prepareOutput [] ({ left := scratchBefore } : Tape)
  have hRewindEntry :
      ({ inputTape := { left := prepareOutput }, outputTape := { left := scratchBefore } } : Configuration).Equivalent ({ inputTape := seekFinish.outputTape, outputTape := seekFinish.inputTape } : Configuration) :=
    ⟨rfl, rfl, hSeekOutput.symm, hSeekInput.symm⟩
  obtain ⟨rewindFinish, hRewindRun, hRewindEq⟩ := hCanonicalRewindRun.exists_equivalent hRewindEntry
  have hRewindHalt : rewindFinish.halted = true := hRewindEq.2.1.symm.trans hCanonicalRewindHalt
  let a := prepareDDHChooseRequest.asSubroutine 0 96
  let b := restoreDDHTuple.asSubroutine 96 106
  let c := GuardedCompiler.seekScratchInput.asSubroutine 106 112
  let d := (Program.swapTapes rewindBitstring).asSubroutine 112 117
  have hPrepare := hPrepareRun.withSubroutine_halted_of_closed
    [] prepareDDHChooseRequest (b ++ c ++ d ++ [.halt]) 96
    (by change 0 < 95; decide) rfl hPrepareHalt prepareDDHChooseRequest_control_closed
  change RunsFor prepareDDHChooseCall (Configuration.initial input)
    (prepareFinish.resumeAt 96) prepareTime at hPrepare
  have hRestore := hRestoreRun.withSubroutine_halted_of_closed
    a restoreDDHTuple (c ++ d ++ [.halt]) 106
    (by change 0 < 9; decide) rfl hRestoreHalt restoreDDHTuple_control_closed
  change RunsFor prepareDDHChooseCall
    ({ pc := 96, inputTape := prepareFinish.inputTape, outputTape := prepareFinish.outputTape } : Configuration)
    (restoreFinish.resumeAt 106) (2 * restoredPrefix.length + 8) at hRestore
  have hRestoreStart : prepareFinish.resumeAt 96 =
      ({ pc := 96, inputTape := prepareFinish.inputTape, outputTape := prepareFinish.outputTape } : Configuration) := rfl
  rw [← hRestoreStart] at hRestore
  have hSeek := hSeekRun.withSubroutine_halted_of_closed
    (a ++ b) GuardedCompiler.seekScratchInput (d ++ [.halt]) 112
    (by change 0 < 5; decide) rfl hSeekHalt GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareDDHChooseCall
    ({ pc := 106, inputTape := restoreFinish.inputTape, outputTape := restoreFinish.outputTape } : Configuration)
    (seekFinish.resumeAt 112) (3 * restoredBits.length + 3) at hSeek
  have hSeekStart : restoreFinish.resumeAt 106 =
      ({ pc := 106, inputTape := restoreFinish.inputTape, outputTape := restoreFinish.outputTape } : Configuration) := rfl
  rw [← hSeekStart] at hSeek
  have hRewindSwap := hRewindRun.swapTapes
  have hRewind := hRewindSwap.withSubroutine_halted_of_closed
    (a ++ b ++ c) (Program.swapTapes rewindBitstring) [.halt] 117
    (by change 0 < 4; decide) rfl hRewindHalt rewindOutput_control_closed
  change RunsFor prepareDDHChooseCall
    ({ pc := 112, inputTape := seekFinish.inputTape, outputTape := seekFinish.outputTape } : Configuration)
    (rewindFinish.swapTapes.resumeAt 117) (2 * sourceBits.length + 4) at hRewind
  have hRewindStart : seekFinish.resumeAt 112 =
      ({ pc := 112, inputTape := seekFinish.inputTape, outputTape := seekFinish.outputTape } : Configuration) := rfl
  rw [← hRewindStart] at hRewind
  have hHalt : Step prepareDDHChooseCall (rewindFinish.swapTapes.resumeAt 117)
      { rewindFinish.swapTapes.resumeAt 117 with halted := true } := by
    simp [Step, successors, next, prepareDDHChooseCall, prepareDDHChooseRequest,
      prepareDDHPublicPrefix, skipUnary, skipFrame, savePublicPrefix, rewindBitstring,
      copyBitstring, assembleChooseField, writeChooseHeader, readDelimited,
      restoreDDHTuple, GuardedCompiler.seekScratchInput, Program.swapTapes,
      Instruction.swapTapes, TapeId.swap, Program.asSubroutine, Instruction.asSubroutine,
      Configuration.resumeAt, Configuration.swapTapes, Instruction.next]
  let nativeFinish : Configuration := { rewindFinish.swapTapes.resumeAt 117 with halted := true }
  have hNativeRun : RunsFor prepareDDHChooseCall (Configuration.initial input) nativeFinish
      (prepareTime + (2 * restoredPrefix.length + 8) + (3 * restoredBits.length + 3) +
        (2 * sourceBits.length + 4) + 1) :=
    RunsFor.succ (((hPrepare.trans hRestore).trans hSeek).trans hRewind) hHalt
  have hLayout : (nativeFinish.resumeAt 0).Equivalent
      (GuardedCompiler.packInputStart ([none] ++ sourceSaved) scratchBefore sourceBits).swapTapes := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · change rewindFinish.outputTape.Equivalent { left := scratchBefore }
      rw [← hCanonicalRewindOutput]
      exact hRewindEq.2.2.2.symm
    · change rewindFinish.inputTape.Equivalent { Tape.ofBits sourceBits with left := [none] ++ sourceSaved }
      simpa only [List.append_nil] using hRewindEq.2.2.1.symm.trans hCanonicalRewindInput
  obtain ⟨finish, used, hBound, hRun, hHalted⟩ := prepareDDHChooseCall_terminates input
  have hSame : finish = nativeFinish := RunsFor.halted_finish_eq_of_no_randomBit
    hRun hNativeRun hHalted rfl prepareDDHChooseCall_no_randomBit
  have hActualLayout : (finish.resumeAt 0).Equivalent
      (GuardedCompiler.packInputStart ([none] ++ sourceSaved) scratchBefore sourceBits).swapTapes := by
    rw [hSame]
    exact hLayout
  refine ⟨finish, used, [none] ++ sourceSaved, restoredBits.reverse.map some ++ restoredBefore, sourceBits,
    hBound, hRun, hHalted, hActualLayout, ?_⟩
  exact hActualLayout.2.2.2.contiguous_length_le_cells

/-- The guarded source-call entry, forgetting only the explicit blank
at the front of its protected output prefix. -/
theorem prepareDDHChooseCall_terminates_with_layout (input : List Bool) :
    ∃ (finish : Configuration) (used : Nat) (beforeInput beforeOutput : List (Option Bool))
      (sourceInput : List Bool),
      used ≤ 20000000 * (input.length + 1) ∧
      RunsFor prepareDDHChooseCall (Configuration.initial input) finish used ∧
      finish.halted = true ∧
      (finish.resumeAt 0).Equivalent
        (GuardedCompiler.packInputStart beforeInput beforeOutput sourceInput).swapTapes ∧
      sourceInput.length ≤ finish.outputTape.cells := by
  obtain ⟨finish, used, beforeInput, beforeOutput, sourceInput,
    hBound, hRun, hHalted, hLayout, hLength⟩ :=
    prepareDDHChooseCall_terminates_with_separated_layout input
  exact ⟨finish, used, beforeInput, none :: beforeOutput, sourceInput,
    hBound, hRun, hHalted, hLayout, hLength⟩

theorem prepareDDHChooseCall_haltsWithin_anyInput (input : List Bool) :
    HaltsWithin prepareDDHChooseCall input (20000000 * (input.length + 1)) := by
  obtain ⟨finish, used, hBound, hRun, hHalted⟩ := prepareDDHChooseCall_terminates input
  have hHalts : HaltsWith prepareDDHChooseCall input finish.outputBits used := ⟨finish, hRun, hHalted, rfl⟩
  exact (hHalts.haltsWithin_of_no_randomBit prepareDDHChooseCall_no_randomBit).mono hBound

theorem prepareDDHChooseCall_polynomialTime : PolynomialTime prepareDDHChooseCall := by
  refine ⟨fun m => 20000000 * (m + 1), ?_, prepareDDHChooseCall_haltsWithin_anyInput⟩
  exact (PolynomiallyBounded.const 20000000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))

end Machine
