import Foundation.Machine.ContextualInput
import Foundation.Machine.OppositeCall
import Foundation.Machine.GuardedTrace

namespace Machine

/-- Reach fresh output storage beyond four retained input blocks and
rewind a separately assembled source request. This fixed native code is used
before an opposite-tape guarded source call. It does not execute that call. -/
def prepareStoredCall : Program :=
  GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++
  GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
  GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++
  GuardedCompiler.seekScratchInput.asSubroutine 18 24 ++
  rewindBitstring.swapTapes.asSubroutine 24 29 ++ [.halt]

def prepareStoredCallStart (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat) : Configuration :=
  seekBitstringNextStart beforeInput first
    (second.map some ++ none :: third.map some ++ none :: fourth.map some ++ none :: List.replicate inputBlanks none)
    { left := request.reverse.map some ++ none :: beforeOutput, right := List.replicate outputBlanks none }

def prepareStoredCallFinish (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat) : Configuration :=
  { pc := 29,
    inputTape := {
      left := none :: fourth.reverse.map some ++ none :: third.reverse.map some ++
        none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput
      right := List.replicate (inputBlanks - 1) none },
    outputTape := ({
      left := beforeOutput
      right := request.map some ++ none :: List.replicate outputBlanks none } : Tape).moveRight,
    halted := true }

def prepareStoredCallSteps (first second third fourth request : List Bool) : Nat :=
  3 * (first.length + second.length + third.length + fourth.length) + 2 * request.length + 17

set_option maxHeartbeats 600000 in
theorem prepareStoredCall_runs (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat) :
    RunsFor prepareStoredCall
      (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      (prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      (prepareStoredCallSteps first second third fourth request) := by
  let output : Tape := { left := request.reverse.map some ++ none :: beforeOutput, right := List.replicate outputBlanks none }
  let b₂ := none :: first.reverse.map some ++ beforeInput
  let b₃ := none :: second.reverse.map some ++ b₂
  let b₄ := none :: third.reverse.map some ++ b₃
  let r₄ : List (Option Bool) := List.replicate inputBlanks none
  let r₃ := fourth.map some ++ none :: r₄
  let r₂ := third.map some ++ none :: r₃
  let r₁ := second.map some ++ none :: r₂
  let p₁ := GuardedCompiler.seekScratchInput.asSubroutine 0 6
  let p₂ := GuardedCompiler.seekScratchInput.asSubroutine 6 12
  let p₃ := GuardedCompiler.seekScratchInput.asSubroutine 12 18
  let p₄ := GuardedCompiler.seekScratchInput.asSubroutine 18 24
  let rew := rewindBitstring.swapTapes.asSubroutine 24 29
  have h₁ := (seekBitstringNext_runs beforeInput first r₁ output).withSubroutine_halted_of_closed
    [] GuardedCompiler.seekScratchInput (p₂ ++ p₃ ++ p₄ ++ rew ++ [.halt]) 6
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  have h₁' : RunsFor prepareStoredCall
      (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      ((seekBitstringNextFinish beforeInput first r₁ output).resumeAt 6) (3 * first.length + 3) := by
    simpa [prepareStoredCall, prepareStoredCallStart, Program.withSubroutine, output,
      r₁, r₂, r₃, r₄, p₂, p₃, p₄, rew, Configuration.rebasePc, List.append_assoc] using h₁
  have hStart₂ : (seekBitstringNextFinish beforeInput first r₁ output).resumeAt 6 =
      (seekBitstringNextStart b₂ second r₂ output).rebasePc 6 := by
    cases second <;> simp [seekBitstringNextFinish_layout_cells, seekBitstringNextStart_layout,
      r₁, b₂, Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight]
  rw [hStart₂] at h₁'
  have h₂ := (seekBitstringNext_runs b₂ second r₂ output).withSubroutine_halted_of_closed
    p₁ GuardedCompiler.seekScratchInput (p₃ ++ p₄ ++ rew ++ [.halt]) 12
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareStoredCall ((seekBitstringNextStart b₂ second r₂ output).rebasePc 6)
    ((seekBitstringNextFinish b₂ second r₂ output).resumeAt 12) (3 * second.length + 3) at h₂
  have hStart₃ : (seekBitstringNextFinish b₂ second r₂ output).resumeAt 12 =
      (seekBitstringNextStart b₃ third r₃ output).rebasePc 12 := by
    cases third <;> simp [seekBitstringNextFinish_layout_cells, seekBitstringNextStart_layout,
      r₂, b₃, Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight]
  rw [hStart₃] at h₂
  have h₃ := (seekBitstringNext_runs b₃ third r₃ output).withSubroutine_halted_of_closed
    (p₁ ++ p₂) GuardedCompiler.seekScratchInput (p₄ ++ rew ++ [.halt]) 18
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareStoredCall ((seekBitstringNextStart b₃ third r₃ output).rebasePc 12)
    ((seekBitstringNextFinish b₃ third r₃ output).resumeAt 18) (3 * third.length + 3) at h₃
  have hStart₄ : (seekBitstringNextFinish b₃ third r₃ output).resumeAt 18 =
      (seekBitstringNextStart b₄ fourth r₄ output).rebasePc 18 := by
    cases fourth <;> simp [seekBitstringNextFinish_layout_cells, seekBitstringNextStart_layout,
      r₃, b₄, Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight]
  rw [hStart₄] at h₃
  have h₄ := (seekBitstringNext_runs b₄ fourth r₄ output).withSubroutine_halted_of_closed
    (p₁ ++ p₂ ++ p₃) GuardedCompiler.seekScratchInput (rew ++ [.halt]) 24
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareStoredCall ((seekBitstringNextStart b₄ fourth r₄ output).rebasePc 18)
    ((seekBitstringNextFinish b₄ fourth r₄ output).resumeAt 24) (3 * fourth.length + 3) at h₄
  let scratch : Tape := {
    left := none :: fourth.reverse.map some ++ none :: third.reverse.map some ++
      none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput
    right := List.replicate (inputBlanks - 1) none }
  have hRewind := (rewindScratch_runs_from beforeOutput request none (List.replicate outputBlanks none) scratch).swapTapes.withSubroutine_halted_of_closed
    (p₁ ++ p₂ ++ p₃ ++ p₄) rewindBitstring.swapTapes [.halt] 29
    (by change 0 < 4; decide) rfl rfl
    (Program.controlClosed_swapTapes _ rewindBitstring_control_closed)
  let rewindStart : Configuration := { inputTape := scratch, outputTape := output }
  have hRewindStart : (seekBitstringNextFinish b₄ fourth r₄ output).resumeAt 24 = rewindStart.rebasePc 24 := by
    cases inputBlanks <;> simp [seekBitstringNextFinish_layout_cells, scratch, rewindStart,
      r₄, b₄, b₃, b₂, Configuration.resumeAt, Configuration.rebasePc,
      List.append_assoc, List.replicate_succ, Tape.moveRight]
  rw [hRewindStart] at h₄
  change RunsFor prepareStoredCall (rewindStart.rebasePc 24)
    ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 29)
    (2 * request.length + 4) at hRewind
  have hHalt : Step prepareStoredCall
      ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 29)
      (prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks) := by
    simp [Step, successors, next, prepareStoredCall, GuardedCompiler.seekScratchInput,
      rewindBitstring, Program.swapTapes, Instruction.swapTapes, Program.asSubroutine,
      Instruction.asSubroutine, prepareStoredCallFinish, Configuration.resumeAt, Instruction.next]
  have run := RunsFor.succ ((((h₁'.trans h₂).trans h₃).trans h₄).trans hRewind) hHalt
  convert run using 1
  simp only [prepareStoredCallSteps]
  omega

theorem prepareStoredCall_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ prepareStoredCall := by
  simp [prepareStoredCall, GuardedCompiler.seekScratchInput, rewindBitstring,
    Program.swapTapes, Instruction.swapTapes, Program.asSubroutine, Instruction.asSubroutine]

theorem prepareStoredCall_eval (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat) :
    evalConfigWithin prepareStoredCall
      (prepareStoredCallStart beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      (prepareStoredCallSteps first second third fourth request) =
      PMF.pure (prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks) :=
  (prepareStoredCall_runs beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).evalConfigWithin_eq_pure_of_no_randomBit
    prepareStoredCall_no_randomBit

set_option maxHeartbeats 600000 in
theorem prepareStoredCall_control_closed (c d : Configuration)
    (hPc : c.pc < prepareStoredCall.length) (step : Step prepareStoredCall c d)
    (_hRunning : d.halted = false) : d.pc < prepareStoredCall.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 30 at hPc
  change d.pc < 30
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, prepareStoredCall,
    GuardedCompiler.seekScratchInput, rewindBitstring, Program.swapTapes, Instruction.swapTapes,
    TapeId.swap, Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

private theorem padding_getD (count i : Nat) :
    (List.replicate count (none : Option Bool)).getD i none = none := by
  induction count generalizing i with
  | zero => simp
  | succ count ih => cases i with
    | zero => simp [List.replicate_succ]
    | succ i => simpa only [List.replicate_succ, List.getD_cons_succ] using ih i

private theorem append_padding_getD (cells : List (Option Bool)) (count i : Nat) :
    (cells ++ none :: List.replicate count none).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> simp
  | cons cell cells ih => cases i with
    | zero => rfl
    | succ i => exact ih i

/-- Cell-by-cell equality with the guarded source-call entry. Explicit
outer blanks still occur in the actual result of the preceding native run;
this relation never removes them by a machine operation. -/
theorem prepareStoredCall_call_layout (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat) :
    ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0).Equivalent
      (GuardedCompiler.packInputStart (none :: beforeOutput)
        (none :: fourth.reverse.map some ++ none :: third.reverse.map some ++
          none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput) request).swapTapes := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · refine ⟨rfl, fun _ => rfl, ?_⟩
    intro i
    exact padding_getD (inputBlanks - 1) i
  · cases request with
    | nil =>
        refine ⟨rfl, fun _ => rfl, ?_⟩
        intro i
        exact padding_getD outputBlanks i
    | cons bit rest =>
        refine ⟨rfl, fun _ => rfl, ?_⟩
        intro i
        exact append_padding_getD (rest.map some) outputBlanks i

/-- Invoke any fixed source program on the actually assembled request.
Its budget is evaluated at this request's original length. The complete
returned-state law holds for every observation invariant under redundant
outer blank representations, including subsequent native continuations. -/
theorem prepareStoredCall_evalObservation {α : Type*} (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (observe : Configuration → α)
    (hObserve : ∀ c d, c.Equivalent d → observe c = observe d) :
    (evalConfigWithin (GuardedCompiler.rawCompileOpposite source)
      ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0)
      (GuardedCompiler.rawTraceBudget q request.length)).map observe =
      (evalConfigWithin source (GuardedCompiler.preparedSource request) (q request.length)).map
        (fun c => observe ((GuardedCompiler.rawResultFrom source request (none :: beforeOutput)
          (none :: fourth.reverse.map some ++ none :: third.reverse.map some ++
            none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput) c).swapTapes)) := by
  rw [evalConfigWithin_map_eq_of_equivalent _ _ _
      (prepareStoredCall_call_layout beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks)
      _ observe hObserve,
    GuardedCompiler.rawCompileOpposite_configuration_eval _ _ _ _ q halts, PMF.map_comp]
  rfl

theorem prepareStoredCall_call_haltsFrom (source : Program)
    (beforeInput beforeOutput : List (Option Bool))
    (first second third fourth request : List Bool) (inputBlanks outputBlanks : Nat)
    (q : Nat → Nat) (halts : HaltsWithin source request (q request.length))
    (finish : Configuration)
    (run : PaddedRunsFor (GuardedCompiler.rawCompileOpposite source)
      ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0)
      finish (GuardedCompiler.rawTraceBudget q request.length)) : finish.halted = true := by
  have hMem : finish.halted ∈
      ((evalConfigWithin (GuardedCompiler.rawCompileOpposite source)
        ((prepareStoredCallFinish beforeInput beforeOutput first second third fourth request inputBlanks outputBlanks).resumeAt 0)
        (GuardedCompiler.rawTraceBudget q request.length)).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨finish, (mem_support_evalConfigWithin_iff _ _ _ _).mpr run, rfl⟩
  rw [prepareStoredCall_evalObservation source beforeInput beforeOutput first second third fourth request
    inputBlanks outputBlanks q halts Configuration.halted (fun _ _ h => h.2.1),
    PMF.mem_support_map_iff] at hMem
  obtain ⟨c, _hc, hEq⟩ := hMem
  exact hEq.symm


/-- Each retained-block scan and the opposite-tape request rewind terminates
on arbitrary finite tapes. This is a native preparation-time bound; validity
and the layout required by the subsequent guarded call remain separate. -/
theorem prepareStoredCall_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor prepareStoredCall
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨scan1, t1, hTime1, run1, halt1, _output1⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape input output
  have embedded1 := run1.withSubroutine_halted_of_closed
    [] GuardedCompiler.seekScratchInput (GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++ GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++ GuardedCompiler.seekScratchInput.asSubroutine 18 24 ++ rewindBitstring.swapTapes.asSubroutine 24 29 ++ [.halt]) 6
    (by change 0 < 5; decide) rfl halt1 GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareStoredCall ({ inputTape := input, outputTape := output } : Configuration) (scan1.resumeAt 6) t1 at embedded1
  have toScan2 := embedded1
  obtain ⟨scan2, t2, hTime2, run2, halt2, _output2⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape scan1.inputTape scan1.outputTape
  have embedded2 := run2.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6) GuardedCompiler.seekScratchInput (GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++ GuardedCompiler.seekScratchInput.asSubroutine 18 24 ++ rewindBitstring.swapTapes.asSubroutine 24 29 ++ [.halt]) 12
    (by change 0 < 5; decide) rfl halt2 GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareStoredCall (scan1.resumeAt 6) (scan2.resumeAt 12) t2 at embedded2
  have toScan3 := toScan2.trans embedded2
  obtain ⟨scan3, t3, hTime3, run3, halt3, _output3⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape scan2.inputTape scan2.outputTape
  have embedded3 := run3.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++ GuardedCompiler.seekScratchInput.asSubroutine 6 12) GuardedCompiler.seekScratchInput (GuardedCompiler.seekScratchInput.asSubroutine 18 24 ++ rewindBitstring.swapTapes.asSubroutine 24 29 ++ [.halt]) 18
    (by change 0 < 5; decide) rfl halt3 GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareStoredCall (scan2.resumeAt 12) (scan3.resumeAt 18) t3 at embedded3
  have toScan4 := toScan3.trans embedded3
  obtain ⟨scan4, t4, hTime4, run4, halt4, _output4⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape scan3.inputTape scan3.outputTape
  have embedded4 := run4.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++ GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++ GuardedCompiler.seekScratchInput.asSubroutine 12 18) GuardedCompiler.seekScratchInput (rewindBitstring.swapTapes.asSubroutine 24 29 ++ [.halt]) 24
    (by change 0 < 5; decide) rfl halt4 GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareStoredCall (scan3.resumeAt 18) (scan4.resumeAt 24) t4 at embedded4
  have toScan5 := toScan4.trans embedded4
  obtain ⟨rewound, rewindTime, hRewindTime, rewindRun, rewindHalt, _rewindOutput⟩ :=
    rewindBitstring_terminates_from scan4.outputTape scan4.inputTape
  have swapped := rewindRun.swapTapes
  let physical := rewound.swapTapes
  have embeddedRewind := swapped.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++
      GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
      GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++
      GuardedCompiler.seekScratchInput.asSubroutine 18 24)
    rewindBitstring.swapTapes [.halt] 29
    (by change 0 < 4; decide) rfl rewindHalt
    (Program.controlClosed_swapTapes _ rewindBitstring_control_closed)
  change RunsFor prepareStoredCall (scan4.resumeAt 24) (physical.resumeAt 29) rewindTime at embeddedRewind
  let finish : Configuration := { physical with pc := 29, halted := true }
  have last : Step prepareStoredCall (physical.resumeAt 29) finish := by
    have code : prepareStoredCall[29]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, t1 + t2 + t3 + t4 + rewindTime + 1, ?_,
    RunsFor.succ (toScan5.trans embeddedRewind) last, rfl⟩
  have storage1 := GuardedCompiler.sourceStorage_le_of_run toScan2
  change scan1.inputTape.cells + scan1.outputTape.cells ≤ input.cells + output.cells + (t1) at storage1
  have storage2 := GuardedCompiler.sourceStorage_le_of_run toScan3
  change scan2.inputTape.cells + scan2.outputTape.cells ≤ input.cells + output.cells + (t1 + t2) at storage2
  have storage3 := GuardedCompiler.sourceStorage_le_of_run toScan4
  change scan3.inputTape.cells + scan3.outputTape.cells ≤ input.cells + output.cells + (t1 + t2 + t3) at storage3
  have storage4 := GuardedCompiler.sourceStorage_le_of_run toScan5
  change scan4.inputTape.cells + scan4.outputTape.cells ≤ input.cells + output.cells + (t1 + t2 + t3 + t4) at storage4
  have hLeft : scan4.outputTape.left.length ≤ scan4.outputTape.cells := by
    dsimp only [Tape.cells]; omega
  omega

end Machine
