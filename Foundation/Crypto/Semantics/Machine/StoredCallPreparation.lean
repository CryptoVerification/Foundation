import Foundation.Crypto.Semantics.Machine.ContextualInput
import Foundation.Crypto.Semantics.Machine.OppositeCall
import Foundation.Crypto.Semantics.Machine.GuardedTrace

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


/-- The four retained-block scans and opposite-tape request rewind stop on
arbitrary finite tapes and retain their exact input-head movement. `advance`
describes one native scan to the next blank and one cell beyond it; it is
not a new primitive or an uncharged tape operation. Protocol validity and
freshness for the subsequent guarded call remain separate conditions. -/
private theorem prepareStoredCall_terminates_layout_core (input output : Tape) :
    let advance := fun t : Tape =>
      (Tape.moveRight^[((t.current :: t.right).takeWhile Option.isSome).length + 1]) t
    ∃ finish used, ∃ (request : List Bool) (beforeOutput savedInput : List (Option Bool)),
      used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor prepareStoredCall
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      finish.inputTape = advance (advance (advance (advance input))) ∧
      finish.inputTape.left = none :: savedInput ∧ 3 ≤ savedInput.count none ∧
      request.length ≤ output.left.length ∧
      finish.outputTape = { ({ right := request.map some ++ output.current :: output.right } : Tape).moveRight
        with left := none :: beforeOutput } := by
  dsimp only
  obtain ⟨scan1, t1, hTime1, run1, halt1, output1⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape input output
  have embedded1 := run1.withSubroutine_halted_of_closed
    [] GuardedCompiler.seekScratchInput (GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++ GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++ GuardedCompiler.seekScratchInput.asSubroutine 18 24 ++ rewindBitstring.swapTapes.asSubroutine 24 29 ++ [.halt]) 6
    (by change 0 < 5; decide) rfl halt1 GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareStoredCall ({ inputTape := input, outputTape := output } : Configuration) (scan1.resumeAt 6) t1 at embedded1
  have toScan2 := embedded1
  obtain ⟨scan2, t2, hTime2, run2, halt2, output2⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape scan1.inputTape scan1.outputTape
  have embedded2 := run2.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6) GuardedCompiler.seekScratchInput (GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++ GuardedCompiler.seekScratchInput.asSubroutine 18 24 ++ rewindBitstring.swapTapes.asSubroutine 24 29 ++ [.halt]) 12
    (by change 0 < 5; decide) rfl halt2 GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareStoredCall (scan1.resumeAt 6) (scan2.resumeAt 12) t2 at embedded2
  have toScan3 := toScan2.trans embedded2
  obtain ⟨scan3, t3, hTime3, run3, halt3, output3⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape scan2.inputTape scan2.outputTape
  have embedded3 := run3.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++ GuardedCompiler.seekScratchInput.asSubroutine 6 12) GuardedCompiler.seekScratchInput (GuardedCompiler.seekScratchInput.asSubroutine 18 24 ++ rewindBitstring.swapTapes.asSubroutine 24 29 ++ [.halt]) 18
    (by change 0 < 5; decide) rfl halt3 GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareStoredCall (scan2.resumeAt 12) (scan3.resumeAt 18) t3 at embedded3
  have toScan4 := toScan3.trans embedded3
  obtain ⟨scan4, t4, hTime4, run4, halt4, output4⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape scan3.inputTape scan3.outputTape
  have embedded4 := run4.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++ GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++ GuardedCompiler.seekScratchInput.asSubroutine 12 18) GuardedCompiler.seekScratchInput (rewindBitstring.swapTapes.asSubroutine 24 29 ++ [.halt]) 24
    (by change 0 < 5; decide) rfl halt4 GuardedCompiler.seekScratchInput_control_closed
  change RunsFor prepareStoredCall (scan3.resumeAt 18) (scan4.resumeAt 24) t4 at embedded4
  have toScan5 := toScan4.trans embedded4
  obtain ⟨rewound, request, beforeOutput, hRequestLength, rewindRun,
    rewindHalt, rewindInput, rewindOutput⟩ :=
    rewindBitstring_terminates_with_layout scan4.outputTape scan4.inputTape
  let rewindTime := 2 * request.length + 4
  have hRewindTime : rewindTime ≤ 2 * scan4.outputTape.left.length + 4 := by
    dsimp only [rewindTime]
    omega
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
  have hOutput : scan4.outputTape = output :=
    output4.trans (output3.trans (output2.trans output1))
  have hLeft1 := GuardedCompiler.seekScratchInput_halted_input_left
    input output scan1 t1 run1 halt1
  have hLeft2 := GuardedCompiler.seekScratchInput_halted_input_left
    scan1.inputTape scan1.outputTape scan2 t2 run2 halt2
  have hLeft3 := GuardedCompiler.seekScratchInput_halted_input_left
    scan2.inputTape scan2.outputTape scan3 t3 run3 halt3
  have hLeft4 := GuardedCompiler.seekScratchInput_halted_input_left
    scan3.inputTape scan3.outputTape scan4 t4 run4 halt4
  let savedInput := ((scan3.inputTape.current :: scan3.inputTape.right).takeWhile Option.isSome).reverse ++ scan3.inputTape.left
  refine ⟨finish, t1 + t2 + t3 + t4 + rewindTime + 1, request, beforeOutput, savedInput, ?_,
    RunsFor.succ (toScan5.trans embeddedRewind) last, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have storage1 := GuardedCompiler.sourceStorage_le_of_run toScan2
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
  · have hFirst := (GuardedCompiler.seekScratchInput_halted_input_layout
      input output scan1 t1 run1 halt1).1
    have hSecond := (GuardedCompiler.seekScratchInput_halted_input_layout
      scan1.inputTape scan1.outputTape scan2 t2 run2 halt2).1
    have hThird := (GuardedCompiler.seekScratchInput_halted_input_layout
      scan2.inputTape scan2.outputTape scan3 t3 run3 halt3).1
    have hFourth := (GuardedCompiler.seekScratchInput_halted_input_layout
      scan3.inputTape scan3.outputTape scan4 t4 run4 halt4).1
    change rewound.outputTape = _
    rw [rewindOutput, hFourth, hThird, hSecond, hFirst]
  · change rewound.outputTape.left = _
    rw [rewindOutput]
    exact hLeft4
  · dsimp only [savedInput]
    rw [hLeft3, hLeft2, hLeft1]
    simp only [List.count_append, List.count_cons_self]
    omega
  · simpa only [hOutput] using hRequestLength
  · change rewound.inputTape = _
    simpa only [hOutput, List.singleton_append] using rewindInput

/-- The exact input-head position of the four native scans is retained on
arbitrary tapes. The additional call-entry data remains available through
the stronger layout theorem used for actual guarded source invocations. -/
theorem prepareStoredCall_terminates_with_input_layout (input output : Tape) :
    let advance := fun t : Tape =>
      (Tape.moveRight^[((t.current :: t.right).takeWhile Option.isSome).length + 1]) t
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor prepareStoredCall
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧
      finish.inputTape = advance (advance (advance (advance input))) := by
  obtain ⟨finish, used, _request, _beforeOutput, _savedInput,
    hBound, run, hHalted, hInput, _hLeft, _hCount, _hLength, _hOutput⟩ :=
    prepareStoredCall_terminates_layout_core input output
  exact ⟨finish, used, hBound, run, hHalted, hInput⟩

/-- Each scan and the opposite-tape rewind stops on arbitrary finite tapes.
The stronger input-layout theorem retains the four actual head advances;
stopping alone does not assert a fresh head for the following source call. -/
theorem prepareStoredCall_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor prepareStoredCall
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hBound, run, hHalted, _hInput⟩ :=
    prepareStoredCall_terminates_with_input_layout input output
  exact ⟨finish, used, hBound, run, hHalted⟩


/-- Every padded execution from the retained caller tapes has halted at the
same displayed budget. This uses the actual deterministic stopping trace. -/
theorem prepareStoredCall_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor prepareStoredCall
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (1000000 * (input.cells + output.cells) + 1000000)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ :=
    prepareStoredCall_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted prepareStoredCall_no_randomBit hBound finish trace

-- These private list/tape functions describe the postcondition of the
-- existing charged native scan. They introduce no new machine primitive,
-- tape reset, decoder, or operational shortcut.
private def scanCells (cells : List (Option Bool)) : List (Option Bool) :=
  cells.drop ((cells.takeWhile Option.isSome).length + 1)

private theorem scanCells_cons_some (bit : Bool) (cells : List (Option Bool)) :
    scanCells (some bit :: cells) = scanCells cells := by
  simp [scanCells, List.takeWhile, Nat.add_assoc]

private theorem scanCells_cons_none (cells : List (Option Bool)) :
    scanCells (none :: cells) = cells := by simp [scanCells, List.takeWhile]

private theorem scanCells_drop_suffix (cells : List (Option Bool)) (moves : Nat) :
    ∃ count, scanCells (cells.drop moves) = (scanCells cells).drop count := by
  induction cells generalizing moves with
  | nil => exact ⟨0, by simp [scanCells]⟩
  | cons cell rest ih =>
      cases moves with
      | zero => exact ⟨0, by simp⟩
      | succ moves =>
          cases cell with
          | none =>
              refine ⟨moves + ((rest.drop moves).takeWhile Option.isSome).length + 1, ?_⟩
              rw [List.drop_succ_cons, scanCells_cons_none]
              simp only [scanCells, List.drop_drop, Nat.add_assoc]
          | some bit =>
              obtain ⟨count, hCount⟩ := ih moves
              exact ⟨count, by simpa only [List.drop_succ_cons, scanCells_cons_some] using hCount⟩

private theorem scanCells_iterate_drop_suffix (cells : List (Option Bool)) (moves count : Nat) :
    ∃ skipped, (scanCells^[count]) (cells.drop moves) = ((scanCells^[count]) cells).drop skipped := by
  induction count generalizing moves cells with
  | zero => exact ⟨moves, rfl⟩
  | succ count ih =>
      obtain ⟨skipped, hSkipped⟩ := ih cells moves
      rw [Function.iterate_succ_apply', hSkipped, Function.iterate_succ_apply']
      exact scanCells_drop_suffix _ skipped

private theorem scanCells_block (bits : List Bool) (cells : List (Option Bool)) :
    scanCells (bits.map some ++ none :: cells) = cells := by
  induction bits with
  | nil => exact scanCells_cons_none cells
  | cons bit bits ih => simpa only [List.map_cons, List.cons_append, scanCells_cons_some] using ih

private theorem scanCells_four_blocks (first second third fourth : List Bool)
    (blanks : Nat) :
    (scanCells^[4]) (first.map some ++ none :: second.map some ++ none ::
      third.map some ++ none :: fourth.map some ++ none :: List.replicate blanks none) =
      List.replicate blanks none := by
  change scanCells (scanCells (scanCells (scanCells _))) = _
  simp only [List.append_assoc, List.cons_append]
  rw [scanCells_block, scanCells_block, scanCells_block, scanCells_block]

private theorem cells_getD_drop (cells : List (Option Bool)) (count i : Nat) :
    (cells.drop count).getD i none = cells.getD (count + i) none := by
  induction count generalizing cells with
  | zero => simp
  | succ count ih =>
      cases cells with
      | nil => simp
      | cons cell rest => simpa only [List.drop_succ_cons, Nat.succ_add, List.getD_cons_succ] using ih rest

private theorem cells_takeWhile_eq (first second : List (Option Bool))
    (hCells : ∀ i, first.getD i none = second.getD i none) :
    first.takeWhile Option.isSome = second.takeWhile Option.isSome := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons cell rest =>
          have hCell : cell = none := by simpa using (hCells 0).symm
          simp [hCell, List.takeWhile]
  | cons cell rest ih =>
      cases second with
      | nil =>
          have hCell : cell = none := by simpa using hCells 0
          simp [hCell, List.takeWhile]
      | cons other remaining =>
          have hCell : cell = other := by simpa using hCells 0
          subst other
          have hTail : ∀ i, rest.getD i none = remaining.getD i none := by
            intro i
            simpa using hCells (i + 1)
          cases cell with
          | none => simp [List.takeWhile]
          | some bit => simp [List.takeWhile, ih remaining hTail]

private theorem scanCells_preserves_cells (first second : List (Option Bool))
    (hCells : ∀ i, first.getD i none = second.getD i none) :
    ∀ i, (scanCells first).getD i none = (scanCells second).getD i none := by
  intro i
  simp only [scanCells, cells_getD_drop, cells_takeWhile_eq first second hCells]
  exact hCells _

private theorem scanCells_iterate_preserves_cells (first second : List (Option Bool))
    (hCells : ∀ i, first.getD i none = second.getD i none) (count : Nat) :
    ∀ i, ((scanCells^[count]) first).getD i none = ((scanCells^[count]) second).getD i none := by
  induction count with
  | zero => exact hCells
  | succ count ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact scanCells_preserves_cells _ _ ih

private def scanInput (input : Tape) : Tape :=
  (Tape.moveRight^[((input.current :: input.right).takeWhile Option.isSome).length + 1]) input

private theorem scanInput_cells (input : Tape) :
    ∀ i, ((scanInput input).current :: (scanInput input).right).getD i none =
      (scanCells (input.current :: input.right)).getD i none := by
  intro i
  unfold scanInput
  rw [GuardedCompiler.moveRight_iterate_remaining]
  split
  · rename_i hEmpty
    simp [scanCells, hEmpty]
  · rfl

private theorem scanInput_iterate_cells (input : Tape) (count : Nat) :
    ∀ i, (((scanInput^[count]) input).current :: ((scanInput^[count]) input).right).getD i none =
      ((scanCells^[count]) (input.current :: input.right)).getD i none := by
  induction count with
  | zero => intro i; rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      intro i
      exact (scanInput_cells _ i).trans (scanCells_preserves_cells _ _ ih i)

private theorem scanCells_four_blocks_suffix_blank
    (first second third fourth : List Bool) (blanks moves i : Nat) :
    ((scanCells^[4]) ((first.map some ++ none :: second.map some ++ none ::
      third.map some ++ none :: fourth.map some ++ none :: List.replicate blanks none).drop moves)).getD i none = none := by
  obtain ⟨skipped, hSkipped⟩ := scanCells_iterate_drop_suffix
    (first.map some ++ none :: second.map some ++ none :: third.map some ++
      none :: fourth.map some ++ none :: List.replicate blanks none) moves 4
  rw [hSkipped, scanCells_four_blocks, cells_getD_drop]
  exact (Tape.blank_padding_equivalent [] blanks).2.2 _

/-- Four actual native frontier scans reach blank current/right input cells
from any rightward suffix of four retained raw blocks. A malformed parser
may consume earlier separators, and a virtual outer blank may become
represented. Only the physical remaining cells matter. This theorem does
not assume correctly encoded DDH fields or a normalized source response. -/
theorem prepareStoredCall_halted_input_frontier_of_retained_suffix
    (input output : Tape) (first second third fourth : List Bool) (blanks moves : Nat)
    (hCells : ∀ i, (input.current :: input.right).getD i none =
      ((first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: List.replicate blanks none).drop moves).getD i none)
    {finish : Configuration} {used : Nat}
    (run : RunsFor prepareStoredCall
      ({ inputTape := input, outputTape := output } : Configuration) finish used)
    (hHalted : finish.halted = true) :
    finish.inputTape.current = none ∧ ∀ i, finish.inputTape.right.getD i none = none := by
  obtain ⟨exact, time, _hTime, exactRun, exactHalt, exactInput⟩ :=
    prepareStoredCall_terminates_with_input_layout input output
  have hUnique := run.halted_finish_eq_of_no_randomBit exactRun
    hHalted exactHalt prepareStoredCall_no_randomBit
  have hRemaining : ∀ i,
      (((scanInput^[4]) input).current :: ((scanInput^[4]) input).right).getD i none = none := by
    intro i
    apply (scanInput_iterate_cells input 4 i).trans
    apply (scanCells_iterate_preserves_cells _ _ hCells 4 i).trans
    exact scanCells_four_blocks_suffix_blank first second third fourth blanks moves i
  rw [hUnique, exactInput]
  change (scanInput (scanInput (scanInput (scanInput input)))).current = none ∧
    ∀ i, (scanInput (scanInput (scanInput (scanInput input)))).right.getD i none = none
  refine ⟨?_, ?_⟩
  · simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      List.getD_cons_zero] using hRemaining 0
  · intro i
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      List.getD_cons_succ] using hRemaining (i + 1)

/-- Actual call preparation exposes a guarded source entry on a suffix of
four raw retained blocks and a fresh output frontier. Its request is the
bitstring reached by the native output rewind, not a reloaded input. The
three retained separators behind the input guard remain available to the
result continuation. No protocol decoding or validity premise is used. -/
theorem prepareStoredCall_terminates_with_call_layout_of_retained_suffix
    (input : Tape) (savedOutput : List (Option Bool)) (outputBlanks : Nat)
    (first second third fourth : List Bool) (inputBlanks moves : Nat)
    (hCells : ∀ i, (input.current :: input.right).getD i none =
      ((first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: List.replicate inputBlanks none).drop moves).getD i none) :
    let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
    ∃ finish used, ∃ (request : List Bool) (beforeInput savedInput : List (Option Bool)),
      used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor prepareStoredCall
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ request.length ≤ savedOutput.length ∧ 3 ≤ savedInput.count none ∧
      beforeInput.length + savedInput.length ≤ input.cells + output.cells + used ∧
      (finish.resumeAt 0).Equivalent
        (GuardedCompiler.packInputStart (none :: beforeInput) (none :: savedInput) request).swapTapes := by
  dsimp only
  let output : Tape := { left := savedOutput, right := List.replicate outputBlanks none }
  obtain ⟨finish, used, request, beforeInput, savedInput, hBound, run, hHalted,
    _hInput, hLeft, hCount, hLength, hOutput⟩ := prepareStoredCall_terminates_layout_core input output
  have hFrontier := prepareStoredCall_halted_input_frontier_of_retained_suffix
    input output first second third fourth inputBlanks moves hCells run hHalted
  have hPrefix : beforeInput.length + savedInput.length ≤ GuardedCompiler.sourceStorage finish := by
    simp only [GuardedCompiler.sourceStorage, Tape.cells, hLeft, hOutput, List.length_cons]
    omega
  have hStorage := GuardedCompiler.sourceStorage_le_of_run run
  change GuardedCompiler.sourceStorage finish ≤ input.cells + output.cells + used at hStorage
  refine ⟨finish, used, request, beforeInput, savedInput, hBound, run, hHalted, hLength, hCount,
    hPrefix.trans hStorage, ?_⟩
  refine ⟨rfl, rfl, ?_, ?_⟩
  · refine ⟨hFrontier.1, ?_, hFrontier.2⟩
    intro i
    change finish.inputTape.left.getD i none = (none :: savedInput).getD i none
    rw [hLeft]
  · change finish.outputTape.Equivalent { Tape.ofBits request with left := none :: beforeInput }
    rw [hOutput]
    cases request with
    | nil =>
        refine ⟨rfl, fun _ => rfl, ?_⟩
        intro i
        exact padding_getD outputBlanks i
    | cons bit rest =>
        refine ⟨rfl, fun _ => rfl, ?_⟩
        intro i
        exact append_padding_getD (rest.map some) outputBlanks i

end Machine
