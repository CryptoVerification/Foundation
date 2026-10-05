import Foundation.Crypto.Semantics.Machine.ContextualInput
import Foundation.Crypto.Semantics.Machine.SegmentCopy
import Foundation.Crypto.Semantics.Machine.GuardedTrace
import Foundation.Crypto.Semantics.Machine.StoredGuessInputScratch

namespace Machine

/-- Append the saved raw multiplication result after the delimited state
and ciphertext first component. Reach that result by scanning four actual
retained input blocks, then copy exactly to its terminating blank. No group
operation, list slicing, or arbitrary program selection is a machine step. -/
def appendStoredGuessProduct : Program :=
  GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++
  GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
  GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++
  GuardedCompiler.seekScratchInput.asSubroutine 18 24 ++
  copyBitstring.asSubroutine 24 33 ++ [.halt]

def appendStoredGuessProductStart (beforeInput beforeOutput tail : List (Option Bool))
    (first second third fourth product : List Bool) (blanks : Nat) : Configuration :=
  seekBitstringNextStart beforeInput first
    (second.map some ++ none :: third.map some ++ none :: fourth.map some ++
      none :: product.map some ++ none :: tail)
    { left := beforeOutput, right := List.replicate blanks none }

def appendStoredGuessProductFinish (beforeInput beforeOutput tail : List (Option Bool))
    (first second third fourth product : List Bool) (blanks : Nat) : Configuration :=
  { copySegmentFinish
      (none :: fourth.reverse.map some ++ none :: third.reverse.map some ++
        none :: second.reverse.map some ++ none :: first.reverse.map some ++ beforeInput)
      beforeOutput tail product blanks with pc := 33 }

def appendStoredGuessProductSteps (first second third fourth product : List Bool) : Nat :=
  3*(first.length + second.length + third.length + fourth.length) + 12 + copyBitstringSteps product + 1

set_option maxHeartbeats 600000 in
theorem appendStoredGuessProduct_runs (beforeInput beforeOutput tail : List (Option Bool))
    (first second third fourth product : List Bool) (blanks : Nat) :
    RunsFor appendStoredGuessProduct
      (appendStoredGuessProductStart beforeInput beforeOutput tail first second third fourth product blanks)
      (appendStoredGuessProductFinish beforeInput beforeOutput tail first second third fourth product blanks)
      (appendStoredGuessProductSteps first second third fourth product) := by
  let output : Tape := { left := beforeOutput, right := List.replicate blanks none }
  let b₂ := none :: first.reverse.map some ++ beforeInput
  let b₃ := none :: second.reverse.map some ++ b₂
  let b₄ := none :: third.reverse.map some ++ b₃
  let r₄ := product.map some ++ none :: tail
  let r₃ := fourth.map some ++ none :: r₄
  let r₂ := third.map some ++ none :: r₃
  let r₁ := second.map some ++ none :: r₂
  let p₁ := GuardedCompiler.seekScratchInput.asSubroutine 0 6
  let p₂ := GuardedCompiler.seekScratchInput.asSubroutine 6 12
  let p₃ := GuardedCompiler.seekScratchInput.asSubroutine 12 18
  let p₄ := GuardedCompiler.seekScratchInput.asSubroutine 18 24
  let copier := copyBitstring.asSubroutine 24 33
  have h₁ := (seekBitstringNext_runs beforeInput first r₁ output).withSubroutine_halted_of_closed
    [] GuardedCompiler.seekScratchInput (p₂ ++ p₃ ++ p₄ ++ copier ++ [.halt]) 6
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  have h₁' : RunsFor appendStoredGuessProduct
      (appendStoredGuessProductStart beforeInput beforeOutput tail first second third fourth product blanks)
      ((seekBitstringNextFinish beforeInput first r₁ output).resumeAt 6) (3 * first.length + 3) := by
    simpa [appendStoredGuessProduct, appendStoredGuessProductStart, Program.withSubroutine, output,
      r₁, r₂, r₃, r₄, p₂, p₃, p₄, copier, Configuration.rebasePc, List.append_assoc] using h₁
  have hStart₂ : (seekBitstringNextFinish beforeInput first r₁ output).resumeAt 6 =
      (seekBitstringNextStart b₂ second r₂ output).rebasePc 6 := by
    cases second <;> simp [seekBitstringNextFinish_layout_cells, seekBitstringNextStart_layout,
      r₁, b₂, Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight]
  rw [hStart₂] at h₁'
  have h₂ := (seekBitstringNext_runs b₂ second r₂ output).withSubroutine_halted_of_closed
    p₁ GuardedCompiler.seekScratchInput (p₃ ++ p₄ ++ copier ++ [.halt]) 12
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  change RunsFor appendStoredGuessProduct ((seekBitstringNextStart b₂ second r₂ output).rebasePc 6)
    ((seekBitstringNextFinish b₂ second r₂ output).resumeAt 12) (3 * second.length + 3) at h₂
  have hStart₃ : (seekBitstringNextFinish b₂ second r₂ output).resumeAt 12 =
      (seekBitstringNextStart b₃ third r₃ output).rebasePc 12 := by
    cases third <;> simp [seekBitstringNextFinish_layout_cells, seekBitstringNextStart_layout,
      r₂, b₃, Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight]
  rw [hStart₃] at h₂
  have h₃ := (seekBitstringNext_runs b₃ third r₃ output).withSubroutine_halted_of_closed
    (p₁ ++ p₂) GuardedCompiler.seekScratchInput (p₄ ++ copier ++ [.halt]) 18
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  change RunsFor appendStoredGuessProduct ((seekBitstringNextStart b₃ third r₃ output).rebasePc 12)
    ((seekBitstringNextFinish b₃ third r₃ output).resumeAt 18) (3 * third.length + 3) at h₃
  have hStart₄ : (seekBitstringNextFinish b₃ third r₃ output).resumeAt 18 =
      (seekBitstringNextStart b₄ fourth r₄ output).rebasePc 18 := by
    cases fourth <;> simp [seekBitstringNextFinish_layout_cells, seekBitstringNextStart_layout,
      r₃, b₄, Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight]
  rw [hStart₄] at h₃
  have h₄ := (seekBitstringNext_runs b₄ fourth r₄ output).withSubroutine_halted_of_closed
    (p₁ ++ p₂ ++ p₃) GuardedCompiler.seekScratchInput (copier ++ [.halt]) 24
    (by change 0 < 5; decide) rfl rfl GuardedCompiler.seekScratchInput_control_closed
  change RunsFor appendStoredGuessProduct ((seekBitstringNextStart b₄ fourth r₄ output).rebasePc 18)
    ((seekBitstringNextFinish b₄ fourth r₄ output).resumeAt 24) (3 * fourth.length + 3) at h₄
  let beforeProduct := none :: fourth.reverse.map some ++ b₄
  let copyStart := copySegmentStart beforeProduct beforeOutput tail product blanks
  have hCopyStart : (seekBitstringNextFinish b₄ fourth r₄ output).resumeAt 24 = copyStart.rebasePc 24 := by
    cases product <;> simp [seekBitstringNextFinish_layout_cells, copyStart, copySegmentStart_layout,
      beforeProduct, r₄, output, Configuration.resumeAt, Configuration.rebasePc, Tape.moveRight]
  rw [hCopyStart] at h₄
  have hCopy := (copySegment_runs beforeProduct beforeOutput tail product blanks).withSubroutine_halted_of_closed
    (p₁ ++ p₂ ++ p₃ ++ p₄) copyBitstring [.halt] 33
    (by change 0 < 8; decide) rfl rfl GuardedCompiler.copyBitstring_control_closed
  have hCopyFinish : copySegmentFinish beforeProduct beforeOutput tail product blanks =
      { appendStoredGuessProductFinish beforeInput beforeOutput tail first second third fourth product blanks with pc := 7 } := by
    simp [appendStoredGuessProductFinish, copySegmentFinish, beforeProduct, b₄, b₃, b₂, List.append_assoc]
  rw [hCopyFinish] at hCopy
  change RunsFor appendStoredGuessProduct (copyStart.rebasePc 24)
    ((appendStoredGuessProductFinish beforeInput beforeOutput tail first second third fourth product blanks).resumeAt 33)
    (copyBitstringSteps product) at hCopy
  have hHalt : Step appendStoredGuessProduct
      ((appendStoredGuessProductFinish beforeInput beforeOutput tail first second third fourth product blanks).resumeAt 33)
      (appendStoredGuessProductFinish beforeInput beforeOutput tail first second third fourth product blanks) := by
    simp [Step, successors, next, appendStoredGuessProduct, GuardedCompiler.seekScratchInput,
      copyBitstring, Program.asSubroutine, Instruction.asSubroutine, appendStoredGuessProductFinish,
      copySegmentFinish, Configuration.resumeAt, Instruction.next]
  have run := RunsFor.succ ((((h₁'.trans h₂).trans h₃).trans h₄).trans hCopy) hHalt
  convert run using 1
  simp only [appendStoredGuessProductSteps]
  omega

theorem appendStoredGuessProduct_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ appendStoredGuessProduct := by
  simp [appendStoredGuessProduct, GuardedCompiler.seekScratchInput, copyBitstring,
    Program.asSubroutine, Instruction.asSubroutine]

theorem appendStoredGuessProduct_eval (beforeInput beforeOutput tail : List (Option Bool))
    (first second third fourth product : List Bool) (blanks : Nat) :
    evalConfigWithin appendStoredGuessProduct
      (appendStoredGuessProductStart beforeInput beforeOutput tail first second third fourth product blanks)
      (appendStoredGuessProductSteps first second third fourth product) =
      PMF.pure (appendStoredGuessProductFinish beforeInput beforeOutput tail first second third fourth product blanks) :=
  (appendStoredGuessProduct_runs _ _ _ _ _ _ _ _ _).evalConfigWithin_eq_pure_of_no_randomBit
    appendStoredGuessProduct_no_randomBit

theorem appendStoredGuessProduct_steps_le (first second third fourth product : List Bool) :
    appendStoredGuessProductSteps first second third fourth product ≤
      3*(first.length + second.length + third.length + fourth.length) + 6*product.length + 15 := by
  have h := copyBitstringSteps_le product
  simp only [appendStoredGuessProductSteps]
  omega

set_option maxHeartbeats 600000 in
theorem appendStoredGuessProduct_control_closed (c d : Configuration)
    (hPc : c.pc < appendStoredGuessProduct.length) (step : Step appendStoredGuessProduct c d)
    (_hRunning : d.halted = false) : d.pc < appendStoredGuessProduct.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 34 at hPc
  change d.pc < 34
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, appendStoredGuessProduct,
    GuardedCompiler.seekScratchInput, copyBitstring, Program.asSubroutine, Instruction.asSubroutine,
    subroutineAddress, Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]


/-- Appending the stored product also stops on arbitrary finite tapes. All
four frontier scans and every copied bit are charged native transitions. -/
private theorem appendStoredGuessProduct_terminates_core (input output : Tape) :
    let advance := fun t : Tape =>
      (Tape.moveRight^[((t.current :: t.right).takeWhile Option.isSome).length + 1]) t
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor appendStoredGuessProduct
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.inputTape.current = none ∧
      finish.inputTape.moveRight = advance (advance (advance (advance (advance input)))) ∧
      ∀ before blanks, output = ({ left := before, right := List.replicate blanks none } : Tape) →
        ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none } := by
  dsimp only
  obtain ⟨scan1, t1, hTime1, run1, halt1, output1⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape input output
  have embedded1 := run1.withSubroutine_halted_of_closed
    [] GuardedCompiler.seekScratchInput (GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++ GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++ GuardedCompiler.seekScratchInput.asSubroutine 18 24 ++ copyBitstring.asSubroutine 24 33 ++ [.halt]) 6
    (by change 0 < 5; decide) rfl halt1 GuardedCompiler.seekScratchInput_control_closed
  change RunsFor appendStoredGuessProduct ({ inputTape := input, outputTape := output } : Configuration) (scan1.resumeAt 6) t1 at embedded1
  have toScan2 := embedded1
  obtain ⟨scan2, t2, hTime2, run2, halt2, output2⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape scan1.inputTape scan1.outputTape
  have embedded2 := run2.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6) GuardedCompiler.seekScratchInput (GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++ GuardedCompiler.seekScratchInput.asSubroutine 18 24 ++ copyBitstring.asSubroutine 24 33 ++ [.halt]) 12
    (by change 0 < 5; decide) rfl halt2 GuardedCompiler.seekScratchInput_control_closed
  change RunsFor appendStoredGuessProduct (scan1.resumeAt 6) (scan2.resumeAt 12) t2 at embedded2
  have toScan3 := toScan2.trans embedded2
  obtain ⟨scan3, t3, hTime3, run3, halt3, output3⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape scan2.inputTape scan2.outputTape
  have embedded3 := run3.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++ GuardedCompiler.seekScratchInput.asSubroutine 6 12) GuardedCompiler.seekScratchInput (GuardedCompiler.seekScratchInput.asSubroutine 18 24 ++ copyBitstring.asSubroutine 24 33 ++ [.halt]) 18
    (by change 0 < 5; decide) rfl halt3 GuardedCompiler.seekScratchInput_control_closed
  change RunsFor appendStoredGuessProduct (scan2.resumeAt 12) (scan3.resumeAt 18) t3 at embedded3
  have toScan4 := toScan3.trans embedded3
  obtain ⟨scan4, t4, hTime4, run4, halt4, output4⟩ :=
    GuardedCompiler.seekScratchInput_terminates_from_anyTape scan3.inputTape scan3.outputTape
  have embedded4 := run4.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++ GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++ GuardedCompiler.seekScratchInput.asSubroutine 12 18) GuardedCompiler.seekScratchInput (copyBitstring.asSubroutine 24 33 ++ [.halt]) 24
    (by change 0 < 5; decide) rfl halt4 GuardedCompiler.seekScratchInput_control_closed
  change RunsFor appendStoredGuessProduct (scan3.resumeAt 18) (scan4.resumeAt 24) t4 at embedded4
  have toScan5 := toScan4.trans embedded4

  obtain ⟨copied, copyTime, hCopyTime, copyRun, copyHalt⟩ :=
    copyBitstring_terminates_from_anyTape scan4.inputTape scan4.outputTape
  have hCopy := copyRun.withSubroutine_halted_of_closed
    (GuardedCompiler.seekScratchInput.asSubroutine 0 6 ++
      GuardedCompiler.seekScratchInput.asSubroutine 6 12 ++
      GuardedCompiler.seekScratchInput.asSubroutine 12 18 ++
      GuardedCompiler.seekScratchInput.asSubroutine 18 24) copyBitstring [.halt] 33
    (by change 0 < 8; decide) rfl copyHalt GuardedCompiler.copyBitstring_control_closed
  change RunsFor appendStoredGuessProduct (scan4.resumeAt 24) (copied.resumeAt 33) copyTime at hCopy
  let finish : Configuration := { copied with pc := 33, halted := true }
  have last : Step appendStoredGuessProduct (copied.resumeAt 33) finish := by
    have code : appendStoredGuessProduct[33]? = some .halt := rfl
    simp [Step, successors, next, code, Configuration.resumeAt, finish, Instruction.next]
  obtain ⟨hCopyInput, hCopyBlank⟩ :=
    copyBitstring_halted_input_layout scan4.inputTape scan4.outputTape copied copyTime copyRun copyHalt
  refine ⟨finish, t1 + t2 + t3 + t4 + copyTime + 1, ?_,
    RunsFor.succ (toScan5.trans hCopy) last, rfl, hCopyBlank, ?_, ?_⟩
  · have storage1 := GuardedCompiler.sourceStorage_le_of_run toScan2
    change scan1.inputTape.cells + scan1.outputTape.cells ≤ input.cells + output.cells + (t1) at storage1
    have storage2 := GuardedCompiler.sourceStorage_le_of_run toScan3
    change scan2.inputTape.cells + scan2.outputTape.cells ≤ input.cells + output.cells + (t1 + t2) at storage2
    have storage3 := GuardedCompiler.sourceStorage_le_of_run toScan4
    change scan3.inputTape.cells + scan3.outputTape.cells ≤ input.cells + output.cells + (t1 + t2 + t3) at storage3
    have storage4 := GuardedCompiler.sourceStorage_le_of_run toScan5
    change scan4.inputTape.cells + scan4.outputTape.cells ≤ input.cells + output.cells + (t1 + t2 + t3 + t4) at storage4
    omega
  · let advance := fun t : Tape =>
      (Tape.moveRight^[((t.current :: t.right).takeWhile Option.isSome).length + 1]) t
    have input1 := (GuardedCompiler.seekScratchInput_halted_input_layout input output
      scan1 t1 run1 halt1).1
    have input2 := (GuardedCompiler.seekScratchInput_halted_input_layout scan1.inputTape scan1.outputTape
      scan2 t2 run2 halt2).1
    have input3 := (GuardedCompiler.seekScratchInput_halted_input_layout scan2.inputTape scan2.outputTape
      scan3 t3 run3 halt3).1
    have input4 := (GuardedCompiler.seekScratchInput_halted_input_layout scan3.inputTape scan3.outputTape
      scan4 t4 run4 halt4).1
    have hNext : copied.inputTape.moveRight = advance scan4.inputTape := by
      rw [hCopyInput]
      dsimp only [advance]
      rw [Function.iterate_succ_apply']
    change copied.inputTape.moveRight = advance (advance (advance (advance (advance input))))
    rw [hNext, input4, input3, input2, input1]
  · intro before blanks hOutput
    have hEntry := output4.trans (output3.trans (output2.trans (output1.trans hOutput)))
    obtain ⟨fresh, freshTime, after, remaining, _hFreshTime, freshRun, freshHalt, freshOutput⟩ :=
      copyBitstring_terminates_with_output_layout scan4.inputTape before blanks
    rw [hEntry] at copyRun
    have hSame := copyRun.halted_finish_eq_of_no_randomBit freshRun copyHalt freshHalt copyBitstring_no_randomBit
    refine ⟨after, remaining, ?_⟩
    change copied.outputTape = _
    rw [hSame]
    exact freshOutput

theorem appendStoredGuessProduct_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor appendStoredGuessProduct
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true := by
  obtain ⟨finish, used, hBound, run, hHalted, _hBlank, _hInput, _hLayout⟩ :=
    appendStoredGuessProduct_terminates_core input output
  exact ⟨finish, used, hBound, run, hHalted⟩

/-- The native scans leave the other tape unchanged, and copying the actual
returned product retains its fresh output frontier. The retained blocks need
not satisfy a cryptographic parsing predicate for this tape-layout fact. -/
theorem appendStoredGuessProduct_terminates_with_output_layout (input : Tape)
    (before : List (Option Bool)) (blanks : Nat) :
    ∃ finish used after remaining,
      used ≤ 1000000 * (input.cells +
        ({ left := before, right := List.replicate blanks none } : Tape).cells) + 1000000 ∧
      RunsFor appendStoredGuessProduct
        ({ inputTape := input, outputTape := { left := before, right := List.replicate blanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.outputTape = { left := after, right := List.replicate remaining none } := by
  obtain ⟨finish, used, hBound, run, hHalted, _hBlank, _hInput, hLayout⟩ :=
    appendStoredGuessProduct_terminates_core input { left := before, right := List.replicate blanks none }
  obtain ⟨after, remaining, hOutput⟩ := hLayout before blanks rfl
  exact ⟨finish, used, after, remaining, hBound, run, hHalted, hOutput⟩

/-- Four native scans followed by copying stop on the fifth block's first
blank. One further mathematical head move identifies precisely the tape
position returned by five native scans. The extra move is a postcondition,
not an instruction silently added to this copy routine. -/
theorem appendStoredGuessProduct_terminates_with_input_layout (input output : Tape) :
    let advance := fun t : Tape =>
      (Tape.moveRight^[((t.current :: t.right).takeWhile Option.isSome).length + 1]) t
    ∃ finish used, used ≤ 1000000 * (input.cells + output.cells) + 1000000 ∧
      RunsFor appendStoredGuessProduct
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.inputTape.current = none ∧
      finish.inputTape.moveRight = advance (advance (advance (advance (advance input)))) := by
  obtain ⟨finish, used, hBound, run, hHalted, hBlank, hInput, _hLayout⟩ :=
    appendStoredGuessProduct_terminates_core input output
  exact ⟨finish, used, hBound, run, hHalted, hBlank, hInput⟩

/-- From a suffix of the five retained bit blocks, the final product copy
leaves both physical heads at fresh blank frontiers. The source tape is the
same tape observed by the five-scan certificate, one cell before its return.
The blocks may contain malformed frames or raw replies; validity is not a
premise. Fresh output is preserved by actual one-bit copying. -/
private theorem appendStoredGuessProduct_frontier_of_scan
    (input : Tape) (beforeOutput : List (Option Bool)) (outputBlanks : Nat)
    (frontier : Configuration) (frontierTime : Nat) (afterInput : List (Option Bool)) (remaining : Nat)
    (frontierRun : RunsFor seekGuessInputScratch
      ({ inputTape := input, outputTape := { left := beforeOutput, right := List.replicate outputBlanks none } } : Configuration)
      frontier frontierTime)
    (frontierHalt : frontier.halted = true)
    (frontierInput : frontier.inputTape =
      { left := none :: afterInput, right := List.replicate remaining none }) :
    ∃ finish used afterInput inputRemaining afterOutput outputRemaining,
      used ≤ 1000000 * (input.cells +
        ({ left := beforeOutput, right := List.replicate outputBlanks none } : Tape).cells) + 1000000 ∧
      RunsFor appendStoredGuessProduct
        ({ inputTape := input, outputTape := { left := beforeOutput, right := List.replicate outputBlanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate inputRemaining none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate outputRemaining none } := by
  let output : Tape := { left := beforeOutput, right := List.replicate outputBlanks none }
  obtain ⟨finish, used, hBound, run, hHalted, hBlank, hInput, hLayout⟩ :=
    appendStoredGuessProduct_terminates_core input output
  obtain ⟨afterOutput, outputRemaining, hOutput⟩ := hLayout beforeOutput outputBlanks rfl
  obtain ⟨scanned, scanTime, _scanBound, scanRun, scanHalt, _scanOutput, scanInput⟩ :=
    seekGuessInputScratch_terminates_with_input_layout input output
  have hScanned := scanRun.halted_finish_eq_of_no_randomBit frontierRun
    scanHalt frontierHalt seekGuessInputScratch_no_randomBit
  have hNext : finish.inputTape.moveRight =
      { left := none :: afterInput, right := List.replicate remaining none } := by
    rw [hInput, ← scanInput, hScanned, frontierInput]
  have hRightBlank : finish.inputTape.right = List.replicate finish.inputTape.right.length none := by
    cases hTape : finish.inputTape with
    | mk left current right =>
        cases right with
        | nil => rfl
        | cons cell rest =>
            simp only [hTape, Tape.moveRight, Tape.mk.injEq] at hNext
            rcases hNext with ⟨_hLeft, hCell, hRest⟩
            simp only [hCell, hRest, List.length_cons, List.length_replicate, List.replicate_succ]
  refine ⟨finish, used, finish.inputTape.left, finish.inputTape.right.length,
    afterOutput, outputRemaining, hBound, run, hHalted, ?_, hOutput⟩
  cases hTape : finish.inputTape with
  | mk left current right =>
      have hCurrent : current = none := by simpa only [hTape] using hBlank
      have hRight : right = List.replicate right.length none := by simpa only [hTape] using hRightBlank
      change ({ left := left, current := current, right := right } : Tape) = _
      rw [hCurrent]
      exact congrArg (fun remaining : List (Option Bool) => ({ left := left, right := remaining } : Tape)) hRight

/-- A suffix of five retained blocks under a bit head supplies the scratch
position used by the product copy. Neither malformed fields nor an arbitrary
saved output prefix change the fresh return frontiers. -/
theorem appendStoredGuessProduct_terminates_with_suffix_frontier
    (input : Tape) (beforeOutput : List (Option Bool)) (outputBlanks : Nat)
    (first second third fourth fifth : List Bool) (padding count : Nat) (bit : Bool)
    (hCurrent : input.current = some bit)
    (hRight : input.right =
      (first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: fifth.map some ++ none ::
          List.replicate padding none).drop count) :
    ∃ finish used afterInput inputRemaining afterOutput outputRemaining,
      used ≤ 1000000 * (input.cells +
        ({ left := beforeOutput, right := List.replicate outputBlanks none } : Tape).cells) + 1000000 ∧
      RunsFor appendStoredGuessProduct
        ({ inputTape := input, outputTape := { left := beforeOutput, right := List.replicate outputBlanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate inputRemaining none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate outputRemaining none } := by
  obtain ⟨frontier, frontierTime, afterInput, remaining, _hBound,
    frontierRun, frontierHalt, _hOutput, hInput⟩ :=
    seekGuessInputScratch_terminates_with_separated_frontier input
      { left := beforeOutput, right := List.replicate outputBlanks none }
      first second third fourth fifth padding count bit hCurrent hRight
  exact appendStoredGuessProduct_frontier_of_scan input beforeOutput outputBlanks
    frontier frontierTime afterInput remaining frontierRun frontierHalt hInput

/-- The blank-head case uses the leading blank and four remaining retained
blocks. The copy still returns fresh input and output tapes, including when
the head denotes an empty or truncated last field of an earlier block. -/
theorem appendStoredGuessProduct_terminates_with_suffix_frontier_of_blank
    (input : Tape) (beforeOutput : List (Option Bool)) (outputBlanks : Nat)
    (first second third fourth : List Bool) (padding count : Nat)
    (hCurrent : input.current = none)
    (hRight : input.right =
      (first.map some ++ none :: second.map some ++ none :: third.map some ++
        none :: fourth.map some ++ none :: List.replicate padding none).drop count) :
    ∃ finish used afterInput inputRemaining afterOutput outputRemaining,
      used ≤ 1000000 * (input.cells +
        ({ left := beforeOutput, right := List.replicate outputBlanks none } : Tape).cells) + 1000000 ∧
      RunsFor appendStoredGuessProduct
        ({ inputTape := input, outputTape := { left := beforeOutput, right := List.replicate outputBlanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate inputRemaining none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate outputRemaining none } := by
  obtain ⟨frontier, frontierTime, afterInput, remaining, _hBound,
    frontierRun, frontierHalt, _hOutput, hInput⟩ :=
    seekGuessInputScratch_terminates_with_separated_frontier_of_blank input
      { left := beforeOutput, right := List.replicate outputBlanks none }
      first second third fourth padding count hCurrent hRight
  exact appendStoredGuessProduct_frontier_of_scan input beforeOutput outputBlanks
    frontier frontierTime afterInput remaining frontierRun frontierHalt hInput

theorem appendStoredGuessProduct_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (trace : PaddedRunsFor appendStoredGuessProduct
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (1000000 * (input.cells + output.cells) + 1000000)) : finish.halted = true := by
  obtain ⟨target, used, hBound, run, hHalted⟩ := appendStoredGuessProduct_terminates_from_anyTape input output
  exact run.haltsFrom_of_no_randomBit hHalted appendStoredGuessProduct_no_randomBit hBound finish trace

/-- Full-stream suffix form of the product-copy frontier. It accepts either
a bit or a blank current cell, and also the virtual blank after all retained
cells have been consumed. The exact five-scan and native-copy positions
identify the same fresh input and output frontiers. -/
theorem appendStoredGuessProduct_terminates_with_stream_frontier
    (input : Tape) (beforeOutput : List (Option Bool)) (outputBlanks : Nat)
    (first second third fourth fifth : List Bool) (padding count : Nat)
    (hStream : input.current :: input.right =
      let remaining :=
        (first.map some ++ none :: second.map some ++ none :: third.map some ++
          none :: fourth.map some ++ none :: fifth.map some ++ none ::
            List.replicate padding none).drop count
      if remaining = [] then [none] else remaining) :
    ∃ finish used afterInput inputRemaining afterOutput outputRemaining,
      used ≤ 1000000 * (input.cells +
        ({ left := beforeOutput, right := List.replicate outputBlanks none } : Tape).cells) + 1000000 ∧
      RunsFor appendStoredGuessProduct
        ({ inputTape := input, outputTape := { left := beforeOutput, right := List.replicate outputBlanks none } } : Configuration)
        finish used ∧ finish.halted = true ∧
      finish.inputTape = { left := afterInput, right := List.replicate inputRemaining none } ∧
      finish.outputTape = { left := afterOutput, right := List.replicate outputRemaining none } := by
  obtain ⟨frontier, frontierTime, afterInput, remaining, _hBound,
    frontierRun, frontierHalt, _hOutput, hInput⟩ :=
    seekGuessInputScratch_terminates_with_stream_frontier input
      { left := beforeOutput, right := List.replicate outputBlanks none }
      first second third fourth fifth padding count hStream
  exact appendStoredGuessProduct_frontier_of_scan input beforeOutput outputBlanks
    frontier frontierTime afterInput remaining frontierRun frontierHalt hInput

end Machine
