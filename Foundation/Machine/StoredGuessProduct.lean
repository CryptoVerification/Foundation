import Foundation.Machine.ContextualInput
import Foundation.Machine.SegmentCopy

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

end Machine
