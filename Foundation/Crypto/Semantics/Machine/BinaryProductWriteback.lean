import Foundation.Crypto.Semantics.Machine.BinaryProductWorkspace
import Foundation.Crypto.Semantics.Machine.GuardedOutput
import Foundation.Crypto.Semantics.Machine.BitstringErasure
import Foundation.Crypto.Semantics.Machine.TapeSwap
import Mathlib.Data.List.GetD

set_option maxHeartbeats 1600000

namespace Machine.BinaryProductWriteback

open BinaryProductSelection BinaryProductWorkspace GuardedCompiler

/-- The arithmetic call leaves its result after a blank separator following
its matrix. This code copies that result onto the other physical tape,
erases the temporary result, rewinds both operands, and scatters the result
back into the matrix. Every copy, erasure, separator and rewind is native. -/
def program : Program :=
  [.moveRight .output] ++
  rewindBitstring.asSubroutine 1 6 ++
  copyBitstring.asSubroutine 6 15 ++
  eraseOutputBlock.swapTapes.asSubroutine 15 21 ++
  rewindBitstring.asSubroutine 21 26 ++
  rewindBitstring.swapTapes.asSubroutine 26 31 ++
  scatterProgram.asSubroutine 31 49 ++ [.halt]

def start (columns : List Column) (result : List Bool)
    (saved : List (Option Bool)) : Configuration :=
  { inputTape := { left := result.reverse.map some ++ none :: (matrix columns).reverse.map some },
    outputTape := { left := saved } }

/-- Retained scratch on the other tape is protected by the actual blank
inserted before the result copy. The accumulator alone is overwritten. -/
def finish (columns : List Column) (result : List Bool)
    (saved : List (Option Bool)) : Configuration :=
  { pc := 49,
    inputTape := { left := (matrix (replaceAccumulator columns result)).reverse.map some ++ [none] },
    outputTape := { left := result.reverse.map some ++ none :: saved },
    halted := true }

def budget (width : Nat) : Nat := 40 * width + 24

private theorem matrix_length (columns : List Column) :
    (matrix columns).length = 5 * columns.length := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp [matrix, row, Nat.mul_comm]; omega

private theorem scatter_closed (c d : Configuration)
    (hPc : c.pc < scatterProgram.length) (step : Step scatterProgram c d)
    (_hRunning : d.halted = false) : d.pc < scatterProgram.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 17 at hPc
  change d.pc < 17
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, scatterProgram,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

/-- A contextual source trace becomes an actual trace of the linked code.
The only representation freedom is redundant outer blank padding. -/
private theorem call (pre source suffix : Program) (returnPc : Nat)
    (layout : program = Program.withSubroutine pre source suffix returnPc)
    (canonical returned actual : Configuration) (limit : Nat)
    (hPc : canonical.pc < source.length) (hActive : canonical.halted = false)
    (hHalted : returned.halted = true)
    (hEval : evalConfigWithin source canonical limit = PMF.pure returned)
    (closed : ∀ c d, c.pc < source.length → Step source c d →
      d.halted = false → d.pc < source.length)
    (hLayout : (canonical.rebasePc pre.length).Equivalent actual) :
    ∃ (target : Configuration) (used : Nat), used ≤ limit ∧
      RunsFor program actual target used ∧ (returned.resumeAt returnPc).Equivalent target := by
  have padded : PaddedRunsFor source canonical returned limit := by
    apply (mem_support_evalConfigWithin_iff _ _ _ _).mp
    rw [hEval]
    simp
  obtain ⟨used, hUsed, run⟩ := padded.toRunsFor_le
  have embedded := run.withSubroutine_halted_of_closed pre source suffix returnPc
    hPc hActive hHalted closed
  rw [← layout] at embedded
  obtain ⟨target, hRun, hTarget⟩ := embedded.exists_equivalent hLayout
  exact ⟨target, used, hUsed, hRun, hTarget⟩

private theorem append_blank (bits : List Bool) (blanks : Nat) (saved : List (Option Bool)) :
    (({ left := saved, right := bits.map some ++ List.replicate (blanks + 1) none } : Tape).moveRight).Equivalent
      { Tape.ofBits bits with left := none :: saved } := by
  cases bits with
  | nil =>
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro i
      simpa [Tape.moveRight, Tape.ofBits, List.replicate_succ] using
        (Tape.blank_padding_equivalent (none :: saved) blanks).2.2 i
  | cons bit rest =>
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro i
      simp only [List.map_cons, List.cons_append, Tape.moveRight, Tape.ofBits]
      by_cases hIndex : i < rest.length
      · exact List.getD_append _ _ _ _ (by simpa using hIndex)
      · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt hIndex),
          List.getD_eq_default (rest.map some) none (by simpa using Nat.le_of_not_lt hIndex)]
        exact (Tape.blank_padding_equivalent [] (blanks + 1)).2.2 _

/-- The same physical matrix is restored after a guarded arithmetic call.
Saved caller data stay on the other tape. No fresh machine input is loaded
between the copy, erasure, rewinds and accumulator writes. -/
theorem runs (columns : List Column) (result : List Bool)
    (hLength : result.length = columns.length) (saved : List (Option Bool)) :
    ∃ (target : Configuration) (used : Nat), used ≤ budget columns.length ∧
      RunsFor program (start columns result saved) target used ∧
      (finish columns result saved).Equivalent target := by
  let mat := matrix columns
  let out : Tape := { left := none :: saved }
  let afterMove : Configuration := { start columns result saved with pc := 1, outputTape := out }
  have hMove : Step program (start columns result saved) afterMove := by
    simp [Step, successors, next, program, start, afterMove, out,
      Instruction.next, Configuration.updateTape, Configuration.advance, Tape.moveRight]
  let pre1 : Program := [.moveRight .output]
  let suffix1 := copyBitstring.asSubroutine 6 15 ++
    eraseOutputBlock.swapTapes.asSubroutine 15 21 ++
    rewindBitstring.asSubroutine 21 26 ++ rewindBitstring.swapTapes.asSubroutine 26 31 ++
    scatterProgram.asSubroutine 31 49 ++ [.halt]
  have layout1 : program = Program.withSubroutine pre1 rewindBitstring suffix1 6 := by
    simp [program, Program.withSubroutine, pre1, suffix1, List.append_assoc]
  obtain ⟨s1, u1, hu1, r1, e1⟩ := call pre1 rewindBitstring suffix1 6 layout1
    (rewindScratchStart (mat.reverse.map some) result out)
    (rewindScratchFinish (mat.reverse.map some) result out) afterMove
    (2 * result.length + 4) (by change 0 < _; decide) rfl rfl
    (rewindScratch_eval _ _ _) rewindBitstring_control_closed (by
      exact Configuration.Equivalent.refl _)
  let pre2 := pre1 ++ rewindBitstring.asSubroutine 1 6
  let suffix2 := eraseOutputBlock.swapTapes.asSubroutine 15 21 ++
    rewindBitstring.asSubroutine 21 26 ++ rewindBitstring.swapTapes.asSubroutine 26 31 ++
    scatterProgram.asSubroutine 31 49 ++ [.halt]
  have layout2 : program = Program.withSubroutine pre2 copyBitstring suffix2 15 := by
    simp [program, Program.withSubroutine, pre2, pre1, suffix2, List.append_assoc,
      show rewindBitstring.length = 4 from rfl]
  have copyLayout : (copyScratchStart (none :: (mat.reverse.map some)) (none :: saved) result 0).rebasePc pre2.length =
      (rewindScratchFinish (mat.reverse.map some) result out).resumeAt 6 := by
    change ({
      pc := 6,
      inputTape := { packedLogicalInput result with left := none :: (mat.reverse.map some) },
      outputTape := out } : Configuration) = (rewindScratchFinish (mat.reverse.map some) result out).resumeAt 6
    cases result <;> simp [packedLogicalInput, rewoundTape, rewindScratchFinish,
      Configuration.resumeAt, Tape.moveRight]
  obtain ⟨s2, u2, hu2, r2, e2⟩ := call pre2 copyBitstring suffix2 15 layout2
    (copyScratchStart (none :: (mat.reverse.map some)) (none :: saved) result 0)
    (copyScratchFinish (none :: (mat.reverse.map some)) (none :: saved) result 0) s1
    (copyBitstringSteps result) (by change 0 < _; decide) rfl rfl (copyScratch_eval _ _ _ _)
    copyBitstring_control_closed (copyLayout ▸ e1)
  let output : Tape := { left := result.reverse.map some ++ none :: saved }
  let pre3 := pre2 ++ copyBitstring.asSubroutine 6 15
  let suffix3 := rewindBitstring.asSubroutine 21 26 ++
    rewindBitstring.swapTapes.asSubroutine 26 31 ++ scatterProgram.asSubroutine 31 49 ++ [.halt]
  have layout3 : program = Program.withSubroutine pre3 eraseOutputBlock.swapTapes suffix3 21 := by
    simp [program, Program.withSubroutine, pre3, pre2, pre1, suffix3, List.append_assoc,
      show rewindBitstring.length = 4 from rfl, show copyBitstring.length = 8 from rfl]
  have eraseEval := (eraseOutputBlock_runs output (mat.reverse.map some) result []).swapTapes
    |>.evalConfigWithin_eq_pure_of_no_randomBit (by intro tape; cases tape <;>
      simp [Program.swapTapes, eraseOutputBlock, Instruction.swapTapes])
  obtain ⟨s3, u3, hu3, r3, e3⟩ := call pre3 eraseOutputBlock.swapTapes suffix3 21 layout3
    (eraseOutputBlockStart output (mat.reverse.map some) result []).swapTapes
    (eraseOutputBlockFinish output (mat.reverse.map some) result []).swapTapes s2
    (4 * result.length + 3) (by change 0 < _; decide) rfl rfl eraseEval
    (Program.controlClosed_swapTapes _ eraseOutputBlock_control_closed) (by
      change ({
        pc := 15,
        inputTape := { left := result.reverse.map some ++ none :: (mat.reverse.map some) },
        outputTape := output } : Configuration).Equivalent s2
      simpa [Configuration.resumeAt, copyScratchFinish, output] using e2)
  let pre4 := pre3 ++ eraseOutputBlock.swapTapes.asSubroutine 15 21
  let suffix4 := rewindBitstring.swapTapes.asSubroutine 26 31 ++ scatterProgram.asSubroutine 31 49 ++ [.halt]
  have layout4 : program = Program.withSubroutine pre4 rewindBitstring suffix4 26 := by
    simp [program, Program.withSubroutine, pre4, pre3, pre2, pre1, suffix4, List.append_assoc,
      show rewindBitstring.length = 4 from rfl, show copyBitstring.length = 8 from rfl,
      show eraseOutputBlock.length = 5 from rfl]
  let matrixStart : Configuration :=
    { inputTape := { left := (mat.reverse.map some), right := List.replicate (result.length + 1) none },
      outputTape := output }
  let matrixFinish : Configuration :=
    { pc := 3, inputTape := ({ right := mat.map some ++ none :: List.replicate (result.length + 1) none } : Tape).moveRight,
      outputTape := output, halted := true }
  have matrixEval := (rewindBitstring_runs_from mat none (List.replicate (result.length + 1) none) output).evalConfigWithin_eq_pure_of_no_randomBit rewindBitstring_no_randomBit
  obtain ⟨s4, u4, hu4, r4, e4⟩ := call pre4 rewindBitstring suffix4 26 layout4
    matrixStart matrixFinish s3 (2 * mat.length + 4) (by change 0 < _; decide) rfl rfl matrixEval
    rewindBitstring_control_closed (by
      change ({ pc := 21, inputTape := matrixStart.inputTape, outputTape := output } : Configuration).Equivalent s3
      change ({
        pc := 21,
        inputTape := { left := mat.reverse.map some, right := List.replicate (result.reverse.length + 1) none ++ [] },
        outputTape := output } : Configuration).Equivalent s3 at e3
      simpa [matrixStart] using e3)
  let pre5 := pre4 ++ rewindBitstring.asSubroutine 21 26
  let suffix5 := scatterProgram.asSubroutine 31 49 ++ [.halt]
  have layout5 : program = Program.withSubroutine pre5 rewindBitstring.swapTapes suffix5 31 := by
    simp [program, Program.withSubroutine, pre5, pre4, pre3, pre2, pre1, suffix5, List.append_assoc,
      show rewindBitstring.length = 4 from rfl, show copyBitstring.length = 8 from rfl,
      show eraseOutputBlock.length = 5 from rfl]
  have resultEval := (rewindScratch_runs saved result matrixFinish.inputTape).swapTapes
    |>.evalConfigWithin_eq_pure_of_no_randomBit (by intro tape; cases tape <;>
      simp [Program.swapTapes, rewindBitstring, Instruction.swapTapes])
  obtain ⟨s5, u5, hu5, r5, e5⟩ := call pre5 rewindBitstring.swapTapes suffix5 31 layout5
    (rewindScratchStart saved result matrixFinish.inputTape).swapTapes
    (rewindScratchFinish saved result matrixFinish.inputTape).swapTapes s4
    (2 * result.length + 4) (by change 0 < _; decide) rfl rfl resultEval
    (Program.controlClosed_swapTapes _ rewindBitstring_control_closed) (by
      change ({ pc := 26, inputTape := matrixFinish.inputTape, outputTape := output } : Configuration).Equivalent s4
      exact e4)
  let pre6 := pre5 ++ rewindBitstring.swapTapes.asSubroutine 26 31
  have layout6 : program = Program.withSubroutine pre6 scatterProgram [.halt] 49 := by
    simp [program, Program.withSubroutine, pre6, pre5, pre4, pre3, pre2, pre1, List.append_assoc,
      show rewindBitstring.length = 4 from rfl, show copyBitstring.length = 8 from rfl,
      show eraseOutputBlock.length = 5 from rfl]
  let scattered : Configuration :=
    { pc := 15, inputTape := { left := (matrix (replaceAccumulator columns result)).reverse.map some ++ [none] },
      outputTape := output, halted := true }
  have scatterLayout :
      ((scatterStart [none] (none :: saved) mat result).rebasePc pre6.length).Equivalent
        ((rewindScratchFinish saved result matrixFinish.inputTape).swapTapes.resumeAt 31) := by
    refine ⟨by change pre6.length + 0 = 31; simp [pre6, pre5, pre4, pre3, pre2, pre1, Program.asSubroutine_length,
      show rewindBitstring.length = 4 from rfl, show copyBitstring.length = 8 from rfl,
      show eraseOutputBlock.length = 5 from rfl], rfl, ?_, ?_⟩
    · exact (append_blank mat (result.length + 1) []).symm
    · exact (append_blank result 0 saved).symm
  obtain ⟨s6, u6, hu6, r6, e6⟩ := call pre6 scatterProgram [.halt] 49 layout6
    (scatterStart [none] (none :: saved) mat result) scattered s5
    (11 * columns.length + 2) (by change 0 < _; decide) rfl rfl
    (eval_scatter_context columns result hLength [none] (none :: saved)) scatter_closed
    (⟨scatterLayout.1.trans e5.1, scatterLayout.2.1.trans e5.2.1,
      scatterLayout.2.2.1.trans e5.2.2.1, scatterLayout.2.2.2.trans e5.2.2.2⟩)
  have hLast : Step program s6 { s6 with halted := true } := by
    have hp : s6.pc = 49 := e6.1.symm
    have ha : s6.halted = false := e6.2.1.symm
    have instruction : program[49]? = some .halt := by decide
    simp [Step, successors, next, hp, ha, instruction, Instruction.next]
  have run := (((((RunsFor.succ (RunsFor.zero _) hMove).trans r1).trans r2).trans r3).trans r4).trans r5
    |>.trans r6
  refine ⟨{ s6 with halted := true }, 1 + u1 + u2 + u3 + u4 + u5 + u6 + 1, ?_,
    RunsFor.succ run hLast, ?_⟩
  · have hMat : mat.length = 5 * columns.length := matrix_length columns
    have hCopy := copyBitstringSteps_le result
    dsimp only [budget]
    omega
  · exact e6.withHalted true

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> simp [program, Program.asSubroutine, Program.swapTapes,
    Instruction.asSubroutine, Instruction.swapTapes, rewindBitstring,
    copyBitstring, eraseOutputBlock, scatterProgram]

/-- A common bound from the retained caller configuration covers every
operational branch. The source need not be in a fresh input-loading state. -/
theorem haltsFrom (columns : List Column) (result : List Bool)
    (hLength : result.length = columns.length) (saved : List (Option Bool))
    (target : Configuration)
    (trace : PaddedRunsFor program (start columns result saved) target (budget columns.length)) :
    target.halted = true := by
  obtain ⟨returned, used, hBound, run, hEquivalent⟩ := runs columns result hLength saved
  exact run.haltsFrom_of_no_randomBit hEquivalent.2.1.symm no_randomBit hBound target trace

/-- The observed matrix and result of the linked native writeback code.
The old scratch prefix is retained, rather than reloaded or erased for free. -/
theorem eval (columns : List Column) (result : List Bool)
    (hLength : result.length = columns.length) (saved : List (Option Bool)) :
    (evalConfigWithin program (start columns result saved) (budget columns.length)).map
      (fun c => (c.halted, c.inputTape.bits, c.outputBits)) =
      PMF.pure (true, matrix (replaceAccumulator columns result),
        saved.reverse.filterMap id ++ result) := by
  obtain ⟨returned, used, hBound, run, hEquivalent⟩ := runs columns result hLength saved
  have hAt := run.haltsFrom_of_no_randomBit hEquivalent.2.1.symm no_randomBit (Nat.le_refl used)
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAt,
    run.evalConfigWithin_eq_pure_of_no_randomBit no_randomBit, PMF.pure_map]
  rw [← hEquivalent.2.1, ← hEquivalent.2.2.1.bits, ← hEquivalent.outputBits]
  simp [finish, Configuration.outputBits, Tape.bits, List.filterMap_append]

end Machine.BinaryProductWriteback
