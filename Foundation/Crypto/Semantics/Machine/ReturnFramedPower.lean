import Foundation.Crypto.Semantics.Machine.StoredGuessLayout
import Foundation.Crypto.Semantics.Machine.NativeSequence
import Foundation.Crypto.Semantics.Machine.ConsumedInputErasure

namespace Machine.ReturnFramedPower

/-- Physically erase the two guarded arithmetic scratch blocks and frame
the power result on the cleared output. The request and result on the
input tape remain intact for returning the same scalar as secret key. -/
def program : Program := (eraseOutputBlocks 2).followedBy frameReturnedResult

theorem runs (source : Program) (columns request : List Bool) (c : Configuration) :
    let returned := (GuardedCompiler.rawResultFrom source columns [none]
      (none::request.reverse.map some) c).swapTapes
    ∃ target used,
      used ≤ eraseOutputBlocksSteps [c.outputBits, GuardedCompiler.storedSourceScratchBits columns c.inputTape] +
        frameReturnedResultSteps c.outputBits + 1 ∧
      RunsFor program (returned.resumeAt 0) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent returned.inputTape ∧
      target.outputBits = frame c.outputBits ∧
      target.outputTape.Equivalent {left := (frame c.outputBits).reverse.map some} := by
  dsimp only
  let returned := (GuardedCompiler.rawResultFrom source columns [none]
    (none::request.reverse.map some) c).swapTapes
  let blocks := [c.outputBits, GuardedCompiler.storedSourceScratchBits columns c.inputTape]
  let erased := eraseOutputBlocksFinish returned.inputTape [] blocks []
  have erasedEval := eraseOutputBlocks_eval returned.inputTape [] blocks []
  have initialEq : eraseOutputBlocksStart returned.inputTape [] blocks [] = returned.resumeAt 0 := by
    have saved := GuardedCompiler.rawResultFrom_output_storedBlocks source columns []
      (none::request.reverse.map some) c
    have outputEq : returned.outputTape = {left := savedOutputBlocks blocks} := by
      change ({left := c.outputBits.reverse.map some ++
        GuardedCompiler.scratchPrefix (columns.reverse.map some ++ [none]) c.inputTape} : Tape) = _
      congr 1
      change c.outputBits.reverse.map some ++
        GuardedCompiler.scratchPrefix (columns.reverse.map some ++ [none]) c.inputTape =
          savedOutputBlocks [c.outputBits, GuardedCompiler.storedSourceScratchBits columns c.inputTape] ++ [] at saved
      simpa only [blocks, List.append_nil] using saved
    change ({inputTape := returned.inputTape, outputTape := {left := savedOutputBlocks blocks ++ []}} : Configuration) = returned.resumeAt 0
    simp only [List.append_nil]
    rw [← outputEq]
    rfl
  rw [initialEq] at erasedEval
  change evalConfigWithin (eraseOutputBlocks 2) (returned.resumeAt 0) (eraseOutputBlocksSteps blocks) = PMF.pure erased at erasedEval
  have eraseTrace : PaddedRunsFor (eraseOutputBlocks 2) (returned.resumeAt 0) erased
      (eraseOutputBlocksSteps blocks) := by
    apply (mem_support_evalConfigWithin_iff _ _ _ _).mp
    rw [erasedEval]
    simp [erased]
  obtain ⟨v, hv, eraseRun⟩ := eraseTrace.toRunsFor_le
  let tail := List.replicate (2*c.outputTape.cells+2-c.outputBits.length) (none : Option Bool)
  let blanks := (blocks.map List.length).sum + blocks.length
  have frameRun := frameReturnedResult_runs (request.reverse.map some) [] tail c.outputBits blanks
  have layout : frameReturnedResultStart (request.reverse.map some) [] tail c.outputBits blanks =
      erased.resumeAt 0 := by
    simp [erased, returned, GuardedCompiler.rawResultFrom, GuardedCompiler.extractOutputFinish,
      GuardedCompiler.copyScratchFinish, frameReturnedResultStart, eraseOutputBlocksFinish, tail, blanks,
      Configuration.swapTapes, Configuration.resumeAt, Configuration.outputBits]
  obtain ⟨target, used, bound, run, halted, input, output⟩ :=
    eraseRun.followedBy_equivalent frameRun (layout ▸ Configuration.Equivalent.refl _)
      (Nat.zero_le _) rfl rfl rfl
  have bits : (frameReturnedResultFinish (request.reverse.map some) [] tail c.outputBits blanks).outputBits =
      frame c.outputBits := by
    simp [frameReturnedResultFinish, Configuration.outputBits, Tape.bits, List.filterMap_append]
  have tape : (frameReturnedResultFinish (request.reverse.map some) [] tail c.outputBits blanks).outputTape.Equivalent
      {left := (frame c.outputBits).reverse.map some} := by
    have rightBlank := Tape.blank_padding_equivalent ((frame c.outputBits).reverse.map some ++ [none])
      (blanks-1-(2*c.outputBits.length+1))
    refine rightBlank.trans ⟨rfl, ?_, fun _ => rfl⟩
    exact (ConsumedInputErasure.outer_blank (frame c.outputBits)).symm.2.1
  refine ⟨target, used, ?_, run, halted, input.symm, output.bits.symm.trans bits, output.symm.trans tape⟩
  change used ≤ eraseOutputBlocksSteps blocks + frameReturnedResultSteps c.outputBits + 1
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _ (eraseOutputBlocks_no_randomBit 2) frameReturnedResult_no_randomBit tape

end Machine.ReturnFramedPower
