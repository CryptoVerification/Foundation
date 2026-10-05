import Foundation.Machine.ReturnFramedPower
import Foundation.Machine.JoinReturnedResult

namespace Machine.ReturnJoinedPower

/-- Clean the guarded arithmetic workspace, join the actual result to its
retained request, rewind the joined input, and clear the framed work output.
The result remains in input cells for later powers and multiplication. -/
def program : Program := (ReturnFramedPower.program.followedBy JoinReturnedResult.program).followedBy eraseOutputBlock

def budget (columns : List Bool) (request : List Bool) (c : Configuration) : Nat :=
  eraseOutputBlocksSteps [c.outputBits, GuardedCompiler.storedSourceScratchBits columns c.inputTape] +
    frameReturnedResultSteps c.outputBits + 10*c.outputBits.length+2*request.length+
      4*(frame c.outputBits).length+22

theorem runs (source : Program) (columns request : List Bool) (c : Configuration) :
    let returned := (GuardedCompiler.rawResultFrom source columns [none]
      (none::request.reverse.map some) c).swapTapes
    ∃ target used, used ≤ budget columns request c ∧
      RunsFor program (returned.resumeAt 0) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits (request++c.outputBits)) ∧
      target.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  let returned := (GuardedCompiler.rawResultFrom source columns [none]
    (none::request.reverse.map some) c).swapTapes
  let bits := c.outputBits
  let blanks := 2*c.outputTape.cells+2-bits.length
  let output : Tape := {left := (frame bits).reverse.map some}
  obtain ⟨cleaned, u, hu, cleanup, cleanedHalt, ci, _, co⟩ := ReturnFramedPower.runs source columns request c
  obtain ⟨joined, v, hv, joining, joinedHalt, ji, jo⟩ := JoinReturnedResult.runs request bits blanks output
  have layout : ({inputTape := {left := bits.reverse.map some ++ none::request.reverse.map some, right := List.replicate blanks none}, outputTape := output} : Configuration).Equivalent (cleaned.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, co.symm⟩
    have same : returned.inputTape = {left := bits.reverse.map some ++ none::request.reverse.map some, right := List.replicate blanks none} := by
      simp [returned, bits, blanks, GuardedCompiler.rawResultFrom, GuardedCompiler.extractOutputFinish,
        GuardedCompiler.copyScratchFinish, Configuration.swapTapes, Configuration.outputBits]
    rw [same] at ci
    exact ci.symm
  obtain ⟨middle, a, ha, first, halt, input, out⟩ := cleanup.followedBy_equivalent joining layout
    (Nat.zero_le _) rfl cleanedHalt joinedHalt
  let joinedBits := request++bits
  have erase := eraseOutputBlock_runs (Tape.ofBits joinedBits) [] (frame bits) []
  have eraseEntry : (eraseOutputBlockStart (Tape.ofBits joinedBits) [] (frame bits) []).Equivalent
      (middle.resumeAt 0) := by
    refine ⟨rfl, rfl, ji.symm.trans input, ?_⟩
    change ({left := (frame bits).reverse.map some ++ [none]} : Tape).Equivalent (middle.resumeAt 0).outputTape
    exact (ConsumedInputErasure.outer_blank (frame bits)).symm.trans (jo.symm.trans out)
  obtain ⟨target, used, bound, run, halted, ti, targetOutput⟩ :=
    first.followedBy_equivalent erase eraseEntry (Nat.zero_le _) rfl halt rfl
  refine ⟨target, used, ?_, run, halted, ti.symm, ?_⟩
  · change used ≤ eraseOutputBlocksSteps [bits, GuardedCompiler.storedSourceScratchBits columns c.inputTape] +
      frameReturnedResultSteps bits + 10*bits.length+2*request.length+4*(frame bits).length+22
    change u ≤ eraseOutputBlocksSteps [bits, GuardedCompiler.storedSourceScratchBits columns c.inputTape] + frameReturnedResultSteps bits + 1 at hu
    omega
  · apply Tape.Equivalent.trans targetOutput.symm
    change ({right := List.replicate ((frame bits).reverse.length+1) none ++ []} : Tape).Equivalent ({} : Tape)
    simpa only [List.append_nil] using Tape.blank_padding_equivalent [] ((frame bits).reverse.length+1)

theorem budget_le (columns request : List Bool) (c : Configuration) :
    budget columns request c ≤ 8*c.inputTape.cells+4*columns.length+
      2*request.length+40*c.outputBits.length+100 := by
  have framing := frameReturnedResult_steps_le c.outputBits
  have scratch := GuardedCompiler.storedSourceScratchBits_length columns c.inputTape
  simp only [budget, eraseOutputBlocksSteps, frame, List.length_append,
    List.length_replicate, List.length_singleton] at *
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _
    (Program.followedBy_no_randomBit _ _ ReturnFramedPower.no_randomBit JoinReturnedResult.no_randomBit)
    eraseOutputBlock_no_randomBit tape

end Machine.ReturnJoinedPower
