import Foundation.Machine.ReturnFramedPower
import Foundation.Machine.RewindReturnedRequest
import Foundation.Machine.SelectRetainedScalar
import Foundation.Machine.FixedWidthScalarReturn

namespace Machine.NativeKeygenReturn

/-- Return a keypair from the arithmetic call's actual tapes. The public
key is the computed power, and the secret key is the retained same scalar. -/
def program : Program := ((ReturnFramedPower.program.followedBy RewindReturnedRequest.program).followedBy SelectRetainedScalar.program).followedBy FixedWidthScalarReturn.fromEnd

def budget (n : Nat) (modulus scalar generator columns : List Bool) (c : Configuration) : Nat :=
  eraseOutputBlocksSteps [c.outputBits, GuardedCompiler.storedSourceScratchBits columns c.inputTape] +
    frameReturnedResultSteps c.outputBits + 2*c.outputBits.length +
    2*(encodeSecurityParameter n ++ frame (modulus++scalar++generator)).length +
    3*n+3*(modulus++scalar++generator).length+68*scalar.length+128

theorem runs (source : Program) (n : Nat) (modulus scalar generator columns : List Bool)
    (c : Configuration) (hWidth : modulus.length = c.outputBits.length)
    (hScalar : scalar.length = c.outputBits.length) (hGenerator : generator.length = scalar.length)
    (hNonempty : scalar ≠ []) :
    let raw := encodeSecurityParameter n ++ frame (modulus++scalar++generator)
    let returned := (GuardedCompiler.rawResultFrom source columns [none] (none::raw.reverse.map some) c).swapTapes
    ∃ target used, used ≤ budget n modulus scalar generator columns c ∧
      RunsFor program (returned.resumeAt 0) target used ∧ target.halted = true ∧
      target.outputBits = frame c.outputBits ++ frame scalar := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame (modulus++scalar++generator)
  let returned := (GuardedCompiler.rawResultFrom source columns [none] (none::raw.reverse.map some) c).swapTapes
  let tail := List.replicate (2*c.outputTape.cells+2-c.outputBits.length) (none : Option Bool)
  let keyOutput : Tape := {left := (frame c.outputBits).reverse.map some}
  have nonemptyPower : c.outputBits ≠ [] := by
    intro empty
    have zero : scalar.length = 0 := by simpa [empty] using hScalar
    exact hNonempty (List.length_eq_zero_iff.mp zero)
  obtain ⟨a, u, hu, cleanup, aHalt, ai, _, ao⟩ := ReturnFramedPower.runs source columns raw c
  obtain ⟨b, v, hv, rewind, bHalt, bi, bo⟩ := RewindReturnedRequest.runs raw c.outputBits tail keyOutput nonemptyPower
  have rewindEntry : ({inputTape := {left := c.outputBits.reverse.map some ++ none::raw.reverse.map some, right := tail}, outputTape := keyOutput} : Configuration).Equivalent (a.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, ao.symm⟩
    have same : returned.inputTape = ({left := c.outputBits.reverse.map some ++ none::raw.reverse.map some, right := tail} : Tape) := by
      simp [returned, GuardedCompiler.rawResultFrom, GuardedCompiler.extractOutputFinish,
        GuardedCompiler.copyScratchFinish, Configuration.swapTapes, Configuration.outputBits, tail]
    rw [same] at ai
    exact ai.symm
  obtain ⟨ab, ua, ha, first, firstHalt, abi, abo⟩ := cleanup.followedBy_equivalent rewind rewindEntry
    (Nat.zero_le _) rfl aHalt bHalt
  let retained := c.outputBits.map some ++ none::tail
  obtain ⟨selected, z, hz, selectRun, selectHalt, si, so⟩ := SelectRetainedScalar.runs n modulus scalar generator c.outputBits retained hWidth
  have selectEntry : ({inputTape := {({right := raw.map some ++ none::retained} : Tape).moveRight with left := [none]}, outputTape := keyOutput} : Configuration).Equivalent (ab.resumeAt 0) :=
    ⟨rfl, rfl, by simpa only [retained, Configuration.resumeAt, List.cons_append, List.append_assoc] using bi.symm.trans abi, bo.symm.trans abo⟩
  obtain ⟨abc, ub, hb, second, secondHalt, abci, abco⟩ := first.followedBy_equivalent selectRun selectEntry
    (Nat.zero_le _) rfl firstHalt selectHalt
  have inputSelected := si.symm.trans abci
  have outputSelected := so.symm.trans abco
  let before := (SelectRetainedScalar.requestPrefix n modulus scalar generator).reverse.map some ++ [none]
  have beforeNonempty : before ≠ [] := by simp [before]
  cases hBefore : before with
  | nil => exact False.elim (beforeNonempty hBefore)
  | cons previous saved =>
    cases generator with
    | nil =>
      have zero : scalar.length = 0 := by simpa using hGenerator.symm
      exact False.elim (hNonempty (List.length_eq_zero_iff.mp zero))
    | cons bit rest =>
      obtain ⟨keys, k, hk, keyRun, keyHalt, keyBits⟩ := FixedWidthScalarReturn.runs_from_end
        previous saved (some bit) (rest.map some ++ none::retained) scalar c.outputBits hScalar hNonempty
      have keyEntry : ({inputTape := {({right := scalar.map some ++ some bit::(rest.map some ++ none::retained)} : Tape).moveRight with left := previous::saved}, outputTape := keyOutput} : Configuration).Equivalent (abc.resumeAt 0) := by
        have input := inputSelected
        change ({({right := (scalar++bit::rest).map some ++ none::retained} : Tape).moveRight with left := before} : Tape).Equivalent abc.inputTape at input
        rw [hBefore] at input
        simpa only [List.map_append, List.map_cons, List.cons_append, List.append_assoc] using
          (show ({inputTape := {({right := (scalar++bit::rest).map some ++ none::retained} : Tape).moveRight with left := previous::saved}, outputTape := keyOutput} : Configuration).Equivalent (abc.resumeAt 0) from
            ⟨rfl, rfl, input, outputSelected⟩)
      obtain ⟨target, used, bound, run, halt, _, tout⟩ := second.followedBy_equivalent keyRun keyEntry
        (Nat.zero_le _) rfl secondHalt keyHalt
      refine ⟨target, used, ?_, run, halt, ?_⟩
      · change used ≤ eraseOutputBlocksSteps [c.outputBits, GuardedCompiler.storedSourceScratchBits columns c.inputTape] +
          frameReturnedResultSteps c.outputBits + 2*c.outputBits.length + 2*raw.length +
          3*n+3*(modulus++scalar++bit::rest).length+68*scalar.length+128
        change u ≤ eraseOutputBlocksSteps [c.outputBits, GuardedCompiler.storedSourceScratchBits columns c.inputTape] + frameReturnedResultSteps c.outputBits+1 at hu
        omega
      · change target.outputTape.bits = _
        exact tout.bits.symm.trans keyBits

/-- The retained guarded scratch is real storage, so its source-cell
count is bounded by the actual native trace, not an uncharged cleanup. -/
theorem source_cells_le_of_run {code source : Program} {start target : Configuration}
    {used : Nat} (columns request : List Bool) (c : Configuration)
    (run : RunsFor code start target used)
    (output : target.outputTape.Equivalent
      ((GuardedCompiler.rawResultFrom source columns [none]
        (none::request.reverse.map some) c).swapTapes).outputTape) :
    c.inputTape.cells ≤ start.inputTape.cells + start.outputTape.cells + used := by
  have bits := output.bits
  have scratchBits : ((GuardedCompiler.rawResultFrom source columns [none]
      (none::request.reverse.map some) c).swapTapes).outputTape.bits =
      GuardedCompiler.storedSourceScratchBits columns c.inputTape ++ c.outputBits := by
    have left := GuardedCompiler.rawResultFrom_output_storedBlocks source columns []
      (none::request.reverse.map some) c
    change c.outputBits.reverse.map some ++ GuardedCompiler.scratchPrefix
      (columns.reverse.map some ++ [none]) c.inputTape = _ at left
    simp only [GuardedCompiler.rawResultFrom, GuardedCompiler.extractOutputFinish,
      Configuration.swapTapes, Tape.bits]
    change ((c.outputBits.reverse.map some ++ GuardedCompiler.scratchPrefix
      (columns.reverse.map some ++ [none]) c.inputTape).reverse ++ [none]).filterMap id = _
    rw [left]
    simp [savedOutputBlocks, List.filterMap_append, List.reverse_append, List.map_reverse]
  rw [scratchBits] at bits
  have length := congrArg List.length bits
  simp only [List.length_append, GuardedCompiler.storedSourceScratchBits_length] at length
  have tapeBound := target.outputTape.bits_length_le_cells
  have storage := GuardedCompiler.sourceStorage_le_of_run run
  change target.inputTape.cells+target.outputTape.cells ≤ start.inputTape.cells+start.outputTape.cells+used at storage
  omega

/-- Charged return time depends polynomially on the retained request,
the fixed width, and the actual source storage. -/
theorem budget_le (n : Nat) (modulus scalar generator columns : List Bool) (c : Configuration)
    (hModulus : modulus.length = scalar.length) (hGenerator : generator.length = scalar.length)
    (hPower : c.outputBits.length = scalar.length) :
    budget n modulus scalar generator columns c ≤
      8*c.inputTape.cells+4*columns.length+5*n+120*scalar.length+180 := by
  have framing := frameReturnedResult_steps_le c.outputBits
  have scratch := GuardedCompiler.storedSourceScratchBits_length columns c.inputTape
  simp only [budget, eraseOutputBlocksSteps, List.length_append, encodeSecurityParameter,
    List.length_replicate, List.length_singleton, frame, hModulus, hGenerator, hPower] at *
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  apply Program.followedBy_no_randomBit
  · exact Program.followedBy_no_randomBit _ _
      (Program.followedBy_no_randomBit _ _ ReturnFramedPower.no_randomBit RewindReturnedRequest.no_randomBit)
      SelectRetainedScalar.no_randomBit
  · exact FixedWidthScalarReturn.fromEnd_no_randomBit

end Machine.NativeKeygenReturn
