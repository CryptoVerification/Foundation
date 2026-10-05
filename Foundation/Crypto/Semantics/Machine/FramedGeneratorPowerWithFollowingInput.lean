import Foundation.Crypto.Semantics.Machine.FramedExponentPreparation
import Foundation.Crypto.Semantics.Machine.InstanceBaseCopy
import Foundation.Crypto.Semantics.Machine.ContextualInput
import Foundation.Crypto.Semantics.Machine.NativeSequence

namespace Machine.FramedGeneratorPowerWithFollowingInput

private theorem getD_append_none (xs : List (Option Bool)) (i : Nat) :
    (xs++[none]).getD i none = xs.getD i none := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => simpa using ih i

/-- Populate all three power tracks from the actual request, retain that
request (including its scalar) below a guard, and rewind the arithmetic
columns for a native opposite-tape call. -/
def program : Program :=
  (((FramedExponentPreparation.program.followedBy OutputColumnRewind.secondBoundaryToFirst).followedBy
    InstanceBaseCopy.program).followedBy GuardedCompiler.seekScratchInput).followedBy OutputColumnRewind.toFirst

theorem runs_valid (n : Nat) (modulus exponent generator following : List Bool)
    (hModulus : modulus.length = n+3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length) :
    let raw := encodeSecurityParameter n ++ frame (modulus++exponent++generator++following)
    let columns := BinaryColumnSlotFill.fullSlots generator exponent modulus
    ∃ target used,
      used ≤ FramedExponentPreparation.validBudget n modulus exponent (generator++following) +
        4*columns.length + 9*generator.length + 3*following.length + 40 ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent {left := none::raw.reverse.map some} ∧
      target.outputTape.Equivalent (Tape.ofBits columns) := by
  dsimp only
  let instanceBits := modulus++exponent++generator++following
  let raw := encodeSecurityParameter n ++ frame instanceBits
  let before := exponent.reverse.map some ++ modulus.reverse.map some ++
    some false::List.replicate instanceBits.length (some true) ++
      some false::List.replicate n (some true)
  let old := BinaryColumnSlotFill.fullSlots (List.replicate modulus.length false) exponent modulus
  let columns := BinaryColumnSlotFill.fullSlots generator exponent modulus
  obtain ⟨prepared, u, hu, preparation, hHalt, hInput, hOutput⟩ :=
    FramedExponentPreparation.runs_valid n modulus exponent (generator++following) [] hModulus hExponent
  let input : Tape := {Tape.ofBits (generator++following) with left := before}
  obtain ⟨rewound, v, hv, rewindRun, rewindHalt, rewindInput, rewindOutput⟩ :=
    OutputColumnRewind.secondBoundaryToFirst_runs old input
  have join :
      ({inputTape := input, outputTape := {left := none::old.reverse.map some}} : Configuration).Equivalent
        (prepared.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa [input, before, instanceBits, List.append_assoc, Configuration.resumeAt] using hInput.symm
    · exact hOutput.symm
  obtain ⟨first, x, hx, firstRun, firstHalt, firstInput, firstOutput⟩ :=
    preparation.followedBy_equivalent rewindRun join (Nat.zero_le _) rfl hHalt rewindHalt
  obtain ⟨fillTarget, fillUsed, fillBound, fillRun, fillHalt, fillInput, fillOutput⟩ :=
    InstanceBaseCopy.runs_first (List.replicate modulus.length false) generator exponent modulus following
      (by simp) hGenerator hExponent before
  have fillJoin :
      ({inputTape := input, outputTape := Tape.ofBits old} : Configuration).Equivalent (first.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa only [rewindInput, Configuration.resumeAt] using firstInput
    · exact rewindOutput.symm.trans firstOutput
  obtain ⟨filled, y, hy, filledRun, filledHalt, filledInput, filledOutput⟩ :=
    firstRun.followedBy_equivalent fillRun fillJoin (Nat.zero_le _) rfl firstHalt fillHalt
  let saved := following.reverse.map some ++ generator.reverse.map some ++ before
  have protect := seekBitstringNext_runs (generator.reverse.map some ++ before) following []
    {left := columns.reverse.map some}
  have protectJoin : (seekBitstringNextStart (generator.reverse.map some ++ before) following []
      {left := columns.reverse.map some}).Equivalent (filled.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · apply Tape.Equivalent.trans _ (fillInput ▸ filledInput)
      rw [seekBitstringNextStart_layout]
      cases following with
      | nil => exact ⟨rfl, fun _ => rfl, fun i => by cases i <;> rfl⟩
      | cons bit rest =>
        refine ⟨rfl, fun _ => rfl, ?_⟩
        intro i
        simpa [Tape.moveRight, Tape.ofBits] using getD_append_none (rest.map some) i
    · simpa only [seekBitstringNextStart_layout, fillOutput, Configuration.resumeAt] using filledOutput
  obtain ⟨guarded, z, hz, guardedRun, guardedHalt, guardedInput, guardedOutput⟩ :=
    filledRun.followedBy_equivalent protect protectJoin (Nat.zero_le _) rfl filledHalt rfl
  let guardedTape : Tape := {left := none::saved}
  obtain ⟨t, ht, lastRun, lastOutput⟩ := OutputColumnRewind.toFirst_runs columns guardedTape
  have lastJoin :
      (rewindBitstringStart columns guardedTape).swapTapes.Equivalent (guarded.resumeAt 0) :=
    ⟨rfl, rfl, by simpa [seekBitstringNextFinish_layout_cells, saved, guardedTape, rewindBitstringStart, Configuration.swapTapes, Configuration.resumeAt, Tape.moveRight, List.append_assoc] using guardedInput,
      by simpa [seekBitstringNextFinish_layout_cells, rewindBitstringStart, Configuration.swapTapes, Configuration.resumeAt] using guardedOutput⟩
  obtain ⟨target, used, bound, run, halted, inputResult, outputResult⟩ :=
    guardedRun.followedBy_equivalent lastRun lastJoin (Nat.zero_le _) rfl guardedHalt rfl
  have hOldLength : old.length = columns.length := by
    simp [old, columns, BinaryColumnSlotFill.fullSlots_length, hExponent, hGenerator]
  refine ⟨target, used, ?_, ?_, halted, ?_, outputResult.symm.trans lastOutput⟩
  · change used ≤ FramedExponentPreparation.validBudget n modulus exponent (generator++following) +
      4*columns.length + 9*generator.length+3*following.length+40
    omega
  · simpa [program, raw, instanceBits] using run
  · have same : none::saved = none::raw.reverse.map some := by
      simp [saved, before, raw, instanceBits, encodeSecurityParameter, frame,
        List.reverse_append, List.map_append, List.append_assoc]
    simpa [guardedTape, rewindBitstringFinish, seekBitstringNextFinish_layout, Configuration.swapTapes, same, raw, instanceBits] using inputResult.symm

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  apply Program.followedBy_no_randomBit
  · apply Program.followedBy_no_randomBit
    · apply Program.followedBy_no_randomBit
      · exact Program.followedBy_no_randomBit _ _ FramedExponentPreparation.no_randomBit OutputColumnRewind.secondBoundaryToFirst_no_randomBit
      · exact InstanceBaseCopy.no_randomBit
    · exact GuardedCompiler.seekScratchInput_no_randomBit
  · exact OutputColumnRewind.toFirst_no_randomBit

end Machine.FramedGeneratorPowerWithFollowingInput
