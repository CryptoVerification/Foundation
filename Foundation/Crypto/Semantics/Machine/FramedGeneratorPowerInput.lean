import Foundation.Crypto.Semantics.Machine.FramedExponentPreparation
import Foundation.Crypto.Semantics.Machine.NativeSequence

namespace Machine.FramedGeneratorPowerInput

private def protectInput : Program := [.moveRight .input, .halt]

/-- Populate all three power tracks from the actual request, retain that
request (including its scalar) below a guard, and rewind the arithmetic
columns for a native opposite-tape call. -/
def program : Program :=
  (((FramedExponentPreparation.program.followedBy OutputColumnRewind.secondBoundaryToFirst).followedBy
    BinaryColumnSlotFill.program).followedBy protectInput).followedBy OutputColumnRewind.toFirst

private theorem protect_run (before : List (Option Bool)) (output : Tape) :
    RunsFor protectInput
      ({inputTape := {left := before}, outputTape := output} : Configuration)
      ({pc := 1, inputTape := {left := none::before}, outputTape := output, halted := true} : Configuration) 2 := by
  let start : Configuration := {inputTape := {left := before}, outputTape := output}
  let moved := {start with pc := 1, inputTape := start.inputTape.moveRight}
  have one : Step protectInput start moved := by
    simp [Step, successors, next, protectInput, start, moved, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have two : Step protectInput moved {moved with halted := true} := by
    simp [Step, successors, next, protectInput, start, moved, Instruction.next]
  simpa [start, moved, Tape.moveRight] using ((RunsFor.zero _).succ one).succ two

theorem runs_valid (n : Nat) (modulus exponent generator : List Bool)
    (hModulus : modulus.length = n+3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length) :
    let raw := encodeSecurityParameter n ++ frame (modulus++exponent++generator)
    let columns := BinaryColumnSlotFill.fullSlots generator exponent modulus
    ∃ target used,
      used ≤ FramedExponentPreparation.validBudget n modulus exponent generator +
        4*columns.length + 8*generator.length + 30 ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent {left := none::raw.reverse.map some} ∧
      target.outputTape.Equivalent (Tape.ofBits columns) := by
  dsimp only
  let instanceBits := modulus++exponent++generator
  let raw := encodeSecurityParameter n ++ frame instanceBits
  let before := exponent.reverse.map some ++ modulus.reverse.map some ++
    some false::List.replicate instanceBits.length (some true) ++
      some false::List.replicate n (some true)
  let old := BinaryColumnSlotFill.fullSlots (List.replicate modulus.length false) exponent modulus
  let columns := BinaryColumnSlotFill.fullSlots generator exponent modulus
  obtain ⟨prepared, u, hu, preparation, hHalt, hInput, hOutput⟩ :=
    FramedExponentPreparation.runs_valid n modulus exponent generator [] hModulus hExponent
  let input : Tape := {Tape.ofBits generator with left := before}
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
  have fillEval := BinaryColumnSlotFill.eval_context before generator (Tape.ofBits old)
  have oldLeft : {Tape.ofBits old with left := []} = Tape.ofBits old := by cases old <;> rfl
  have fillTape := BinaryColumnSlotFill.fillTape_first_full (List.replicate modulus.length false)
    generator exponent modulus (by simp) hGenerator hExponent []
  rw [oldLeft] at fillTape
  rw [fillTape] at fillEval
  change evalConfigWithin BinaryColumnSlotFill.program
    ({inputTape := input, outputTape := Tape.ofBits old} : Configuration) (8*generator.length+2) =
      PMF.pure ({pc := 10, inputTape := {left := generator.reverse.map some ++ before}, outputTape := {left := columns.reverse.map some ++ []}, halted := true} : Configuration) at fillEval
  let fillTarget : Configuration := {pc := 10, inputTape := {left := generator.reverse.map some ++ before}, outputTape := {left := columns.reverse.map some}, halted := true}
  have fillTrace : PaddedRunsFor BinaryColumnSlotFill.program
      ({inputTape := input, outputTape := Tape.ofBits old} : Configuration) fillTarget (8*generator.length+2) := by
    apply (mem_support_evalConfigWithin_iff _ _ _ _).mp
    rw [fillEval]
    simp [fillTarget]
  obtain ⟨fillUsed, fillBound, fillRun⟩ := fillTrace.toRunsFor_le
  have fillJoin :
      ({inputTape := input, outputTape := Tape.ofBits old} : Configuration).Equivalent (first.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa only [rewindInput, Configuration.resumeAt] using firstInput
    · exact rewindOutput.symm.trans firstOutput
  obtain ⟨filled, y, hy, filledRun, filledHalt, filledInput, filledOutput⟩ :=
    firstRun.followedBy_equivalent fillRun fillJoin (Nat.zero_le _) rfl firstHalt rfl
  let saved := generator.reverse.map some ++ before
  have protect := protect_run saved {left := columns.reverse.map some}
  have protectJoin :
      ({inputTape := {left := saved}, outputTape := {left := columns.reverse.map some}} : Configuration).Equivalent
        (filled.resumeAt 0) := by
    refine ⟨rfl, rfl, filledInput, ?_⟩
    simpa [fillTarget, Configuration.resumeAt] using filledOutput
  obtain ⟨guarded, z, hz, guardedRun, guardedHalt, guardedInput, guardedOutput⟩ :=
    filledRun.followedBy_equivalent protect protectJoin (Nat.zero_le _) rfl filledHalt rfl
  let guardedTape : Tape := {left := none::saved}
  obtain ⟨t, ht, lastRun, lastOutput⟩ := OutputColumnRewind.toFirst_runs columns guardedTape
  have lastJoin :
      (rewindBitstringStart columns guardedTape).swapTapes.Equivalent (guarded.resumeAt 0) :=
    ⟨rfl, rfl, guardedInput, guardedOutput⟩
  obtain ⟨target, used, bound, run, halted, inputResult, outputResult⟩ :=
    guardedRun.followedBy_equivalent lastRun lastJoin (Nat.zero_le _) rfl guardedHalt rfl
  have hOldLength : old.length = columns.length := by
    simp [old, columns, BinaryColumnSlotFill.fullSlots_length, hExponent, hGenerator]
  refine ⟨target, used, ?_, ?_, halted, ?_, outputResult.symm.trans lastOutput⟩
  · change used ≤ FramedExponentPreparation.validBudget n modulus exponent generator +
      4*columns.length + 8*generator.length+30
    omega
  · simpa [program, raw, instanceBits] using run
  · have same : none::saved = none::raw.reverse.map some := by
      simp [saved, before, raw, instanceBits, encodeSecurityParameter, frame,
        List.reverse_append, List.map_append, List.append_assoc]
    simpa [guardedTape, rewindBitstringFinish, Configuration.swapTapes, same, raw, instanceBits] using inputResult.symm

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  apply Program.followedBy_no_randomBit
  · apply Program.followedBy_no_randomBit
    · apply Program.followedBy_no_randomBit
      · exact Program.followedBy_no_randomBit _ _ FramedExponentPreparation.no_randomBit OutputColumnRewind.secondBoundaryToFirst_no_randomBit
      · exact BinaryColumnSlotFill.no_randomBit
    · intro tape; simp [protectInput]
  · exact OutputColumnRewind.toFirst_no_randomBit

end Machine.FramedGeneratorPowerInput
