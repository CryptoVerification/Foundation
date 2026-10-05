import Foundation.Machine.FramedExponentPreparation
import Foundation.Machine.ScalarModulusPreparation
import Foundation.Machine.ContextualInput
import Foundation.Machine.ConsumedInputErasure
import Foundation.Machine.SavedBitstringRewind

namespace Machine.SavedFramedScalarInput

/-- Prepare the canonical scalar modulus while retaining the whole public
request below a protecting blank. Unlike the standalone sampler's cleanup,
this code keeps the public parameters available for subsequent arithmetic. -/
def program : Program :=
  ((((FramedExponentPreparation.program.followedBy GuardedCompiler.seekScratchInput).followedBy
    OutputColumnRewind.secondBoundaryToFirst).followedBy ScalarModulusPreparation.program.swapTapes).followedBy
      eraseOutputBlock).followedBy rewindBitstring

def validBudget (n : Nat) (modulus generator : List Bool) : Nat :=
  FramedExponentPreparation.validBudget n modulus (Binary.encode (n+3) 0) generator +
    3*generator.length + 80*(n+3)+50

private theorem getD_append_none (xs : List (Option Bool)) (i : Nat) :
    (xs++[none]).getD i none = xs.getD i none := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => simpa using ih i

theorem runs_valid (n : Nat) (modulus generator : List Bool) (q : Nat)
    (hWidth : modulus.length = n+3) (hPositive : q ≠ 0) (hFit : q < 2^(n+3)) :
    let raw := encodeSecurityParameter n ++ frame (modulus ++ Binary.encode (n+3) q ++ generator)
    ∃ target used, used ≤ validBudget n modulus generator ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent
        {Tape.ofBits q.bits with left :=
          none::(List.replicate (n+3) (some true) ++ none::raw.reverse.map some)} ∧
      target.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  let width := n+3
  let exponent := Binary.encode width q
  let raw := encodeSecurityParameter n ++ frame (modulus ++ exponent ++ generator)
  let prefixBits := encodeSecurityParameter n ++
    List.replicate (modulus++exponent++generator).length true ++ [false] ++ modulus ++ exponent
  let before := prefixBits.reverse.map some
  let bits := BinaryColumnSlotFill.fullSlots (List.replicate width false) exponent modulus
  let columns : Tape := {left := none::bits.reverse.map some}
  let saved : Tape := {left := none::raw.reverse.map some}
  obtain ⟨prepared, u, hu, prepRun, prepHalt, prepInput, prepOutput⟩ :=
    FramedExponentPreparation.runs_valid n modulus exponent generator [] hWidth
      (by simp [exponent, width, hWidth])
  have inputLayout : prepared.inputTape.Equivalent {Tape.ofBits generator with left := before} := by
    simpa [before, prefixBits, encodeSecurityParameter, exponent, List.reverse_append,
      List.map_append, List.append_assoc] using prepInput
  have columnLayout : prepared.outputTape.Equivalent columns := by
    simpa only [columns, bits, width, hWidth] using prepOutput
  have seekRun := seekBitstringNext_runs before generator [] columns
  have seekLayout : (seekBitstringNextStart before generator [] columns).Equivalent
      (prepared.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, columnLayout.symm⟩
    apply Tape.Equivalent.trans _ inputLayout.symm
    rw [seekBitstringNextStart_layout]
    cases generator with
    | nil => exact ⟨rfl, fun _ => rfl, fun i => by cases i <;> rfl⟩
    | cons bit rest =>
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro i
      simpa [Tape.moveRight, Tape.ofBits] using getD_append_none (rest.map some) i
  obtain ⟨actualSeek, a, ha, linked₁, halt₁, input₁, output₁⟩ :=
    prepRun.followedBy_equivalent seekRun seekLayout (Nat.zero_le _) rfl prepHalt rfl
  have savedEq : (seekBitstringNextFinish before generator [] columns).inputTape = saved := by
    rw [seekBitstringNextFinish_layout_cells]
    simp [Tape.moveRight, saved, before, raw, prefixBits,
      frame, List.reverse_append, List.map_append, List.append_assoc]
  have retained : actualSeek.inputTape.Equivalent saved := by
    rw [savedEq] at input₁
    exact input₁.symm
  have columnsRetained : actualSeek.outputTape.Equivalent columns := output₁.symm
  obtain ⟨rewound, b, hb, scanRun, scanHalt, scanInput, scanOutput⟩ :=
    OutputColumnRewind.secondBoundaryToFirst_runs bits saved
  have scanLayout : ({inputTape := saved, outputTape := columns} : Configuration).Equivalent
      (actualSeek.resumeAt 0) := ⟨rfl, rfl, retained.symm, columnsRetained.symm⟩
  obtain ⟨actualScan, c, hc, linked₂, halt₂, input₂, output₂⟩ :=
    linked₁.followedBy_equivalent scanRun scanLayout (Nat.zero_le _) rfl halt₁ scanHalt
  have stillSaved : actualScan.inputTape.Equivalent saved := by
    simpa only [scanInput] using input₂.symm
  have columnsAtFirst : actualScan.outputTape.Equivalent (Tape.ofBits bits) := output₂.symm.trans scanOutput
  obtain ⟨gathered, d, hd, gatherRun, gatherHalt, gatherOutput, gatherInput⟩ :=
    ScalarModulusPreparation.runs_before (none::raw.reverse.map some)
      (List.replicate width false) modulus width q (by simp) hWidth hPositive hFit
  have gatherLayout :
      ({inputTape := Tape.ofBits bits, outputTape := saved} : Configuration).swapTapes.Equivalent
        (actualScan.resumeAt 0) := ⟨rfl, rfl, stillSaved.symm, columnsAtFirst.symm⟩
  obtain ⟨actualGather, e, he, linked₃, halt₃, input₃, output₃⟩ :=
    linked₂.followedBy_equivalent gatherRun.swapTapes gatherLayout (Nat.zero_le _) rfl halt₂ gatherHalt
  have qLayout := input₃.symm.trans gatherOutput
  have consumed : actualGather.outputTape.Equivalent {left := bits.reverse.map some} := output₃.symm.trans gatherInput
  obtain ⟨erased, f, hf, eraseRun, eraseHalt, eraseBlank, erasePreserved⟩ :=
    ConsumedInputErasure.runs bits actualGather.inputTape
  have eraseLayout :
      ({inputTape := {left := bits.reverse.map some ++ [none]},
        outputTape := actualGather.inputTape} : Configuration).swapTapes.Equivalent
          (actualGather.resumeAt 0) :=
    ⟨rfl, rfl, Tape.Equivalent.refl _, (ConsumedInputErasure.outer_blank bits).symm.trans consumed.symm⟩
  obtain ⟨actualErase, h, hh, linked₄, halt₄, input₄, output₄⟩ :=
    linked₃.followedBy_equivalent eraseRun.swapTapes eraseLayout (Nat.zero_le _) rfl halt₃ eraseHalt
  have qPreserved : actualErase.inputTape.Equivalent
      {left := q.bits.reverse.map some ++ none::(List.replicate width (some true) ++ none::raw.reverse.map some),
        right := List.replicate (width-q.bits.length) none} := by
    have preserved : actualErase.inputTape.Equivalent actualGather.inputTape := by
      simpa only [Configuration.swapTapes, erasePreserved] using input₄.symm
    exact preserved.trans qLayout
  have blankOutput : actualErase.outputTape.Equivalent ({} : Tape) := output₄.symm.trans eraseBlank
  let counter := List.replicate width (some true) ++ none::raw.reverse.map some
  have rewindRun := rewindBitstring_runs_saved q.bits counter none
    (List.replicate (width-q.bits.length) none) ({} : Tape)
  have rewindLayout :
      ({inputTape := {left := q.bits.reverse.map some ++ none::counter, right := List.replicate (width-q.bits.length) none},
        outputTape := ({} : Tape)} : Configuration).Equivalent
        (actualErase.resumeAt 0) := ⟨rfl, rfl, qPreserved.symm, blankOutput.symm⟩
  obtain ⟨target, used, hUsed, run, halt, input, output⟩ :=
    linked₄.followedBy_equivalent rewindRun rewindLayout (Nat.zero_le _) rfl halt₄ rfl
  have qLength : q.bits.length ≤ width := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hFit
  have bitsLength : bits.length = 3*width := by
    simp [bits, BinaryColumnSlotFill.fullSlots_length, exponent, hWidth, width]
  have prepBudget : FramedExponentPreparation.validBudget n modulus exponent generator =
      FramedExponentPreparation.validBudget n modulus (Binary.encode (n+3) 0) generator := by
    simp [FramedExponentPreparation.validBudget, exponent, width]
  refine ⟨target, used, ?_, ?_, halt, ?_, output.symm⟩
  · unfold validBudget
    rw [prepBudget] at hu
    omega
  · simpa only [program, ConsumedInputErasure.program, Program.swapTapes_swapTapes,
      exponent, width, List.append_nil] using run
  · exact input.symm.trans (rewindBitstring_saved_input_equivalent q.bits counter (width-q.bits.length))

private theorem template_length (bits : List Bool) :
    (BinaryThirdColumnTemplate.columns bits).length = 3*bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    simp only [BinaryThirdColumnTemplate.columns, List.map_cons,
      BinaryModularAddition.interleave, List.length_cons] at ih ⊢
    omega

theorem validBudget_fixedWidth_polynomiallyBounded (modulus generator : Nat → Nat) :
    PolynomiallyBounded (fun n => validBudget n
      (Binary.encode (n+3) (modulus n)) (Binary.encode (n+3) (generator n))) := by
  apply ((PolynomiallyBounded.const 10000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))).mono
  intro n
  simp only [validBudget, FramedExponentPreparation.validBudget, List.length_append,
    Binary.encode_length, template_length]
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  apply Program.followedBy_no_randomBit
  · apply Program.followedBy_no_randomBit
    · apply Program.followedBy_no_randomBit
      · apply Program.followedBy_no_randomBit
        · apply Program.followedBy_no_randomBit
          · exact FramedExponentPreparation.no_randomBit
          · intro selected; cases selected <;> decide
        · intro selected; cases selected <;> decide
      · exact Program.swapTapes_no_randomBit _ ScalarModulusPreparation.no_randomBit
    · exact eraseOutputBlock_no_randomBit
  · exact rewindBitstring_no_randomBit

end Machine.SavedFramedScalarInput
