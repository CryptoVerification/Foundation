import Foundation.Crypto.Semantics.Machine.FramedExponentPreparation
import Foundation.Crypto.Semantics.Machine.ChooseWorkspaceClear
import Foundation.Crypto.Semantics.Machine.ConsumedInputErasure
import Foundation.Crypto.Semantics.Machine.ScalarModulusPreparation

namespace Machine.FramedScalarPreparation

private def clear : Program := ChooseWorkspaceClear.program.swapTapes
private def scan : Program := OutputColumnRewind.secondBoundaryToFirst
private def gather : Program := ScalarModulusPreparation.program.swapTapes

/-- Prepare the scalar sampler from the real framed p,q,g request. All
copies, counter writes, input erasure, rewinds, and high-zero removal are
finite native instructions. The original field width is retained below a
blank immediately before the canonical q block. -/
def program : Program :=
  (((FramedExponentPreparation.program.followedBy clear).followedBy scan).followedBy gather).followedBy
    eraseOutputBlock

/-- A public budget for valid requests, independent of the numeric value of
q. In particular, it does not charge 2^(n+3) trials to a small modulus. -/
def validBudget (n : Nat) (modulus generator : List Bool) : Nat :=
  let w := n+3
  FramedExponentPreparation.validBudget n modulus (List.replicate w false) generator +
    100*(3*w+2 + (n+1+(modulus.length+w+generator.length)+1+modulus.length+w+generator.length+2) + 1) +
    (6*w+7) + (30*w+18) + (12*w+3) + 4

theorem runs_valid (n : Nat) (modulus generator : List Bool) (q : Nat)
    (hWidth : modulus.length = n+3) (hPositive : q ≠ 0) (hFit : q < 2^(n+3)) :
    ∃ (target : Configuration) (used : Nat), used ≤ validBudget n modulus generator ∧
      RunsFor program (Configuration.initial
        (encodeSecurityParameter n ++ frame (modulus ++ Binary.encode (n+3) q ++ generator))) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { left := q.bits.reverse.map some ++ none :: List.replicate (n+3) (some true)
          right := List.replicate ((n+3)-q.bits.length) none } ∧
      target.outputTape.Equivalent ({} : Tape) := by
  let width := n+3
  let exponent := Binary.encode width q
  let instanceBits := modulus ++ exponent ++ generator
  let bits := BinaryColumnSlotFill.fullSlots (List.replicate width false) exponent modulus
  let columns : Tape := { left := none :: bits.reverse.map some }
  let prefixBits := encodeSecurityParameter n ++ List.replicate instanceBits.length true ++ [false] ++ modulus ++ exponent
  let dirty : Tape := { Tape.ofBits generator with left := prefixBits.reverse.map some ++ [none] }
  obtain ⟨prepared, u, hu, prepRun, prepHalt, prepInput, prepOutput⟩ :=
    FramedExponentPreparation.runs_valid n modulus exponent generator [] hWidth
      (by simp [exponent, width, hWidth])
  have prefixEq : prefixBits.reverse.map some = exponent.reverse.map some ++ modulus.reverse.map some ++
      some false :: List.replicate instanceBits.length (some true) ++
        some false :: List.replicate n (some true) := by
    simp [prefixBits, encodeSecurityParameter, List.reverse_append, List.map_append,
      List.append_assoc]
  have dirtyInput : dirty.Equivalent prepared.inputTape := by
    have outer := (ConsumedInputErasure.outer_blank prefixBits).symm
    have same : dirty.Equivalent
        { Tape.ofBits generator with left := prefixBits.reverse.map some } := by
      exact ⟨rfl, outer.2.1, fun _ => rfl⟩
    apply same.trans
    simpa only [prefixEq, List.append_nil, List.append_assoc, instanceBits] using prepInput.symm
  have savedColumns : columns.Equivalent prepared.outputTape := by
    simpa only [columns, bits, width, hWidth] using prepOutput.symm
  obtain ⟨cleared, v, hv, clearRun, clearHalt, clearPreserved, clearBlank⟩ :=
    ChooseWorkspaceClear.runs_bits_bounded prefixBits generator columns
  have clearLayout :
      ({ inputTape := columns, outputTape := dirty } : Configuration).swapTapes.Equivalent (prepared.resumeAt 0) :=
    ⟨rfl, rfl, dirtyInput, savedColumns⟩
  obtain ⟨actualClear, a, ha, linked₁, halt₁, input₁, output₁⟩ :=
    prepRun.followedBy_equivalent clearRun.swapTapes clearLayout (Nat.zero_le _) rfl prepHalt clearHalt
  have inputBlank : actualClear.inputTape.Equivalent ({} : Tape) := input₁.symm.trans clearBlank
  have outputColumns : actualClear.outputTape.Equivalent columns := by
    simpa only [Configuration.swapTapes, clearPreserved] using output₁.symm
  obtain ⟨rewound, b, hb, scanRun, scanHalt, scanInput, scanOutput⟩ :=
    OutputColumnRewind.secondBoundaryToFirst_runs bits ({} : Tape)
  have scanLayout : ({ inputTape := ({} : Tape), outputTape := columns } : Configuration).Equivalent
      (actualClear.resumeAt 0) := ⟨rfl, rfl, inputBlank.symm, outputColumns.symm⟩
  obtain ⟨actualScan, c, hc, linked₂, halt₂, input₂, output₂⟩ :=
    linked₁.followedBy_equivalent scanRun scanLayout (Nat.zero_le _) rfl halt₁ scanHalt
  have inputStillBlank : actualScan.inputTape.Equivalent ({} : Tape) := by
    simpa only [scanInput] using input₂.symm
  have outputAtFirst : actualScan.outputTape.Equivalent (Tape.ofBits bits) := output₂.symm.trans scanOutput
  obtain ⟨gathered, d, hd, gatherRun, gatherHalt, gatherOutput, gatherInput⟩ :=
    ScalarModulusPreparation.runs (List.replicate width false) modulus width q
      (by simp) hWidth hPositive hFit
  have gatherLayout : (Configuration.initial bits).swapTapes.Equivalent (actualScan.resumeAt 0) :=
    ⟨rfl, rfl, inputStillBlank.symm, outputAtFirst.symm⟩
  obtain ⟨actualGather, e, he, linked₃, halt₃, input₃, output₃⟩ :=
    linked₂.followedBy_equivalent gatherRun.swapTapes gatherLayout (Nat.zero_le _) rfl halt₂ gatherHalt
  have retained : actualGather.inputTape.Equivalent
      { left := q.bits.reverse.map some ++ none :: List.replicate width (some true)
        right := List.replicate (width-q.bits.length) none } := input₃.symm.trans gatherOutput
  have consumedColumns : actualGather.outputTape.Equivalent { left := bits.reverse.map some } :=
    output₃.symm.trans gatherInput
  obtain ⟨erased, f, hf, eraseRun, eraseHalt, eraseBlank, erasePreserved⟩ :=
    ConsumedInputErasure.runs bits actualGather.inputTape
  have eraseLayout :
      ({ inputTape := { left := bits.reverse.map some ++ [none] },
         outputTape := actualGather.inputTape } : Configuration).swapTapes.Equivalent (actualGather.resumeAt 0) :=
    ⟨rfl, rfl, Tape.Equivalent.refl _,
      (ConsumedInputErasure.outer_blank bits).symm.trans consumedColumns.symm⟩
  obtain ⟨target, used, hUsed, linked₄, halt₄, input₄, output₄⟩ :=
    linked₃.followedBy_equivalent eraseRun.swapTapes eraseLayout (Nat.zero_le _) rfl halt₃ eraseHalt
  have hBits : bits.length = 3*width := by
    simp [bits, BinaryColumnSlotFill.fullSlots_length, exponent, hWidth, width]
  have hColumnsCells : columns.cells = 3*width+2 := by
    simp [columns, Tape.cells, hBits]
  have hDirtyCells : dirty.cells ≤ prefixBits.length+generator.length+2 := by
    cases generator <;> simp [dirty, Tape.cells, Tape.ofBits] <;> omega
  have hPrefixLength : prefixBits.length =
      n+1+(modulus.length+width+generator.length)+1+modulus.length+width := by
    simp [prefixBits, encodeSecurityParameter, instanceBits, exponent]
    omega
  have hPrepBudget : FramedExponentPreparation.validBudget n modulus exponent generator =
      FramedExponentPreparation.validBudget n modulus (List.replicate width false) generator := by
    simp [FramedExponentPreparation.validBudget, exponent]
  refine ⟨target, used, ?_, ?_, halt₄, ?_, output₄.symm.trans eraseBlank⟩
  · change used ≤ FramedExponentPreparation.validBudget n modulus (List.replicate width false) generator +
      100*(3*width+2 + (n+1+(modulus.length+width+generator.length)+1+modulus.length+width+generator.length+2)+1) +
      (6*width+7)+(30*width+18)+(12*width+3)+4
    change v ≤ 100*(columns.cells+dirty.cells+1) at hv
    rw [hColumnsCells] at hv
    rw [hPrepBudget] at hu
    simp only [FramedExponentPreparation.validBudget, List.length_append,
      List.length_replicate] at hu ⊢
    omega
  · simpa only [program, clear, scan, gather, ConsumedInputErasure.program,
      Program.swapTapes_swapTapes, instanceBits, exponent, width, List.append_nil] using linked₄
  · have preserved : erased.swapTapes.inputTape = actualGather.inputTape := erasePreserved
    have same := input₄.symm
    rw [preserved] at same
    simpa only [width] using same.trans retained

private theorem template_length (bits : List Bool) :
    (BinaryThirdColumnTemplate.columns bits).length = 3*bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    simp only [BinaryThirdColumnTemplate.columns, List.map_cons,
      BinaryModularAddition.interleave, List.length_cons] at ih ⊢
    omega

/-- Fixed-width representations have a polynomial preparation budget for
arbitrary numeric profiles; no lower bound on q relative to the width is
assumed or hidden in this certificate. -/
theorem validBudget_fixedWidth_polynomiallyBounded (modulus generator : Nat → Nat) :
    PolynomiallyBounded (fun n => validBudget n
      (Binary.encode (n+3) (modulus n)) (Binary.encode (n+3) (generator n))) := by
  apply ((PolynomiallyBounded.const 10000).mul
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))).mono
  intro n
  simp only [validBudget, FramedExponentPreparation.validBudget, List.length_append,
    List.length_replicate, Binary.encode_length, template_length]
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  apply Program.followedBy_no_randomBit
  · apply Program.followedBy_no_randomBit
    · apply Program.followedBy_no_randomBit
      · apply Program.followedBy_no_randomBit
        · exact FramedExponentPreparation.no_randomBit
        · exact Program.swapTapes_no_randomBit _ ChooseWorkspaceClear.no_randomBit
      · intro selected; cases selected <;> native_decide
    · exact Program.swapTapes_no_randomBit _ ScalarModulusPreparation.no_randomBit
  · exact eraseOutputBlock_no_randomBit

end Machine.FramedScalarPreparation
