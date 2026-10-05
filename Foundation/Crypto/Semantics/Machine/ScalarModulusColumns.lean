import Foundation.Crypto.Semantics.Machine.SecondColumnGather
import Foundation.Crypto.Semantics.Machine.BinaryHighZeroTrim
import Foundation.Crypto.Semantics.Machine.NativeSequence

namespace Machine.ScalarModulusColumns

/-- Read the scalar modulus from the middle track and erase its high zero
padding using linked native code. The saved output prefix is retained. -/
def program : Program :=
  SecondColumnGather.program.followedBy BinaryHighZeroTrim.program

private theorem middle_eq (first second modulus : List Bool)
    (hFirst : first.length = second.length) (hModulus : modulus.length = second.length) :
    ((first.zip second).zip modulus).map (fun column => column.1.2) = second := by
  induction first generalizing second modulus with
  | nil =>
    have hSecond : second = [] := List.length_eq_zero_iff.mp (by simpa using hFirst.symm)
    subst second
    simp
  | cons a rest ih =>
    cases second with
    | nil => simp at hFirst
    | cons b bs =>
      cases modulus with
      | nil => simp at hModulus
      | cons p ps =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hFirst hModulus
        simpa using ih bs ps hFirst hModulus

/-- The input rows come from the actual framed instance preparation. Their
middle cells contain the fixed-width q code. The final output contains q's
canonical bits, even when q is much smaller than the public field width. -/
theorem runs (first modulus : List Bool) (width q : Nat)
    (before written : List (Option Bool))
    (hFirst : first.length = width) (hModulus : modulus.length = width)
    (hPositive : q ≠ 0) (hFit : q < 2^width) :
    ∃ (target : Configuration) (used : Nat), used ≤ 14*width+7 ∧
      RunsFor program
        ({ inputTape := { Tape.ofBits
            (BinaryColumnSlotFill.fullSlots first (Binary.encode width q) modulus) with left := before }
           outputTape := { left := written } } : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape =
        { left := (BinaryColumnSlotFill.fullSlots first (Binary.encode width q) modulus).reverse.map some ++ before } ∧
      target.outputTape =
        { left := q.bits.reverse.map some ++ written
          right := List.replicate (width-q.bits.length) none } := by
  let columns := (first.zip (Binary.encode width q)).zip modulus
  have hColumns : columns.length = width := by
    simp [columns, hFirst, hModulus]
  have hMiddle : columns.map (fun column => column.1.2) = Binary.encode width q := by
    exact middle_eq first _ modulus (by simpa using hFirst) (by simpa using hModulus)
  let consumed : Tape :=
    { left := (BinaryModularAddition.interleave columns).reverse.map some ++ before }
  let gathered : Configuration :=
    { pc := 13
      halted := true
      inputTape := consumed
      outputTape := { left := (Binary.encode width q).reverse.map some ++ written } }
  let trimmed : Configuration :=
    { pc := 6
      halted := true
      inputTape := consumed
      outputTape := { left := q.bits.reverse.map some ++ written, right := List.replicate (width-q.bits.length) none } }
  have one : RunsFor SecondColumnGather.program
      ({ inputTape := { Tape.ofBits (BinaryModularAddition.interleave columns) with left := before }
         outputTape := { left := written } } : Configuration)
      gathered (10*width+2) := by
    simpa only [hColumns, hMiddle, gathered, consumed] using
      SecondColumnGather.runs_middle columns before written
  have two : RunsFor BinaryHighZeroTrim.program (gathered.resumeAt 0) trimmed
      (4*(width-q.bits.length)+4) := by
    simpa only [gathered, trimmed, Configuration.resumeAt] using
      BinaryHighZeroTrim.runs_number_before consumed written width q hPositive hFit
  obtain ⟨used, hUsed, run⟩ := one.followedBy two (Nat.zero_le _) rfl rfl rfl
  refine ⟨{ trimmed.resumeAt (SecondColumnGather.program.length + BinaryHighZeroTrim.program.length + 2) with halted := true },
    used, by omega, ?_, rfl, rfl, rfl⟩
  simpa only [program, columns, BinaryColumnSlotFill.fullSlots] using run

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _ SecondColumnGather.no_randomBit
    BinaryHighZeroTrim.no_randomBit tape

end Machine.ScalarModulusColumns
