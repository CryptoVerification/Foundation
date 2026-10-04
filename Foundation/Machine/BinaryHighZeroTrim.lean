import Foundation.Machine.TapeEquivalence
import Foundation.Machine.FixedWidthOutputPadding

namespace Machine.BinaryHighZeroTrim

/-- Erase high zero cells from the output, whose head is just after its
contiguous bit block. The final head is just after the retained canonical
block. No natural-number computation is a machine instruction. -/
def program : Program :=
  [.moveLeft .output, .branch .output 5 2 5, .erase .output,
   .moveLeft .output, .jump 1, .moveRight .output, .halt]

private def trimFinish (input : Tape) (low : List Bool) (before : List (Option Bool)) (blanks : Nat) : Configuration :=
  { pc := 6
    halted := true
    inputTape := input
    outputTape := { left := (low++[true]).reverse.map some ++ before
                    right := List.replicate (blanks-1) none } }

/-- In the loop, the currently inspected zero is counted separately from
zeros still on the left. Each erased zero costs four actual transitions. -/
private def state (input : Tape) (low : List Bool) (before : List (Option Bool)) : Nat → Nat → Configuration
  | 0, blanks =>
    { pc := 1
      inputTape := input
      outputTape := { left := low.reverse.map some ++ before
                      current := some true
                      right := List.replicate blanks none } }
  | zeros+1, blanks =>
    { pc := 1
      inputTape := input
      outputTape := { left := List.replicate zeros (some false) ++ (low++[true]).reverse.map some ++ before
                      current := some false
                      right := List.replicate blanks none } }

private theorem loop_runs (input : Tape) (low : List Bool) (before : List (Option Bool)) (zeros blanks : Nat)
    (hBlanks : 0 < blanks) :
    RunsFor program (state input low before zeros blanks)
      (trimFinish input low before (zeros+blanks)) (4*zeros+3) := by
  induction zeros generalizing blanks with
  | zero =>
    let start := state input low before 0 blanks
    let selected := { start with pc := 5 }
    let moved := { selected with pc := 6, outputTape := selected.outputTape.moveRight }
    have r₁ : Step program start selected := by
      simp [Step, successors, next, program, start, selected, state,
        Instruction.next, Configuration.tape]
    have r₂ : Step program selected moved := by
      simp [Step, successors, next, program, start, selected, moved, state,
        Instruction.next, Configuration.updateTape, Configuration.advance]
    have r₃ : Step program moved (trimFinish input low before (0+blanks)) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : blanks ≠ 0)
      simp [Step, successors, next, program, start, selected, moved, state, trimFinish,
        Tape.moveRight, List.replicate_succ, List.reverse_append, Instruction.next]
    exact (((RunsFor.zero _).succ r₁).succ r₂).succ r₃
  | succ zeros ih =>
    let start := state input low before (zeros+1) blanks
    let selected := { start with pc := 2 }
    let erased := { selected with pc := 3, outputTape := selected.outputTape.write none }
    let moved := { erased with pc := 4, outputTape := erased.outputTape.moveLeft }
    have r₁ : Step program start selected := by
      simp [Step, successors, next, program, start, selected, state,
        Instruction.next, Configuration.tape]
    have r₂ : Step program selected erased := by
      simp [Step, successors, next, program, start, selected, erased, state,
        Instruction.next, Configuration.updateTape, Configuration.advance]
    have r₃ : Step program erased moved := by
      simp [Step, successors, next, program, start, selected, erased, moved, state,
        Instruction.next, Configuration.updateTape, Configuration.advance]
    have r₄ : Step program moved (state input low before zeros (blanks+1)) := by
      cases zeros <;>
        simp [Step, successors, next, program, start, selected, erased, moved, state,
          Instruction.next, Tape.write, Tape.moveLeft, List.replicate_succ,
          List.reverse_append, List.replicate_succ']
    have run := ((((RunsFor.zero _).succ r₁).succ r₂).succ r₃).succ r₄
    have result := run.trans (ih (blanks+1) (by omega))
    have hFinish : trimFinish input low before (zeros+(blanks+1)) =
        trimFinish input low before ((zeros+1)+blanks) := by congr 1 <;> omega
    rw [hFinish] at result
    change RunsFor program (state input low before (zeros+1) blanks) _ _ at result
    convert result using 1 <;> omega

/-- A fixed-width positive binary field is shortened by erasing high zeros,
while the retained bits and the other physical tape are unchanged. -/
theorem runs_padded_before (input : Tape) (low : List Bool) (before : List (Option Bool)) (zeros : Nat) :
    let start : Configuration :=
      { inputTape := input
        outputTape := { left := ((low++[true]) ++ List.replicate zeros false).reverse.map some ++ before } }
    let target : Configuration :=
      { pc := 6
        halted := true
        inputTape := input
        outputTape := { left := (low++[true]).reverse.map some ++ before
                        right := List.replicate zeros none } }
    RunsFor program start target (4*zeros+4) := by
  dsimp only
  let start : Configuration :=
    { inputTape := input
      outputTape := { left := ((low++[true]) ++ List.replicate zeros false).reverse.map some ++ before } }
  have first : Step program start (state input low before zeros 1) := by
    cases zeros <;>
      simp [Step, successors, next, program, start, state, Instruction.next,
        Configuration.updateTape, Configuration.advance, Tape.moveLeft,
        List.reverse_append, List.map_append, List.replicate_succ']
  have result := ((RunsFor.zero _).succ first).trans (loop_runs input low before zeros 1 (by omega))
  simp only [trimFinish, Nat.add_sub_cancel] at result
  change RunsFor program start _ _ at result
  convert result using 1 <;> omega

/-- Convert a positive fixed-width modulus to the canonical binary input
required by the exact rejection sampler. The other tape is retained verbatim. -/
theorem runs_number_before (input : Tape) (before : List (Option Bool)) (width q : Nat) (hPositive : q ≠ 0)
    (hFit : q < 2^width) :
    RunsFor program
      ({ inputTape := input
         outputTape := { left := (Binary.encode width q).reverse.map some ++ before } } : Configuration)
      ({ pc := 6
         halted := true
         inputTape := input
         outputTape := { left := q.bits.reverse.map some ++ before
                         right := List.replicate (width-q.bits.length) none } } : Configuration)
      (4*(width-q.bits.length)+4) := by
  have hLength : q.bits.length ≤ width := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hFit
  obtain ⟨low, hCanonical⟩ := Binary.nat_bits_canonical q hPositive
  have hEncoding : q.bits ++ List.replicate (width-q.bits.length) false = Binary.encode width q := by
    simpa only [Binary.value_nat_bits] using
      FixedWidthOutputPadding.output_eq_encode width q.bits hLength
  have run := runs_padded_before input low before (width-q.bits.length)
  simpa only [← hCanonical, hEncoding] using run

/-- The initial empty-prefix interface remains a specialization of the
same contextual native trace. -/
theorem runs_padded (input : Tape) (low : List Bool) (zeros : Nat) :
    let start : Configuration :=
      { inputTape := input
        outputTape := { left := ((low++[true]) ++ List.replicate zeros false).reverse.map some } }
    let target : Configuration :=
      { pc := 6
        halted := true
        inputTape := input
        outputTape := { left := (low++[true]).reverse.map some
                        right := List.replicate zeros none } }
    RunsFor program start target (4*zeros+4) := by
  simpa only [List.append_nil] using runs_padded_before input low [] zeros

theorem runs_number (input : Tape) (width q : Nat) (hPositive : q ≠ 0)
    (hFit : q < 2^width) :
    RunsFor program
      ({ inputTape := input
         outputTape := { left := (Binary.encode width q).reverse.map some } } : Configuration)
      ({ pc := 6
         halted := true
         inputTape := input
         outputTape := { left := q.bits.reverse.map some
                         right := List.replicate (width-q.bits.length) none } } : Configuration)
      (4*(width-q.bits.length)+4) := by
  simpa only [List.append_nil] using runs_number_before input [] width q hPositive hFit

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  simp [program]

end Machine.BinaryHighZeroTrim
