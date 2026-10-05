import Foundation.Crypto.Semantics.Machine.ShiftInputBlockLeft
import Foundation.Crypto.Semantics.Machine.SavedBitstringRewind

namespace Machine.JoinReturnedResult

/-- Join the physically retained caller request and a returned arithmetic
result. The separator is removed by actual bit reads, writes and erasure;
then the input head is rewound across the joined request. -/
def program : Program := (rewindBitstring.followedBy ShiftInputBlockLeft.program).followedBy rewindBitstring

theorem runs (request result : List Bool) (blanks : Nat) (output : Tape) :
    ∃ target used, used ≤ 10*result.length+2*request.length+14 ∧
      RunsFor program
        ({inputTape := {left := result.reverse.map some ++ none::request.reverse.map some, right := List.replicate blanks none}, outputTape := output} : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits (request++result)) ∧
      target.outputTape.Equivalent output := by
  have one := rewindBitstring_runs_saved result (request.reverse.map some) none
    (List.replicate blanks none) output
  obtain ⟨u, hu, shift⟩ := ShiftInputBlockLeft.runs (request.reverse.map some) none result output
  have shiftEntry :
      ({inputTape := {Tape.ofBits result with left := none::request.reverse.map some}, outputTape := output} : Configuration).Equivalent
        (({pc := 3, inputTape := ({left := request.reverse.map some, right := result.map some ++ none::List.replicate blanks none} : Tape).moveRight, outputTape := output, halted := true} : Configuration).resumeAt 0) :=
    ⟨rfl, rfl, (rewindBitstring_saved_input_equivalent result (request.reverse.map some) blanks).symm,
      Tape.Equivalent.refl output⟩
  obtain ⟨shifted, a, ha, first, halt, input, out⟩ :=
    one.followedBy_equivalent shift shiftEntry (Nat.zero_le _) rfl rfl rfl
  have last := rewindBitstring_runs (request++result) output
  have lastEntry : (rewindBitstringStart (request++result) output).Equivalent
      (shifted.resumeAt 0) := by
    refine ⟨rfl, rfl, ?_, out⟩
    apply Tape.Equivalent.trans _ input
    have padding := (Tape.blank_padding_equivalent ((request++result).reverse.map some) 1).symm
    simpa [rewindBitstringStart, List.reverse_append, List.map_append] using padding
  obtain ⟨target, used, bound, run, halted, ti, targetOutput⟩ :=
    first.followedBy_equivalent last lastEntry (Nat.zero_le _) rfl halt rfl
  refine ⟨target, used, ?_, run, halted,
    ti.symm.trans (rewindBitstringFinish_input_equivalent (request++result) output), ?_⟩
  · simp only [List.length_append] at bound
    omega
  · simpa only [rewindBitstringFinish_output] using targetOutput.symm

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _
    (Program.followedBy_no_randomBit _ _ rewindBitstring_no_randomBit ShiftInputBlockLeft.no_randomBit)
    rewindBitstring_no_randomBit tape

end Machine.JoinReturnedResult
