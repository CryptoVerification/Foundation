import Foundation.Machine.OutputColumnRewind
import Foundation.Machine.UnaryInput
import Foundation.Machine.NativeSequence

namespace Machine.OutputFrameCounter

/-- Reuse a framed output's actual payload as a width counter. Its frame
and every input cell are retained by the native rewind and unary scan. -/
def program : Program := OutputColumnRewind.toFirst.followedBy skipUnary.swapTapes

theorem runs (input : Tape) (bits : List Bool) :
    ∃ target used, used ≤ 7*bits.length+10 ∧
      RunsFor program
        ({inputTape := input, outputTape := {left := (frame bits).reverse.map some}} : Configuration)
        target used ∧ target.halted = true ∧ target.inputTape.Equivalent input ∧
      target.outputTape.Equivalent
        {Tape.ofBits bits with left := (encodeSecurityParameter bits.length).reverse.map some} := by
  obtain ⟨a, ha, rewind, output⟩ := OutputColumnRewind.toFirst_runs (frame bits) input
  have scan := (skipUnary_runs [] bits.length bits input).swapTapes
  have frameEq : encodeSecurityParameter bits.length ++ bits = frame bits := rfl
  have startEq : (skipUnaryStart [] bits.length bits input).swapTapes.outputTape = Tape.ofBits (frame bits) := by
    cases h : frame bits <;> simp [skipUnaryStart, Configuration.swapTapes, frameEq, h, Tape.ofBits]
  have layout : (skipUnaryStart [] bits.length bits input).swapTapes.Equivalent
      ((rewindBitstringFinish (frame bits) input).swapTapes.resumeAt 0) := by
    refine ⟨rfl, rfl, Tape.Equivalent.refl _, ?_⟩
    rw [startEq]
    exact output.symm
  obtain ⟨target, used, bound, run, halt, ti, tout⟩ := rewind.followedBy_equivalent scan layout
    (Nat.zero_le _) rfl rfl rfl
  refine ⟨target, used, ?_, run, halt, ti.symm, ?_⟩
  · have len : (frame bits).length = 2*bits.length+1 := by simp [frame]; omega
    omega
  · have same : (skipUnaryFinish [] bits.length bits input).swapTapes.outputTape =
        ({Tape.ofBits bits with left := (encodeSecurityParameter bits.length).reverse.map some} : Tape) := by
      simp [skipUnaryFinish, Configuration.swapTapes, encodeSecurityParameter, List.map_replicate]
    rw [same] at tout
    exact tout.symm

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _ OutputColumnRewind.toFirst_no_randomBit
    (Program.swapTapes_no_randomBit _ skipUnary_no_randomBit) tape

end Machine.OutputFrameCounter
