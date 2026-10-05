import Foundation.Crypto.Semantics.Machine.OneFieldColumnSkip
import Foundation.Crypto.Semantics.Machine.OutputColumnRewind
import Foundation.Crypto.Semantics.Machine.NativeSequence

namespace Machine.FixedWidthFieldSkip

/-- Skip one actual input field using the populated output columns as a
physical width counter, then rewind those same columns for their next use. -/
def program : Program := OneFieldColumnSkip.program.followedBy OutputColumnRewind.toFirst

private theorem emptyLeft (bits : List Bool) :
    ({Tape.ofBits bits with left := []} : Tape) = Tape.ofBits bits := by
  cases bits <;> rfl

theorem runs (columns : List BinaryModularAddition.Column) (skipped tail : List Bool)
    (hLength : skipped.length = columns.length) (before : List (Option Bool)) :
    ∃ target used, used ≤ 6*columns.length+2*(BinaryModularAddition.interleave columns).length+7 ∧
      RunsFor program
        ({inputTape := {Tape.ofBits (skipped++tail) with left := before},
          outputTape := Tape.ofBits (BinaryModularAddition.interleave columns)} : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape.Equivalent {Tape.ofBits tail with left := skipped.reverse.map some ++ before} ∧
      target.outputTape.Equivalent (Tape.ofBits (BinaryModularAddition.interleave columns)) := by
  obtain ⟨u,hu,first⟩ := OneFieldColumnSkip.runs_columns columns skipped tail hLength before []
  rw [emptyLeft,List.append_nil] at first
  let input : Tape := {Tape.ofBits tail with left := skipped.reverse.map some ++ before}
  obtain ⟨v,hv,last,lastOutput⟩ :=
    OutputColumnRewind.toFirst_runs (BinaryModularAddition.interleave columns) input
  have join : (rewindBitstringStart (BinaryModularAddition.interleave columns) input).swapTapes.Equivalent
      (({pc := 6,inputTape := input,outputTape := {left := (BinaryModularAddition.interleave columns).reverse.map some},halted := true} : Configuration).resumeAt 0) :=
    ⟨rfl,rfl,Tape.Equivalent.refl _,Tape.Equivalent.refl _⟩
  obtain ⟨target,used,bound,run,halt,inp,out⟩ :=
    first.followedBy_equivalent last join (Nat.zero_le _) rfl rfl rfl
  exact ⟨target,used,by omega,run,halt,by simpa [input,rewindBitstringFinish,Configuration.swapTapes] using inp.symm,
    out.symm.trans lastOutput⟩

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _ OneFieldColumnSkip.no_randomBit
    OutputColumnRewind.toFirst_no_randomBit tape

end Machine.FixedWidthFieldSkip
