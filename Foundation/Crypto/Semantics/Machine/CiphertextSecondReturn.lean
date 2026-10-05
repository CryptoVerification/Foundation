import Foundation.Crypto.Semantics.Machine.FixedWidthScalarReturn

namespace Machine.CiphertextSecondReturn
open FixedWidthScalarReturn

/-- Skip the retained shared power using the first ciphertext payload as
an actual counter, then append the framed product from the same input. -/
def program : Program := (OutputFrameCounter.program.followedBy AdvanceInputByOutput.program).followedBy
  FixedWidthScalarReturn.fromEnd

theorem runs (before field : List (Option Bool)) (first second : List Bool)
    (hField : field.length = first.length) (hWidth : second.length = first.length)
    (hFirst : first ≠ []) (hSecond : second ≠ []) :
    ∃ target used, used ≤ 100*first.length+150 ∧
      RunsFor program
        ({inputTape := atCells before (field++second.map some++[none]),outputTape := {left := (frame first).reverse.map some}} : Configuration)
        target used ∧ target.halted = true ∧ target.outputBits = frame first ++ frame second := by
  let input := atCells before (field++second.map some++[none])
  let header := (encodeSecurityParameter first.length).reverse.map some
  obtain ⟨counter,a,ha,countRun,countHalt,countInput,countOutput⟩ := OutputFrameCounter.runs input first
  have advance := AdvanceInputByOutput.runs_option_cells before header (second.map some++[none]) field first hField
  have advanceEntry : ({inputTape := input,outputTape := {Tape.ofBits first with left := header}} : Configuration).Equivalent
      (counter.resumeAt 0) := ⟨rfl,rfl,countInput.symm,countOutput.symm⟩
  obtain ⟨advanced,b,hb,advanceRun,advanceHalt,advanceInput,advanceOutput⟩ :=
    countRun.followedBy_equivalent advance (by simpa only [input,atCells,List.append_assoc] using advanceEntry) (Nat.zero_le _) rfl countHalt rfl
  have beforeNonempty : field.reverse++before ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    have positive : 0 < first.length := List.length_pos_iff.mpr hFirst
    simp only [List.length_append,List.length_reverse,List.length_nil,hField] at lengths
    omega
  cases beforeEq : field.reverse++before with
  | nil => exact False.elim (beforeNonempty beforeEq)
  | cons previous saved =>
    obtain ⟨returned,c,hc,returnRun,returnHalt,bits⟩ :=
      FixedWidthScalarReturn.runs_from_end previous saved none [] second first hWidth hSecond
    have returnEntry : ({inputTape := atCells (previous::saved) (second.map some++[none]), outputTape := {left := (frame first).reverse.map some}} : Configuration).Equivalent
        (advanced.resumeAt 0) := by
      refine ⟨rfl,rfl,?_,?_⟩
      · simpa [atCells,beforeEq,Configuration.resumeAt] using advanceInput
      · have outputEq : first.reverse.map some++header = (frame first).reverse.map some := by
          simp [header,frame,encodeSecurityParameter,List.reverse_append,List.map_append,List.map_replicate]
        simpa only [outputEq,Configuration.resumeAt] using advanceOutput
    obtain ⟨target,used,bound,run,halt,_,out⟩ :=
      advanceRun.followedBy_equivalent returnRun returnEntry (Nat.zero_le _) rfl advanceHalt returnHalt
    refine ⟨target,used,?_,run,halt,?_⟩
    · change used ≤ 100*first.length+150
      rw [hWidth] at hc
      change b ≤ a+(4*first.length+2)+1 at hb
      omega
    · exact out.bits.symm.trans bits

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _
    (Program.followedBy_no_randomBit _ _ OutputFrameCounter.no_randomBit AdvanceInputByOutput.no_randomBit)
    (Program.followedBy_no_randomBit _ _ OutputFrameCounter.no_randomBit FixedWidthScalarReturn.no_randomBit) tape

end Machine.CiphertextSecondReturn
