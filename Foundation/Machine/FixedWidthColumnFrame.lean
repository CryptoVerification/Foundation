import Foundation.Machine.FixedWidthScalarReturn
import Foundation.Machine.OneFieldColumnSkip
import Foundation.Machine.MoveInputLeftByColumns
import Foundation.Machine.BitstringErasure
import Foundation.Machine.ConsumedInputErasure

namespace Machine.FixedWidthColumnFrame
open FixedWidthScalarReturn

/-- Mark the two boundaries of a single retained field using the actual
width columns, return to that field, erase the scratch counter, and frame
its actual bits. No unread suffix is copied into the result. -/
def program : Program :=
  (((((markStart.followedBy OneFieldColumnSkip.program).followedBy markEnd).followedBy
    OutputColumnRewind.toFirst).followedBy MoveInputLeftByColumns.program).followedBy
    eraseOutputBlock).followedBy writeFrame

theorem runs (previous : Option Bool) (saved : List (Option Bool))
    (nextCell : Option Bool) (tail : List (Option Bool)) (bits : List Bool)
    (columns : List BinaryModularAddition.Column)
    (hLength : bits.length = columns.length) (hBits : bits ≠ []) :
    ∃ target used, used ≤ 40*bits.length+6*(BinaryModularAddition.interleave columns).length+70 ∧
      RunsFor program
        ({inputTape := atCells (previous::saved) (bits.map some ++ nextCell::tail), outputTape := Tape.ofBits (BinaryModularAddition.interleave columns)} : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape.Equivalent {left := bits.reverse.map some ++ none::saved,right := tail} ∧
      target.outputTape.Equivalent {left := (frame bits).reverse.map some} := by
  cases bits with
  | nil => exact False.elim (hBits rfl)
  | cons bit rest =>
    let field := bit::rest
    let matrix := BinaryModularAddition.interleave columns
    let markedInput := atCells (none::saved) (field.map some ++ nextCell::tail)
    have startRun := markStart_runs previous saved bit (rest.map some ++ nextCell::tail) (Tape.ofBits matrix)
    obtain ⟨a,ha,forward⟩ := OneFieldColumnSkip.runs_columns columns field [] hLength (none::saved) []
    -- The field reader is used only for its input-head movement; the input
    -- suffix is retained by the identical loop, including a blank guard.
    have skipEval := OneFieldColumnSkip.eval_columns columns field [] hLength (none::saved) []
    -- Instantiate the same loop on cells rather than truncate the suffix.
    have moving := MoveInputLeftByColumns.eval_columns columns
      (atCells (field.reverse.map some ++ none::saved) (nextCell::tail)) []
    have forwardCells : ∃ used, used ≤ 6*columns.length+2 ∧
        RunsFor OneFieldColumnSkip.program
          ({inputTape := markedInput,outputTape := Tape.ofBits matrix} : Configuration)
          ({pc := 6,inputTape := atCells (field.reverse.map some ++ none::saved) (nextCell::tail), outputTape := {left := matrix.reverse.map some},halted := true} : Configuration) used := by
      -- A one-column iteration does not inspect the input cell. It therefore
      -- preserves every option-valued suffix, including the guard.
      clear a ha forward skipEval moving
      have evalAny (cs : List BinaryModularAddition.Column) (input : Tape) (before : List (Option Bool)) :
          evalConfigWithin OneFieldColumnSkip.program
            ({inputTape := input,outputTape := {Tape.ofBits (BinaryModularAddition.interleave cs) with left := before}} : Configuration)
            (6*cs.length+2) = PMF.pure
              {pc := 6,inputTape := (Tape.moveRight^[cs.length]) input, outputTape := {left := (BinaryModularAddition.interleave cs).reverse.map some ++ before},halted := true} := by
        induction cs generalizing input before with
        | nil =>
          cases input <;> simp [evalConfigWithin,stepPMF,next,OneFieldColumnSkip.program,Instruction.next,
            Configuration.tape,Configuration.advance,PMF.pure_bind,BinaryModularAddition.interleave,Tape.ofBits]
        | cons col cs ih =>
          rcases col with ⟨⟨x,y⟩,p⟩
          have step : evalConfigWithin OneFieldColumnSkip.program
              ({inputTape := input,outputTape := {Tape.ofBits (BinaryModularAddition.interleave (((x,y),p)::cs)) with left := before}} : Configuration) 6 =
              PMF.pure {inputTape := input.moveRight,outputTape := {Tape.ofBits (BinaryModularAddition.interleave cs) with left := [some p,some y,some x]++before}} := by
            cases cs <;> cases x <;>
              simp [evalConfigWithin,stepPMF,next,OneFieldColumnSkip.program,Instruction.next,
                Configuration.tape,Configuration.advance,Configuration.updateTape,PMF.pure_bind,
                BinaryModularAddition.interleave,Tape.ofBits,Tape.moveRight]
          have time : 6*(((x,y),p)::cs).length+2 = 6+(6*cs.length+2) := by simp; omega
          rw [time,evalConfigWithin_add,step,PMF.pure_bind,ih]
          simp [BinaryModularAddition.interleave,List.reverse_cons,List.map_append,List.append_assoc,
            Function.iterate_succ_apply]
      have ev := evalAny columns markedInput []
      have empty (xs : List Bool) : ({Tape.ofBits xs with left := []} : Tape) = Tape.ofBits xs := by cases xs <;> rfl
      rw [empty,List.append_nil,←hLength,right_bits,hLength] at ev
      have mem : ({pc := 6,inputTape := atCells (field.reverse.map some ++ none::saved) (nextCell::tail),outputTape := {left := matrix.reverse.map some},halted := true} : Configuration) ∈
          (evalConfigWithin OneFieldColumnSkip.program ({inputTape := markedInput,outputTape := Tape.ofBits matrix} : Configuration) (6*columns.length+2)).support := by
        dsimp only [field,matrix]
        rw [ev]; simp
      exact ((mem_support_evalConfigWithin_iff _ _ _ _).mp mem).toRunsFor_le
    obtain ⟨f,hf,fr⟩ := forwardCells
    have forwardEntry : ({inputTape := markedInput,outputTape := Tape.ofBits matrix} : Configuration).Equivalent
        (({pc := 3,inputTape := {left := none::saved,current := some bit,right := rest.map some ++ nextCell::tail},outputTape := Tape.ofBits matrix,halted := true} : Configuration).resumeAt 0) :=
      ⟨rfl,rfl,Tape.Equivalent.refl _,Tape.Equivalent.refl _⟩
    obtain ⟨one,u,hu,r1,h1,i1,o1⟩ := startRun.followedBy_equivalent fr forwardEntry (Nat.zero_le _) rfl rfl rfl
    have marking := markEnd_runs (field.reverse.map some ++ none::saved) nextCell tail {left := matrix.reverse.map some}
    have markingEntry : ({inputTape := {left := field.reverse.map some ++ none::saved,current := nextCell,right := tail},outputTape := {left := matrix.reverse.map some}} : Configuration).Equivalent (one.resumeAt 0) :=
      ⟨rfl,rfl,i1,o1⟩
    obtain ⟨two,v,hv,r2,h2,i2,o2⟩ := r1.followedBy_equivalent marking markingEntry (Nat.zero_le _) rfl h1 rfl
    let endInput : Tape := {left := field.reverse.map some ++ none::saved,right := tail}
    obtain ⟨w,hw,re,reOut⟩ := OutputColumnRewind.toFirst_runs matrix endInput
    have reEntry : (rewindBitstringStart matrix endInput).swapTapes.Equivalent (two.resumeAt 0) := ⟨rfl,rfl,i2,o2⟩
    obtain ⟨three,t,ht,r3,h3,i3,o3⟩ := r2.followedBy_equivalent re reEntry (Nat.zero_le _) rfl h2 rfl
    obtain ⟨l,hl,back⟩ := MoveInputLeftByColumns.runs columns endInput
    have backEntry : ({inputTape := endInput,outputTape := Tape.ofBits matrix} : Configuration).Equivalent (three.resumeAt 0) :=
      ⟨rfl,rfl,i3,reOut.symm.trans o3⟩
    obtain ⟨four,a4,ha4,r4,h4,i4,o4⟩ := r3.followedBy_equivalent back backEntry (Nat.zero_le _) rfl h3 rfl
    have returned : (Tape.moveLeft^[columns.length]) endInput = atCells (none::saved) (field.map some ++ none::tail) := by
      rw [←hLength]
      exact left_bits (none::saved) (none::tail) field (by simp)
    rw [returned] at i4
    let fieldInput := atCells (none::saved) (field.map some ++ none::tail)
    have erase := eraseOutputBlock_runs fieldInput [] matrix []
    have eraseEntry : (eraseOutputBlockStart fieldInput [] matrix []).Equivalent (four.resumeAt 0) :=
      ⟨rfl,rfl,i4,(ConsumedInputErasure.outer_blank matrix).symm.trans o4⟩
    obtain ⟨five,a5,ha5,r5,h5,i5,o5⟩ := r4.followedBy_equivalent erase eraseEntry (Nat.zero_le _) rfl h4 rfl
    have framing := writeFrameContext_runs saved [] tail field
    have frameEntry : (writeFrameContextStart saved [] tail field).Equivalent (five.resumeAt 0) := by
      refine ⟨rfl,rfl,?_,?_⟩
      · change fieldInput.Equivalent five.inputTape
        change fieldInput.Equivalent five.inputTape at i5
        exact i5
      · apply Tape.Equivalent.trans _ o5
        apply Tape.Equivalent.symm
        change ({right := List.replicate (matrix.reverse.length+1) none ++ []} : Tape).Equivalent ({} : Tape)
        simpa only [List.append_nil] using Tape.blank_padding_equivalent [] (matrix.reverse.length+1)
    obtain ⟨target,used,bound,run,halt,inp,out⟩ := r5.followedBy_equivalent framing frameEntry (Nat.zero_le _) rfl h5 rfl
    refine ⟨target,used,?_,?_,halt,?_,?_⟩
    · have framedBound := writeFrameSteps_le field
      change used ≤ 40*field.length+6*matrix.length+70
      simp only [field,List.length_cons] at hu hv ht hl ha4 ha5 bound hf framedBound hLength ⊢
      omega
    · simpa [program,atCells,field,markedInput,Tape.moveRight,matrix] using run
    · simpa [writeFrameContextFinish,writeFrameContextPaddedFinish,field] using inp.symm
    · simpa [writeFrameContextFinish,writeFrameContextPaddedFinish,field,List.append_nil] using out.symm

private theorem markStartNoRandom (tape : TapeId) : Instruction.randomBit tape ∉ FixedWidthScalarReturn.markStart := by
  cases tape <;> decide

private theorem markEndNoRandom (tape : TapeId) : Instruction.randomBit tape ∉ FixedWidthScalarReturn.markEnd := by
  cases tape <;> decide

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  unfold program
  exact (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ (Program.followedBy_no_randomBit _ _ markStartNoRandom OneFieldColumnSkip.no_randomBit) markEndNoRandom) OutputColumnRewind.toFirst_no_randomBit) MoveInputLeftByColumns.no_randomBit) eraseOutputBlock_no_randomBit) writeFrame_no_randomBit) tape

end Machine.FixedWidthColumnFrame
