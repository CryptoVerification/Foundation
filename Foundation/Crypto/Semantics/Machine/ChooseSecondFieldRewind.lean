import Foundation.Crypto.Semantics.Machine.DelimitedTapeComparison
import Foundation.Crypto.Semantics.Machine.DelimitedTripleWidthCheck
import Foundation.Crypto.Semantics.Machine.TapeEquivalence
import Foundation.Crypto.Semantics.Machine.BitstringRewind

namespace Machine.ChooseSecondFieldRewind

/-- Rewind from the suffix following the second choose field. The output
tape contains three equally wide instance fields and its status cell is
under the head. Each three output cells moved left correspond to one
marker/payload pair moved left on the input. The status cell is cleared;
the stored instance and response bits remain on the tapes. -/
def program : Program :=
  [.erase .output,
   .moveLeft .input,
   .moveLeft .output,
   .branch .output 10 4 4,
   .moveLeft .input,
   .moveLeft .input,
   .moveLeft .output,
   .moveLeft .output,
   .moveLeft .output,
   .jump 3,
   .moveRight .output,
   .halt]

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

def entry (input output : Tape) : Configuration :=
  { inputTape := input, outputTape := output }

def loop (input output : Tape) : Configuration :=
  { pc := 3, inputTape := input, outputTape := output }

def finish (input output : Tape) : Configuration :=
  { pc := 11, inputTape := input,
    outputTape := output.moveRight, halted := true }

theorem enter (input output : Tape) :
    evalConfigWithin program (entry input output) 3 =
      PMF.pure (loop input.moveLeft (output.write none).moveLeft) := by
  simp [evalConfigWithin, stepPMF, next, program, entry, loop,
    Instruction.next, Configuration.advance, Configuration.updateTape,
    PMF.pure_bind]

theorem triple (input output : Tape) (bit : Bool)
    (hBit : output.current = some bit) :
    evalConfigWithin program (loop input output) 7 =
      PMF.pure (loop input.moveLeft.moveLeft
        output.moveLeft.moveLeft.moveLeft) := by
  cases bit <;>
    simp [evalConfigWithin, stepPMF, next, program, loop, hBit,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, PMF.pure_bind]

theorem stop (input output : Tape) (hBlank : output.current = none) :
    evalConfigWithin program (loop input output) 3 =
      PMF.pure (finish input output) := by
  simp [evalConfigWithin, stepPMF, next, program, loop, finish, hBlank,
    Instruction.next, Configuration.advance, Configuration.tape,
    Configuration.updateTape, PMF.pure_bind]

private theorem eval_halted (c : Configuration) (steps : Nat)
    (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, stepPMF, next, h, ih]

/-- Even an arbitrary finite retained output tape cannot cause an
unbounded rewind. This budget counts the actual remaining output cells. -/
theorem loop_any (input output : Tape) :
    ∃ final, final.halted = true ∧
      evalConfigWithin program (loop input output)
        (7 * (output.left.length + 1) + 3) = PMF.pure final := by
  cases hCurrent : output.current with
  | none =>
      refine ⟨finish input output, rfl, ?_⟩
      have hBudget : 7 * (output.left.length + 1) + 3 =
          3 + (7 * (output.left.length + 1)) := by omega
      rw [hBudget, evalConfigWithin_add, stop input output hCurrent,
        PMF.pure_bind]
      exact eval_halted _ _ rfl
  | some bit =>
      let nextInput := input.moveLeft.moveLeft
      let nextOutput := output.moveLeft.moveLeft.moveLeft
      have hTriple := triple input output bit hCurrent
      cases hLeft : output.left with
      | nil =>
          have hBlank : nextOutput.current = none := by
            simp [nextOutput, Tape.moveLeft, hLeft]
          refine ⟨finish nextInput nextOutput, rfl, ?_⟩
          have hBudget : 7 * (output.left.length + 1) + 3 = 7 + 3 := by
            simp [hLeft]
          have hShort : evalConfigWithin program (loop input output) (7 + 3) =
              PMF.pure (finish nextInput nextOutput) := by
            rw [evalConfigWithin_add, hTriple, PMF.pure_bind]
            exact stop nextInput nextOutput hBlank
          simpa [hLeft] using hShort
      | cons cell rest =>
          obtain ⟨final, hHalt, hEval⟩ := loop_any nextInput nextOutput
          refine ⟨final, hHalt, ?_⟩
          have hLength : nextOutput.left.length < output.left.length := by
            cases rest with
            | nil => simp [nextOutput, Tape.moveLeft, hLeft]
            | cons another rest =>
                cases rest <;> simp [nextOutput, Tape.moveLeft, hLeft] <;> omega
          have hUsed : 7 + (7 * (nextOutput.left.length + 1) + 3) ≤
              7 * (output.left.length + 1) + 3 := by omega
          have hBudget : 7 * (output.left.length + 1) + 3 =
              (7 + (7 * (nextOutput.left.length + 1) + 3)) +
                (7 * (output.left.length + 1) + 3 -
                  (7 + (7 * (nextOutput.left.length + 1) + 3))) := by omega
          have hFirst : evalConfigWithin program (loop input output)
              (7 + (7 * (nextOutput.left.length + 1) + 3)) =
                PMF.pure final := by
            rw [evalConfigWithin_add, hTriple, PMF.pure_bind]
            exact hEval
          have hLong : evalConfigWithin program (loop input output)
              (7 * (output.left.length + 1) + 3) = PMF.pure final := by
            rw [hBudget, evalConfigWithin_add, hFirst, PMF.pure_bind]
            exact eval_halted final _ hHalt
          simpa [hLeft] using hLong
termination_by output.left.length
decreasing_by
  cases output with
  | mk left current right =>
      cases rest with
      | nil => simp_all [Tape.moveLeft]
      | cons head tail =>
          cases tail <;> simp_all [Tape.moveLeft] <;> omega

/-- The entire fixed code stops on all finite retained tapes. -/
theorem runs_any (input output : Tape) :
    ∃ final used, used ≤ 7 * (output.left.length + 2) + 6 ∧
      RunsFor program (entry input output) final used ∧
      final.halted = true := by
  let nextInput := input.moveLeft
  let nextOutput := (output.write none).moveLeft
  obtain ⟨final, hHalt, hLoop⟩ := loop_any nextInput nextOutput
  have hLength : nextOutput.left.length ≤ output.left.length := by
    cases output with
    | mk left current right =>
        cases left with
        | nil => simp [nextOutput, Tape.moveLeft, Tape.write]
        | cons head tail =>
            cases tail <;> simp [nextOutput, Tape.moveLeft, Tape.write]
  have hUsed : 3 + (7 * (nextOutput.left.length + 1) + 3) ≤
      7 * (output.left.length + 2) + 6 := by omega
  have hBudget : 7 * (output.left.length + 2) + 6 =
      (3 + (7 * (nextOutput.left.length + 1) + 3)) +
        (7 * (output.left.length + 2) + 6 -
          (3 + (7 * (nextOutput.left.length + 1) + 3))) := by omega
  have hFirst : evalConfigWithin program (entry input output)
      (3 + (7 * (nextOutput.left.length + 1) + 3)) = PMF.pure final := by
    rw [evalConfigWithin_add, enter, PMF.pure_bind]
    exact hLoop
  have hEval : evalConfigWithin program (entry input output)
      (7 * (output.left.length + 2) + 6) = PMF.pure final := by
    rw [hBudget, evalConfigWithin_add, hFirst, PMF.pure_bind]
    exact eval_halted final _ hHalt
  have hSupport : final ∈
      (evalConfigWithin program (entry input output)
        (7 * (output.left.length + 2) + 6)).support := by
    rw [hEval]
    simp
  obtain ⟨used, hUsed', run⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  exact ⟨final, used, hUsed', run, hHalt⟩

private def codeAt : List Bool → List (Option Bool) → Tape
  | [], right => { right := right }
  | bit :: rest, right =>
      { left := rest.map some ++ [none], current := some bit, right := right }

private def moveLeftN (tape : Tape) : Nat → Tape
  | 0 => tape
  | count + 1 => moveLeftN tape.moveLeft count

private theorem moveLeftN_succ (tape : Tape) (count : Nat) :
    moveLeftN tape (count + 1) = moveLeftN tape.moveLeft count := rfl

private theorem moveLeftN_two (tape : Tape) (count : Nat) :
    moveLeftN tape (count + 2) =
      moveLeftN tape.moveLeft.moveLeft count := by
  rw [show count + 2 = (count + 1) + 1 by omega,
    moveLeftN_succ, moveLeftN_succ]

private theorem moveLeftN_prefix (prefixCells : List (Option Bool))
    (marker : Option Bool) (before right : List (Option Bool))
    (current : Option Bool) :
    moveLeftN
      { left := prefixCells ++ marker :: before, current := current, right := right }
      (prefixCells.length + 1) =
      { left := before, current := marker,
        right := prefixCells.reverse ++ current :: right } := by
  induction prefixCells generalizing current right with
  | nil => simp [moveLeftN, Tape.moveLeft]
  | cons cell rest ih =>
      simpa [moveLeftN, Tape.moveLeft, List.reverse_cons,
        List.append_assoc] using ih (current :: right) cell

private theorem getD_append_none (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> simp
  | cons cell rest ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [List.cons_append, List.getD_cons_succ] using ih i

private theorem rewind_consumed_equivalent
    (first : Bool) (rest tail : List Bool)
    (before : List (Option Bool)) :
    (moveLeftN
      ({ Tape.ofBits tail with
        left := (first :: rest).reverse.map some ++ before } : Tape)
      (first :: rest).length).Equivalent
        { Tape.ofBits ((first :: rest) ++ tail) with left := before } := by
  have hRewind := moveLeftN_prefix (rest.reverse.map some)
    (some first) before (Tape.ofBits tail).right (Tape.ofBits tail).current
  have hTape : moveLeftN
      ({ Tape.ofBits tail with
        left := (first :: rest).reverse.map some ++ before } : Tape)
      (first :: rest).length =
      { left := before, current := some first,
        right := rest.map some ++ (Tape.ofBits tail).current ::
          (Tape.ofBits tail).right } := by
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using hRewind
  rw [hTape]
  cases tail with
  | nil =>
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro i
      simpa [Tape.ofBits] using getD_append_none (rest.map some) i
  | cons bit tail =>
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro i
      simp [Tape.ofBits, List.map_append]

private theorem codeAt_three (a b c : Bool) (rest : List Bool)
    (right : List (Option Bool)) :
    (codeAt (a :: b :: c :: rest) right).moveLeft.moveLeft.moveLeft =
      codeAt rest (some c :: some b :: some a :: right) := by
  cases rest <;> simp [codeAt, Tape.moveLeft]

/-- Exactly one backward loop is taken for every three stored instance
cells. The input head moves twice per loop, so it can track a marked
response field without inspecting its bit values. -/
private theorem eval_code (width : Nat) (reversedCode : List Bool)
    (hLength : reversedCode.length = 3 * width)
    (input : Tape) (right : List (Option Bool)) :
    evalConfigWithin program (loop input (codeAt reversedCode right))
      (7 * width + 3) =
      PMF.pure (finish (moveLeftN input (2 * width))
        (codeAt [] (reversedCode.reverse.map some ++ right))) := by
  induction width generalizing reversedCode input right with
  | zero =>
      cases reversedCode with
      | nil => simpa [moveLeftN, codeAt] using stop input (codeAt [] right) rfl
      | cons bit rest => simp at hLength
  | succ width ih =>
      cases reversedCode with
      | nil => simp at hLength
      | cons a rest =>
          cases rest with
          | nil => simp at hLength; omega
          | cons b rest =>
              cases rest with
              | nil => simp at hLength; omega
              | cons c remaining =>
                  have hRest : remaining.length = 3 * width := by
                    simp only [List.length_cons] at hLength
                    omega
                  have hBudget : 7 * (width + 1) + 3 =
                      7 + (7 * width + 3) := by omega
                  rw [hBudget, evalConfigWithin_add]
                  rw [triple input (codeAt (a :: b :: c :: remaining) right) a
                    (by rfl), PMF.pure_bind, codeAt_three]
                  have hIH := ih remaining hRest input.moveLeft.moveLeft
                    (some c :: some b :: some a :: right)
                  simpa [moveLeftN, Nat.mul_succ, List.reverse_cons,
                    List.map_append, List.append_assoc] using hIH

/-- Starting at the exact successful second-width layout, the fixed
rewind walks the response head back by two cells per element bit and the
instance head back by three cells per bit. The final output head is at the
first stored instance bit. -/
theorem eval_matching_layout (beforeInput : List (Option Bool))
    (counter field tail : List Bool)
    (hCounter : counter.length = 3 * field.length) :
    let widthFinish := DelimitedTripleWidthCheck.finish
      beforeInput [none] counter field tail
    evalConfigWithin program
      (entry widthFinish.inputTape widthFinish.outputTape)
      (3 + (7 * field.length + 3)) =
      PMF.pure (finish
        (moveLeftN widthFinish.inputTape.moveLeft (2 * field.length))
        (codeAt [] (counter.map some ++ [none]))) := by
  dsimp only
  let widthFinish := DelimitedTripleWidthCheck.finish
    beforeInput [none] counter field tail
  have hOutput : (widthFinish.outputTape.write none).moveLeft =
      codeAt counter.reverse [none] := by
    cases h : counter.reverse with
    | nil =>
        have hc : counter = [] := by
          simpa using congrArg List.reverse h |>.symm
        simp [widthFinish, DelimitedTripleWidthCheck.finish, hc,
          codeAt, Tape.moveLeft, Tape.write]
    | cons bit rest =>
        have hc : counter.reverse.map some = some bit :: rest.map some := by
          simp [h]
        simp [widthFinish, DelimitedTripleWidthCheck.finish,
          Tape.moveLeft, Tape.write, codeAt, h]
  rw [evalConfigWithin_add, enter, PMF.pure_bind, hOutput]
  have hReverse : counter.reverse.length = 3 * field.length := by
    simpa using hCounter
  simpa only [List.reverse_reverse] using
    eval_code field.length counter.reverse hReverse
      widthFinish.inputTape.moveLeft [none]

/-- At the resulting heads, the entire second response field and the
entire instance code are still present. Tape equivalence ignores only
outer blank padding introduced by head moves. -/
theorem eval_matching_tapes (beforeInput : List (Option Bool))
    (counter field tail : List Bool)
    (hCounter : counter.length = 3 * field.length) :
    let widthFinish := DelimitedTripleWidthCheck.finish
      beforeInput [none] counter field tail
    ∃ target,
      evalConfigWithin program
        (entry widthFinish.inputTape widthFinish.outputTape)
        (3 + (7 * field.length + 3)) = PMF.pure target ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits (FiniteBitEncoding.delimit field ++ tail) with
          left := beforeInput } ∧
      target.outputTape.Equivalent (Tape.ofBits counter) := by
  dsimp only
  let widthFinish := DelimitedTripleWidthCheck.finish
    beforeInput [none] counter field tail
  let target := finish
    (moveLeftN widthFinish.inputTape.moveLeft (2 * field.length))
    (codeAt [] (counter.map some ++ [none]))
  refine ⟨target, eval_matching_layout beforeInput counter field tail hCounter,
    rfl, ?_, ?_⟩
  · have hInput :
        (moveLeftN widthFinish.inputTape.moveLeft
          (2 * field.length)).Equivalent
          { Tape.ofBits (FiniteBitEncoding.delimit field ++ tail) with
            left := beforeInput } := by
      cases field with
      | nil =>
          simpa [widthFinish, DelimitedTripleWidthCheck.finish,
            FiniteBitEncoding.delimit, moveLeftN_succ] using
            rewind_consumed_equivalent false [] tail beforeInput
      | cons bit rest =>
          have hRaw := rewind_consumed_equivalent true
            (bit :: FiniteBitEncoding.delimit rest) tail beforeInput
          have hCount : 2 * (rest.length + 1) =
              2 * rest.length + 2 := by omega
          simp only [List.length_cons]
          rw [hCount, moveLeftN_two]
          simpa [widthFinish, DelimitedTripleWidthCheck.finish,
            FiniteBitEncoding.delimit, FiniteBitEncoding.delimit_length,
            moveLeftN_succ] using hRaw
    exact hInput
  · simpa [target, finish, codeAt, rewindBitstringFinish] using
      rewindBitstringFinish_input_equivalent counter ({} : Tape)

theorem runs_matching_tapes (beforeInput : List (Option Bool))
    (counter field tail : List Bool)
    (hCounter : counter.length = 3 * field.length) :
    let widthFinish := DelimitedTripleWidthCheck.finish
      beforeInput [none] counter field tail
    ∃ target used,
      used ≤ 3 + (7 * field.length + 3) ∧
      RunsFor program (entry widthFinish.inputTape widthFinish.outputTape)
        target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits (FiniteBitEncoding.delimit field ++ tail) with
          left := beforeInput } ∧
      target.outputTape.Equivalent (Tape.ofBits counter) := by
  dsimp only
  obtain ⟨target, hEval, hHalt, hInput, hOutput⟩ :=
    eval_matching_tapes beforeInput counter field tail hCounter
  have hSupport : target ∈
      (evalConfigWithin program
        (entry (DelimitedTripleWidthCheck.finish beforeInput [none]
          counter field tail).inputTape
          (DelimitedTripleWidthCheck.finish beforeInput [none]
            counter field tail).outputTape)
        (3 + (7 * field.length + 3))).support := by
    rw [hEval]
    simp
  obtain ⟨used, hUsed, run⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  exact ⟨target, used, hUsed, run, hHalt, hInput, hOutput⟩

end Machine.ChooseSecondFieldRewind
