import Foundation.Machine.DelimitedSkip

namespace Machine

open Foundation.Probability

/-- Sample the IND-CPA challenge bit on the output tape and position the
input head at the selected canonical message field. The bit is kept behind
a physical blank before the fresh output region. A true bit skips exactly
the first delimited field; a false bit leaves that field at the input head.
The tag, both message fields and the state remain stored on the input tape. -/
def selectMessage : Program :=
  [.randomBit .output, .moveRight .input, .branch .output 3 3 6,
    .moveRight .output, .moveRight .output, .jump 16,
    .moveRight .output, .moveRight .output] ++
    skipDelimited.asSubroutine 8 16 ++ [.halt]

def selectMessageStart (beforeInput beforeOutput : List (Option Bool))
    (first second : List Bool) (stateTail : List (Option Bool)) : Configuration :=
  { inputTape := {
      left := beforeInput
      current := some false
      right := (FiniteBitEncoding.delimit first).map some ++
        (FiniteBitEncoding.delimit second).map some ++ stateTail },
    outputTape := { left := beforeOutput } }

private def selectionAfterBit (beforeInput beforeOutput : List (Option Bool))
    (first second : List Bool) (stateTail : List (Option Bool)) (bit : Bool) : Configuration :=
  { selectMessageStart beforeInput beforeOutput first second stateTail with
    pc := 1, outputTape := { left := beforeOutput, current := some bit } }

private def selectionReady (beforeInput beforeOutput : List (Option Bool))
    (first second : List Bool) (stateTail : List (Option Bool)) (bit : Bool) : Configuration :=
  { skipDelimitedStart (some false :: beforeInput) first
      ((FiniteBitEncoding.delimit second).map some ++ stateTail)
      { left := none :: some bit :: beforeOutput } with pc := if bit then 8 else 5 }

def selectMessageFinish (beforeInput beforeOutput : List (Option Bool))
    (first second : List Bool) (stateTail : List (Option Bool)) (bit : Bool) : Configuration :=
  if bit then
    { skipDelimitedFinish (some false :: beforeInput) first
        ((FiniteBitEncoding.delimit second).map some ++ stateTail)
        { left := none :: some true :: beforeOutput } with pc := 16 }
  else
    { selectionReady beforeInput beforeOutput first second stateTail false with pc := 16, halted := true }

private theorem selection_first_step (beforeInput beforeOutput : List (Option Bool))
    (first second : List Bool) (stateTail : List (Option Bool)) :
    stepPMF selectMessage (selectMessageStart beforeInput beforeOutput first second stateTail) =
      sampleBit.map (selectionAfterBit beforeInput beforeOutput first second stateTail) := by
  simp [stepPMF, next, selectMessage, selectMessageStart,
    Instruction.next, Configuration.updateTape, Configuration.advance, Tape.write]
  congr 1
  funext bit
  cases bit <;> simp [selectionAfterBit, selectMessageStart, List.append_assoc]

/-- The deterministic four transitions after sampling consume only the
response tag and reserve the blank separating the stored bit from output. -/
private theorem selection_header_eval (beforeInput beforeOutput : List (Option Bool))
    (first second : List Bool) (stateTail : List (Option Bool)) (bit : Bool) :
    evalConfigWithin selectMessage
      (selectionAfterBit beforeInput beforeOutput first second stateTail bit) 4 =
      PMF.pure (selectionReady beforeInput beforeOutput first second stateTail bit) := by
  simp only [selectionReady]
  rw [skipDelimitedStart_layout]
  cases bit <;> cases first <;>
    simp [evalConfigWithin, stepPMF, next, selectMessage, selectionAfterBit, selectMessageStart,
      FiniteBitEncoding.delimit,
      Instruction.next, Configuration.tape, Configuration.updateTape, Configuration.advance,
      Tape.moveRight, PMF.pure_bind]

private theorem selection_halted_eval (c : Configuration) (halted : c.halted = true) (steps : Nat) :
    evalConfigWithin selectMessage c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, halted]

private theorem selection_afterBit_eval (beforeInput beforeOutput : List (Option Bool))
    (first second : List Bool) (stateTail : List (Option Bool)) (bit : Bool) :
    evalConfigWithin selectMessage
      (selectionAfterBit beforeInput beforeOutput first second stateTail bit)
      (4 * first.length + 8) =
      PMF.pure (selectMessageFinish beforeInput beforeOutput first second stateTail bit) := by
  rw [show 4 * first.length + 8 = 4 + (4 * first.length + 4) by omega,
    evalConfigWithin_add, selection_header_eval, PMF.pure_bind]
  cases bit with
  | false =>
      have hShort : evalConfigWithin selectMessage
          (selectionReady beforeInput beforeOutput first second stateTail false) 2 =
          PMF.pure (selectMessageFinish beforeInput beforeOutput first second stateTail false) := by
        simp [evalConfigWithin, stepPMF, next, selectMessage, selectionReady,
          selectMessageFinish, skipDelimitedStart, skipDelimited, Program.asSubroutine,
          Instruction.asSubroutine, Instruction.next, PMF.pure_bind]
      rw [show 4 * first.length + 4 = 2 + (4 * first.length + 2) by omega,
        evalConfigWithin_add, hShort, PMF.pure_bind]
      exact selection_halted_eval _ rfl _
  | true =>
      let pre : Program := [.randomBit .output, .moveRight .input, .branch .output 3 3 6,
        .moveRight .output, .moveRight .output, .jump 16,
        .moveRight .output, .moveRight .output]
      have hSkip := (skipDelimited_runs (some false :: beforeInput) first
          ((FiniteBitEncoding.delimit second).map some ++ stateTail)
          { left := none :: some true :: beforeOutput }).evalConfigWithin_withSubroutine_halted_of_closed
        pre skipDelimited [.halt] 16 (by change 0 < 7; decide) rfl rfl
        skipDelimited_control_closed skipDelimited_no_randomBit
      change evalConfigWithin selectMessage
        (selectionReady beforeInput beforeOutput first second stateTail true)
        (4 * first.length + 3) =
        PMF.pure ((selectMessageFinish beforeInput beforeOutput first second stateTail true).resumeAt 16) at hSkip
      rw [show 4 * first.length + 4 = (4 * first.length + 3) + 1 by omega,
        evalConfigWithin_add, hSkip, PMF.pure_bind]
      simp [evalConfigWithin, stepPMF, next, selectMessage, skipDelimited,
        Program.asSubroutine, Instruction.asSubroutine, selectMessageFinish,
        skipDelimitedFinish, Configuration.resumeAt, Instruction.next, PMF.pure_bind]

/-- Full native configuration law. The same fixed transition bound applies
to both fair-bit branches, including the longer scan on the true branch.
Any shorter branch is padded only after its actual halt. -/
theorem selectMessage_eval (beforeInput beforeOutput : List (Option Bool))
    (first second : List Bool) (stateTail : List (Option Bool)) :
    evalConfigWithin selectMessage (selectMessageStart beforeInput beforeOutput first second stateTail)
      (4 * first.length + 9) =
      sampleBit.map (selectMessageFinish beforeInput beforeOutput first second stateTail) := by
  rw [show 4 * first.length + 9 = (4 * first.length + 8) + 1 by omega,
    evalConfigWithin_succ_head, selection_first_step, PMF.bind_map]
  simp only [Function.comp_def]
  simp_rw [selection_afterBit_eval]
  exact PMF.bind_pure_comp _ _

theorem selectMessage_haltsFrom (beforeInput beforeOutput : List (Option Bool))
    (first second : List Bool) (stateTail : List (Option Bool))
    (finish : Configuration)
    (run : PaddedRunsFor selectMessage (selectMessageStart beforeInput beforeOutput first second stateTail)
      finish (4 * first.length + 9)) : finish.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [selectMessage_eval, PMF.mem_support_map_iff] at hMem
  obtain ⟨bit, _hBit, rfl⟩ := hMem
  cases bit <;> rfl

/-- The sampled challenge remains behind its real blank separator, at a
known head-relative position. It is not inserted as external randomness. -/
theorem selectMessageFinish_output (beforeInput beforeOutput : List (Option Bool))
    (first second : List Bool) (stateTail : List (Option Bool)) (bit : Bool) :
    (selectMessageFinish beforeInput beforeOutput first second stateTail bit).outputTape =
      { left := none :: some bit :: beforeOutput } := by
  cases bit <;> rfl

/-- In either branch the current input field is exactly the selected
message encoding. Earlier canonical response cells remain behind the head,
and the second message/state cells remain ahead when the first is selected. -/
theorem selectMessageFinish_input (beforeInput beforeOutput : List (Option Bool))
    (first second : List Bool) (stateTail : List (Option Bool)) (bit : Bool) :
    (selectMessageFinish beforeInput beforeOutput first second stateTail bit).inputTape =
      (skipDelimitedStart
        (if bit then (FiniteBitEncoding.delimit first).reverse.map some ++ some false :: beforeInput
          else some false :: beforeInput)
        (if bit then second else first)
        (if bit then stateTail else (FiniteBitEncoding.delimit second).map some ++ stateTail)
        { left := none :: some bit :: beforeOutput }).inputTape := by
  cases bit with
  | false => rfl
  | true =>
      simp only [selectMessageFinish, ↓reduceIte]
      cases second with
      | nil =>
          rw [show (FiniteBitEncoding.delimit []).map some ++ stateTail = some false :: stateTail from rfl,
            skipDelimitedFinish_layout, skipDelimitedStart_layout]
          simp [FiniteBitEncoding.delimit, Tape.moveRight]
      | cons bit rest =>
          rw [show (FiniteBitEncoding.delimit (bit :: rest)).map some ++ stateTail =
              some true :: some bit :: ((FiniteBitEncoding.delimit rest).map some ++ stateTail) from rfl,
            skipDelimitedFinish_layout, skipDelimitedStart_layout]
          simp [FiniteBitEncoding.delimit, Tape.moveRight]

theorem selectMessage_control_closed (c d : Configuration)
    (hPc : c.pc < selectMessage.length) (step : Step selectMessage c d)
    (_hRunning : d.halted = false) : d.pc < selectMessage.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 17 at hPc
  change d.pc < 17
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, selectMessage,
    skipDelimited, Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals rcases step with rfl | rfl <;>
    simp [Configuration.advance, Configuration.updateTape, hIndex]

private def selectionAfterBitAny (input output : Tape) (bit : Bool) : Configuration :=
  { pc := 1, inputTape := input, outputTape := output.write (some bit) }

private def selectionReadyAny (input output : Tape) (bit : Bool) : Configuration :=
  { pc := if bit then 8 else 5, inputTape := input.moveRight,
    outputTape := (output.write (some bit)).moveRight.moveRight }

private theorem selection_anyTape_first_step (input output : Tape) :
    stepPMF selectMessage ({ inputTape := input, outputTape := output } : Configuration) =
      sampleBit.map (selectionAfterBitAny input output) := by
  simp [stepPMF, next, selectMessage, Instruction.next, Configuration.updateTape,
    Configuration.advance]
  congr 1
  funext bit
  cases bit <;> simp [selectionAfterBitAny]

private theorem selection_anyTape_header_eval (input output : Tape) (bit : Bool) :
    evalConfigWithin selectMessage (selectionAfterBitAny input output bit) 4 =
      PMF.pure (selectionReadyAny input output bit) := by
  cases bit <;> simp [evalConfigWithin, stepPMF, next, selectMessage,
    selectionAfterBitAny, selectionReadyAny, Instruction.next, Configuration.tape,
    Configuration.updateTape, Configuration.advance, Tape.write, PMF.pure_bind]

private theorem selection_anyTape_afterBit_eval (input output : Tape) (bit : Bool) :
    ∃ (finish : Configuration) (used : Nat), used ≤ 4 * input.cells + 20 ∧
      evalConfigWithin selectMessage (selectionAfterBitAny input output bit) used = PMF.pure finish ∧
      finish.halted = true ∧ finish.outputTape = (output.write (some bit)).moveRight.moveRight := by
  cases bit with
  | false =>
      let finish : Configuration := { selectionReadyAny input output false with pc := 16, halted := true }
      have hTail : evalConfigWithin selectMessage (selectionReadyAny input output false) 2 = PMF.pure finish := by
        simp [evalConfigWithin, stepPMF, next, selectMessage, skipDelimited,
          Program.asSubroutine, Instruction.asSubroutine, selectionReadyAny,
          finish, Instruction.next, PMF.pure_bind]
      refine ⟨finish, 6, by omega, ?_, rfl, rfl⟩
      rw [show 6 = 4 + 2 from rfl, evalConfigWithin_add, selection_anyTape_header_eval, PMF.pure_bind]
      exact hTail
  | true =>
      let pre : Program := [.randomBit .output, .moveRight .input, .branch .output 3 3 6,
        .moveRight .output, .moveRight .output, .jump 16, .moveRight .output, .moveRight .output]
      let nextOutput := (output.write (some true)).moveRight.moveRight
      obtain ⟨parsed, parseTime, hTime, hRun, hHalt, hOutput⟩ :=
        skipDelimited_terminates_from_anyTape input.moveRight nextOutput
      have hSkip := hRun.evalConfigWithin_withSubroutine_halted_of_closed
        pre skipDelimited [.halt] 16 (by change 0 < 7; decide) rfl hHalt
        skipDelimited_control_closed skipDelimited_no_randomBit
      change evalConfigWithin selectMessage (selectionReadyAny input output true) parseTime =
        PMF.pure (parsed.resumeAt 16) at hSkip
      let finish : Configuration := { parsed with pc := 16, halted := true }
      have hTail : evalConfigWithin selectMessage (selectionReadyAny input output true) (parseTime + 1) =
          PMF.pure finish := by
        rw [evalConfigWithin_add, hSkip, PMF.pure_bind]
        simp [evalConfigWithin, stepPMF, next, selectMessage, skipDelimited,
          Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt,
          finish, Instruction.next, PMF.pure_bind]
      refine ⟨finish, 4 + (parseTime + 1), ?_, ?_, rfl, hOutput⟩
      · have hMove := Tape.cells_moveRight_le input
        omega
      · rw [evalConfigWithin_add, selection_anyTape_header_eval, PMF.pure_bind]
        exact hTail

/-- Complete native selection law on arbitrary finite tapes. The random
bit is sampled once; escaped-field skipping halts even on a dangling marker
or internal blank. No canonical response shape is assumed by this law. -/
theorem selectMessage_eval_anyTape (input output : Tape) :
    ∃ finish : Bool → Configuration,
      evalConfigWithin selectMessage ({ inputTape := input, outputTape := output } : Configuration)
        (4 * input.cells + 21) = sampleBit.map finish ∧
      ∀ bit, (finish bit).halted = true ∧
        (finish bit).outputTape = (output.write (some bit)).moveRight.moveRight := by
  obtain ⟨first, firstTime, hFirstTime, hFirstEval, hFirstHalt, hFirstOutput⟩ :=
    selection_anyTape_afterBit_eval input output false
  obtain ⟨second, secondTime, hSecondTime, hSecondEval, hSecondHalt, hSecondOutput⟩ :=
    selection_anyTape_afterBit_eval input output true
  let finish := fun bit : Bool => if bit then second else first
  have hAt (bit : Bool) : evalConfigWithin selectMessage (selectionAfterBitAny input output bit)
      (4 * input.cells + 20) = PMF.pure (finish bit) := by
    have hExtend (used : Nat) (target : Configuration)
        (hTime : used ≤ 4 * input.cells + 20)
        (hEval : evalConfigWithin selectMessage (selectionAfterBitAny input output bit) used = PMF.pure target)
        (hHalt : target.halted = true) :
        evalConfigWithin selectMessage (selectionAfterBitAny input output bit)
          (4 * input.cells + 20) = PMF.pure target := by
      have hAll (c : Configuration)
          (run : PaddedRunsFor selectMessage (selectionAfterBitAny input output bit) c used) : c.halted = true := by
        have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
        rw [hEval] at hMem
        have hEq : c = target := by simpa using hMem
        simpa only [hEq] using hHalt
      exact (evalConfigWithin_eq_of_le _ _ _ _ hTime hAll).trans hEval
    cases bit with
    | false => exact hExtend firstTime first hFirstTime hFirstEval hFirstHalt
    | true => exact hExtend secondTime second hSecondTime hSecondEval hSecondHalt
  refine ⟨finish, ?_, ?_⟩
  · rw [show 4 * input.cells + 21 = (4 * input.cells + 20) + 1 by omega,
      evalConfigWithin_succ_head, selection_anyTape_first_step, PMF.bind_map]
    simp only [Function.comp_def]
    simp_rw [hAt]
    exact PMF.bind_pure_comp _ _
  · intro bit
    cases bit with
    | false => exact ⟨hFirstHalt, hFirstOutput⟩
    | true => exact ⟨hSecondHalt, hSecondOutput⟩

theorem selectMessage_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor selectMessage
      ({ inputTape := input, outputTape := output } : Configuration) finish (4 * input.cells + 21)) :
    finish.halted = true := by
  obtain ⟨result, hEval, hHalt⟩ := selectMessage_eval_anyTape input output
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [hEval, PMF.mem_support_map_iff] at hMem
  obtain ⟨bit, _hBit, rfl⟩ := hMem
  exact (hHalt bit).1

end Machine
