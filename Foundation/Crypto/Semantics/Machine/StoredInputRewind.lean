import Foundation.Crypto.Semantics.Machine.BitstringRewind
import Foundation.Crypto.Semantics.Machine.SubroutineProbability
import Foundation.Crypto.Semantics.Machine.GuardedTrace

namespace Machine

/-- Restore the earliest of three stored input blocks. Rewind the consumed
part of the canonical response, cross a real blank, rewind the raw reply,
cross its blank, and rewind the DDH input. The other tape, which contains
the selected message and challenge, is untouched by all eighteen instructions. -/
def restoreStoredInput : Program :=
  rewindBitstring.asSubroutine 0 5 ++ [.moveLeft .input] ++
    rewindBitstring.asSubroutine 6 11 ++ [.moveLeft .input] ++
    rewindBitstring.asSubroutine 12 17 ++ [.halt]

def restoreStoredInputStart (before : List (Option Bool))
    (original reply consumed : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) : Configuration :=
  { inputTape := {
      left := consumed.reverse.map some ++ none :: reply.reverse.map some ++
        none :: original.reverse.map some ++ none :: before
      current := current
      right := right },
    outputTape := output }

def restoreStoredInputFinish (before : List (Option Bool))
    (original reply consumed : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) : Configuration :=
  { pc := 17,
    inputTape := ({
      left := before
      right := original.map some ++ none :: reply.map some ++ none :: consumed.map some ++ current :: right } : Tape).moveRight,
    outputTape := output, halted := true }

def restoreStoredInputSteps (original reply consumed : List Bool) : Nat :=
  (2 * consumed.length + 4) + 1 + (2 * reply.length + 4) + 1 + (2 * original.length + 4) + 1

/-- Exact native transitions, including all three scans, both separator
crossings, and the final halt. No stored bit is changed or copied for free. -/
theorem restoreStoredInput_runs (before : List (Option Bool))
    (original reply consumed : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    RunsFor restoreStoredInput (restoreStoredInputStart before original reply consumed current right output)
      (restoreStoredInputFinish before original reply consumed current right output)
      (restoreStoredInputSteps original reply consumed) := by
  let savedOriginal := original.reverse.map some ++ none :: before
  let savedReply := reply.reverse.map some ++ none :: savedOriginal
  let consumedRight := consumed.map some ++ current :: right
  let replyRight := reply.map some ++ none :: consumedRight
  let a := rewindBitstring.asSubroutine 0 5
  let b := rewindBitstring.asSubroutine 6 11
  let k := rewindBitstring.asSubroutine 12 17
  let rewound : Configuration :=
    { pc := 3, inputTape := ({ left := savedReply, right := consumedRight } : Tape).moveRight,
      outputTape := output, halted := true }
  let back : Configuration :=
    { pc := 6, inputTape := { left := savedReply, right := consumedRight }, outputTape := output }
  have hFirst := (rewindScratch_runs_from savedReply consumed current right output).withSubroutine_halted_of_closed
    [] rewindBitstring ([.moveLeft .input] ++ b ++ [.moveLeft .input] ++ k ++ [.halt]) 5
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  have hFirst' : RunsFor restoreStoredInput
      (restoreStoredInputStart before original reply consumed current right output)
      (rewound.resumeAt 5) (2 * consumed.length + 4) := by
    simpa [restoreStoredInput, Program.withSubroutine, restoreStoredInputStart, savedReply,
      savedOriginal, consumedRight, rewound, b, k, Configuration.rebasePc,
      List.append_assoc] using hFirst
  have hBack : Step restoreStoredInput (rewound.resumeAt 5) back := by
    cases consumed <;> simp [Step, successors, next, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, rewound, back, consumedRight,
      Configuration.resumeAt, Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveRight, Tape.moveLeft]
  let replyRewound : Configuration :=
    { pc := 3, inputTape := ({ left := savedOriginal, right := replyRight } : Tape).moveRight,
      outputTape := output, halted := true }
  let originalBack : Configuration :=
    { pc := 12, inputTape := { left := savedOriginal, right := replyRight }, outputTape := output }
  have hSecond := (rewindScratch_runs_from savedOriginal reply none consumedRight output).withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input]) rewindBitstring ([.moveLeft .input] ++ k ++ [.halt]) 11
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  change RunsFor restoreStoredInput back (replyRewound.resumeAt 11) (2 * reply.length + 4) at hSecond
  have hOriginalBack : Step restoreStoredInput (replyRewound.resumeAt 11) originalBack := by
    cases reply <;> simp [Step, successors, next, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, replyRewound, originalBack, replyRight,
      Configuration.resumeAt, Instruction.next, Configuration.updateTape, Configuration.advance,
      Tape.moveRight, Tape.moveLeft]
  have hThird := (rewindScratch_runs_from before original none replyRight output).withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input] ++ b ++ [.moveLeft .input]) rewindBitstring [.halt] 17
    (by change 0 < 4; decide) rfl rfl rewindBitstring_control_closed
  have hThird' : RunsFor restoreStoredInput originalBack
    ((restoreStoredInputFinish before original reply consumed current right output).resumeAt 17)
    (2 * original.length + 4) := by
    simpa [restoreStoredInput, Program.withSubroutine, a, b, originalBack, savedOriginal,
      replyRight, consumedRight, restoreStoredInputFinish, Configuration.rebasePc,
      Configuration.resumeAt, Program.asSubroutine_length,
      show rewindBitstring.length = 4 from rfl, List.append_assoc] using hThird
  have hHalt : Step restoreStoredInput
      ((restoreStoredInputFinish before original reply consumed current right output).resumeAt 17)
      (restoreStoredInputFinish before original reply consumed current right output) := by
    simp [Step, successors, next, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, restoreStoredInputFinish,
      Configuration.resumeAt, Instruction.next]
  exact RunsFor.succ (((RunsFor.succ hFirst' hBack).trans hSecond).succ hOriginalBack |>.trans hThird') hHalt

theorem restoreStoredInput_no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ restoreStoredInput := by
  simp [restoreStoredInput, rewindBitstring, Program.asSubroutine, Instruction.asSubroutine]

theorem restoreStoredInput_eval (before : List (Option Bool))
    (original reply consumed : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    evalConfigWithin restoreStoredInput
      (restoreStoredInputStart before original reply consumed current right output)
      (restoreStoredInputSteps original reply consumed) =
      PMF.pure (restoreStoredInputFinish before original reply consumed current right output) :=
  (restoreStoredInput_runs before original reply consumed current right output).evalConfigWithin_eq_pure_of_no_randomBit
    restoreStoredInput_no_randomBit

theorem restoreStoredInputFinish_output (before : List (Option Bool))
    (original reply consumed : List Bool) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) :
    (restoreStoredInputFinish before original reply consumed current right output).outputTape = output := rfl

theorem restoreStoredInput_control_closed (c d : Configuration)
    (hPc : c.pc < restoreStoredInput.length) (step : Step restoreStoredInput c d)
    (_hRunning : d.halted = false) : d.pc < restoreStoredInput.length := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  change c.pc < 18 at hPc
  change d.pc < 18
  interval_cases hIndex : c.pc
  all_goals simp [Step, successors, next, hActive, hIndex, restoreStoredInput,
    rewindBitstring, Program.asSubroutine, Instruction.asSubroutine, subroutineAddress,
    Instruction.next, Configuration.tape] at step
  all_goals try (split at step)
  all_goals subst d
  all_goals simp [Configuration.advance, Configuration.updateTape, hIndex]

private theorem restored_block_moveLeft (bits : List Bool) (before : List (Option Bool))
    (current : Option Bool) (right : List (Option Bool)) :
    ({ ({ right := bits.map some ++ current :: right } : Tape).moveRight
      with left := none :: before } : Tape).moveLeft =
      { left := before, right := bits.map some ++ current :: right } := by
  cases bits <;> simp [Tape.moveRight, Tape.moveLeft]

/-- All three native rewinds stop on arbitrary finite tapes. A malformed
separator can change the restored location, but cannot turn any scan into
an infinite traversal. The two separator crossings and caller halt are
actual transitions, and the other physical tape is preserved. -/
private theorem restoreStoredInput_terminates_layout_core (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat) (first second third : List Bool)
      (before : List (Option Bool)), used ≤ 100 * (input.cells + output.cells) + 100 ∧
      RunsFor restoreStoredInput
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape = { ({
        right := first.map some ++ none :: second.map some ++
          none :: third.map some ++ input.current :: input.right } : Tape).moveRight
        with left := none :: before } := by
  obtain ⟨first, thirdBits, before₁, length₁, run₁, halt₁, input₁, output₁⟩ :=
    rewindBitstring_terminates_with_layout input output
  obtain ⟨second, secondBits, before₂, length₂, run₂, halt₂, input₂, output₂⟩ :=
    rewindBitstring_terminates_with_layout first.inputTape.moveLeft first.outputTape
  obtain ⟨third, firstBits, before₃, length₃, run₃, halt₃, input₃, output₃⟩ :=
    rewindBitstring_terminates_with_layout second.inputTape.moveLeft second.outputTape
  let t₁ := 2 * thirdBits.length + 4
  let t₂ := 2 * secondBits.length + 4
  let t₃ := 2 * firstBits.length + 4
  have h₁ : t₁ ≤ 2 * input.left.length + 4 := by dsimp only [t₁]; omega
  have h₂ : t₂ ≤ 2 * first.inputTape.moveLeft.left.length + 4 := by dsimp only [t₂]; omega
  have h₃ : t₃ ≤ 2 * second.inputTape.moveLeft.left.length + 4 := by dsimp only [t₃]; omega
  let a := rewindBitstring.asSubroutine 0 5
  let b := rewindBitstring.asSubroutine 6 11
  let k := rewindBitstring.asSubroutine 12 17
  have firstRun := run₁.withSubroutine_halted_of_closed
    [] rewindBitstring ([.moveLeft .input] ++ b ++ [.moveLeft .input] ++ k ++ [.halt]) 5
    (by change 0 < 4; decide) rfl halt₁ rewindBitstring_control_closed
  change RunsFor restoreStoredInput
    ({ inputTape := input, outputTape := output } : Configuration) (first.resumeAt 5) t₁ at firstRun
  let secondStart : Configuration :=
    { pc := 6, inputTape := first.inputTape.moveLeft, outputTape := first.outputTape }
  have move₁ : Step restoreStoredInput (first.resumeAt 5) secondStart := by
    simp [Step, successors, next, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, secondStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have secondRun := run₂.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input]) rewindBitstring ([.moveLeft .input] ++ k ++ [.halt]) 11
    (by change 0 < 4; decide) rfl halt₂ rewindBitstring_control_closed
  change RunsFor restoreStoredInput secondStart (second.resumeAt 11) t₂ at secondRun
  let thirdStart : Configuration :=
    { pc := 12, inputTape := second.inputTape.moveLeft, outputTape := second.outputTape }
  have move₂ : Step restoreStoredInput (second.resumeAt 11) thirdStart := by
    simp [Step, successors, next, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, thirdStart,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have thirdRun := run₃.withSubroutine_halted_of_closed
    (a ++ [.moveLeft .input] ++ b ++ [.moveLeft .input]) rewindBitstring [.halt] 17
    (by change 0 < 4; decide) rfl halt₃ rewindBitstring_control_closed
  change RunsFor restoreStoredInput thirdStart (third.resumeAt 17) t₃ at thirdRun
  let finish : Configuration := { third with pc := 17, halted := true }
  have last : Step restoreStoredInput (third.resumeAt 17) finish := by
    simp [Step, successors, next, restoreStoredInput, rewindBitstring,
      Program.asSubroutine, Instruction.asSubroutine, Configuration.resumeAt, finish, Instruction.next]
  refine ⟨finish, t₁ + 1 + t₂ + 1 + t₃ + 1, firstBits, secondBits, thirdBits, before₃, ?_,
    RunsFor.succ (((RunsFor.succ firstRun move₁).trans secondRun).succ move₂ |>.trans thirdRun) last,
    rfl, output₃.trans (output₂.trans output₁), ?_⟩
  · have storage₁ := GuardedCompiler.sourceStorage_le_of_run run₁
    have storage₂ := GuardedCompiler.sourceStorage_le_of_run run₂
    have moved₁ := Tape.cells_moveLeft_le first.inputTape
    have moved₂ := Tape.cells_moveLeft_le second.inputTape
    have left₁ : input.left.length ≤ input.cells := by dsimp only [Tape.cells]; omega
    have left₂ : first.inputTape.moveLeft.left.length ≤ first.inputTape.moveLeft.cells := by
      dsimp only [Tape.cells]; omega
    have left₃ : second.inputTape.moveLeft.left.length ≤ second.inputTape.moveLeft.cells := by
      dsimp only [Tape.cells]; omega
    change first.inputTape.cells + first.outputTape.cells ≤ input.cells + output.cells + t₁ at storage₁
    change second.inputTape.cells + second.outputTape.cells ≤
      first.inputTape.moveLeft.cells + first.outputTape.cells + t₂ at storage₂
    omega
  · have back₁ : first.inputTape.moveLeft =
        { left := before₁, right := thirdBits.map some ++ input.current :: input.right } := by
      rw [input₁]
      exact restored_block_moveLeft thirdBits before₁ input.current input.right
    rw [back₁] at input₂
    have back₂ : second.inputTape.moveLeft =
        { left := before₂, right := secondBits.map some ++ none :: thirdBits.map some ++ input.current :: input.right } := by
      rw [input₂]
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        restored_block_moveLeft secondBits before₂ none (thirdBits.map some ++ input.current :: input.right)
    rw [back₂] at input₃
    change third.inputTape = _
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using input₃

theorem restoreStoredInput_terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 100 * (input.cells + output.cells) + 100 ∧
      RunsFor restoreStoredInput
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output := by
  obtain ⟨finish, used, _first, _second, _third, _before, hBound, run, hHalted, hOutput, _hInput⟩ :=
    restoreStoredInput_terminates_layout_core input output
  exact ⟨finish, used, hBound, run, hHalted, hOutput⟩

/-- Arbitrary left cells expose three finite bit blocks. Real or virtual
blank separators stop each native rewind. The previous current/right cells
remain after the exposed blocks, and a reserved separator stays on the left. -/
theorem restoreStoredInput_terminates_with_block_layout (input output : Tape) :
    ∃ (finish : Configuration) (used : Nat) (first second third : List Bool)
      (before : List (Option Bool)), used ≤ 100 * (input.cells + output.cells) + 100 ∧
      RunsFor restoreStoredInput
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape = { ({
        right := first.map some ++ none :: second.map some ++
          none :: third.map some ++ input.current :: input.right } : Tape).moveRight
        with left := none :: before } :=
  restoreStoredInput_terminates_layout_core input output

private theorem storedBlank_split (cells : List (Option Bool))
    (hBlank : 0 < cells.count none) :
    ∃ (bits : List Bool) (saved : List (Option Bool)),
      cells = bits.map some ++ none :: saved := by
  induction cells with
  | nil => simp at hBlank
  | cons cell rest ih =>
      cases cell with
      | none => exact ⟨[], rest, rfl⟩
      | some bit =>
          have hRest : 0 < rest.count none := by simpa using hBlank
          obtain ⟨bits, saved, h⟩ := ih hRest
          exact ⟨bit :: bits, saved, by simp [h]⟩

private theorem storedBlank_count_bitCells (bits : List Bool) :
    (bits.map some).count (none : Option Bool) = 0 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simpa using ih

private theorem storedBlank_three_blocks (cells : List (Option Bool))
    (hBlank : 3 ≤ cells.count none) :
    ∃ (first second consumed : List Bool) (saved : List (Option Bool)),
      cells = consumed.reverse.map some ++ none :: second.reverse.map some ++
        none :: first.reverse.map some ++ none :: saved := by
  obtain ⟨consumed, remaining, hConsumed⟩ := storedBlank_split cells (by omega)
  have hRemaining : 2 ≤ remaining.count none := by
    rw [hConsumed, List.count_append, List.count_cons_self,
      storedBlank_count_bitCells] at hBlank
    omega
  obtain ⟨second, tail, hSecond⟩ := storedBlank_split remaining (by omega)
  have hTail : 1 ≤ tail.count none := by
    rw [hSecond, List.count_append, List.count_cons_self,
      storedBlank_count_bitCells] at hRemaining
    omega
  obtain ⟨first, saved, hFirst⟩ := storedBlank_split tail (by omega)
  refine ⟨first.reverse, second.reverse, consumed.reverse, saved, ?_⟩
  simp only [List.reverse_reverse]
  rw [hConsumed, hSecond, hFirst]
  simp only [List.append_assoc, List.cons_append]

/-- Three retained real separators, together with one redundant outer
blank, expose four finite blocks behind the input head. Appending that
outer blank describes the same tape cells; it is not a machine write. -/
theorem storedInput_four_blocks_of_separators (cells : List (Option Bool))
    (hSeparators : 3 ≤ cells.count none) :
    ∃ (original reply canonical selected : List Bool) (before : List (Option Bool)),
      cells ++ [none] = selected.reverse.map some ++ none :: canonical.reverse.map some ++
        none :: reply.reverse.map some ++ none :: original.reverse.map some ++ none :: before := by
  have hBlank : 4 ≤ (cells ++ [none]).count none := by
    simp only [List.count_append, List.count_cons_self, List.count_nil]
    omega
  obtain ⟨reply, canonical, selected, remaining, hThree⟩ :=
    storedBlank_three_blocks (cells ++ [none]) (by omega)
  have hRemaining : 0 < remaining.count none := by
    rw [hThree] at hBlank
    simp only [List.count_append, List.count_cons_self, storedBlank_count_bitCells] at hBlank
    omega
  obtain ⟨original, before, hOriginal⟩ := storedBlank_split remaining hRemaining
  refine ⟨original.reverse, reply, canonical, selected, before, ?_⟩
  rw [hThree, hOriginal]
  simp only [List.reverse_reverse, List.append_assoc, List.cons_append]

/-- Three actual retained separators protect the caller prefix even when
the intervening cells contain malformed fields. The native restoration
exposes a suffix of the retained cells, rather than reading caller data
before their reserved separator. No protocol decoding premise is needed. -/
theorem restoreStoredInput_terminates_from_retained_prefix
    (retained before : List (Option Bool)) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape)
    (hSeparators : 2 ≤ retained.count none) :
    let input : Tape := { left := retained ++ none :: before, current := current, right := right }
    ∃ finish used count,
      used ≤ 100 * (input.cells + output.cells) + 100 ∧
      RunsFor restoreStoredInput
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape.current :: finish.inputTape.right =
        (retained.reverse ++ current :: right).drop count := by
  dsimp only
  have hBlank : 3 ≤ (retained ++ [none]).count none := by
    simp only [List.count_append, List.count_cons_self, List.count_nil]
    omega
  obtain ⟨first, second, consumed, saved, hSplit⟩ :=
    storedBlank_three_blocks (retained ++ [none]) hBlank
  let start := restoreStoredInputStart (saved ++ before) first second consumed current right output
  let finish := restoreStoredInputFinish (saved ++ before) first second consumed current right output
  have hInput : start.inputTape =
      ({ left := retained ++ none :: before, current := current, right := right } : Tape) := by
    dsimp only [start, restoreStoredInputStart]
    have hLeft := congrArg (fun cells : List (Option Bool) => cells ++ before) hSplit
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      congrArg (fun cells : List (Option Bool) =>
        ({ left := cells, current := current, right := right } : Tape)) hLeft.symm
  have hRun := restoreStoredInput_runs (saved ++ before) first second consumed current right output
  change RunsFor restoreStoredInput start finish (restoreStoredInputSteps first second consumed) at hRun
  have hStart : start =
      ({ inputTape := { left := retained ++ none :: before, current := current, right := right },
         outputTape := output } : Configuration) := by
    change ({ inputTape := start.inputTape, outputTape := output } : Configuration) = _
    rw [hInput]
  rw [hStart] at hRun
  refine ⟨finish, restoreStoredInputSteps first second consumed, saved.length, ?_, hRun, rfl, rfl, ?_⟩
  · have hLength := congrArg List.length hSplit
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map, List.length_reverse] at hLength
    dsimp only [restoreStoredInputSteps, Tape.cells]
    simp only [List.length_append, List.length_cons]
    omega
  · have hReverse := congrArg List.reverse hSplit
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.map_reverse,
      List.reverse_reverse, List.nil_append, List.append_assoc, List.cons_append] at hReverse
    have hDrop := congrArg
      (fun cells : List (Option Bool) => (cells ++ current :: right).drop (saved.length + 1)) hReverse
    have hDrop' : (retained.reverse ++ current :: right).drop saved.length =
        first.map some ++ none :: second.map some ++ none :: consumed.map some ++ current :: right := by
      have hEmpty : saved.reverse.drop (saved.length + 1) = [] := by
        apply List.drop_eq_nil_of_le
        simp
      simpa [List.append_assoc, List.drop_append, hEmpty] using hDrop
    rw [hDrop']
    dsimp only [finish, restoreStoredInputFinish]
    cases first <;> simp [Tape.moveRight]

private theorem retained_prefix_after_moves
    (retained before : List (Option Bool)) (current : Option Bool)
    (right : List (Option Bool)) (moves : Nat) :
    let input : Tape := { left := retained ++ none :: before, current := current, right := right }
    let moved := (Tape.moveRight^[moves]) input
    ∃ (after : List (Option Bool)) (padding : Nat),
      moved.left = after ++ none :: before ∧
      retained.count none ≤ after.count none ∧
      after.reverse ++ moved.current :: moved.right =
        retained.reverse ++ current :: right ++ List.replicate padding none := by
  induction moves with
  | zero => exact ⟨retained, 0, rfl, Nat.le_refl _, by simp⟩
  | succ moves ih =>
      dsimp only at ih ⊢
      obtain ⟨after, padding, hLeft, hCount, hContents⟩ := ih
      let previous := (Tape.moveRight^[moves])
        ({ left := retained ++ none :: before, current := current, right := right } : Tape)
      change previous.left = _ at hLeft
      change after.reverse ++ previous.current :: previous.right = _ at hContents
      rw [Function.iterate_succ_apply']
      change ∃ after padding, previous.moveRight.left = after ++ none :: before ∧
        retained.count none ≤ after.count none ∧
        after.reverse ++ previous.moveRight.current :: previous.moveRight.right = _
      have hNewCount : retained.count none ≤ (previous.current :: after).count none := by
        have hCountLe : after.count none ≤ (previous.current :: after).count none := by
          cases previous.current <;> simp
        exact hCount.trans hCountLe
      cases hRight : previous.right with
      | nil =>
          refine ⟨previous.current :: after, padding + 1, ?_, hNewCount, ?_⟩
          · simp [Tape.moveRight, hRight, hLeft]
          · simp only [Tape.moveRight, hRight, List.reverse_cons, List.append_assoc,
              List.cons_append, List.nil_append]
            have hContents' : after.reverse ++ [previous.current] =
                retained.reverse ++ current :: right ++ List.replicate padding none := by
              simpa only [hRight] using hContents
            calc
              after.reverse ++ [previous.current, none] =
                  (after.reverse ++ [previous.current]) ++ [none] := by simp
              _ = (retained.reverse ++ current :: right ++ List.replicate padding none) ++ [none] :=
                congrArg (fun cells : List (Option Bool) => cells ++ [none]) hContents'
              _ = retained.reverse ++ current :: (right ++ List.replicate (padding + 1) none) := by
                simp [List.replicate_succ', List.append_assoc]
      | cons cell rest =>
          refine ⟨previous.current :: after, padding, ?_, hNewCount, ?_⟩
          · simp [Tape.moveRight, hRight, hLeft]
          · simpa only [Tape.moveRight, hRight, List.reverse_cons, List.append_assoc,
              List.cons_append, List.nil_append] using hContents

/-- Right-reading native routines may pass malformed fields or even reach
unused blank cells. Subsequent three-block restoration still exposes only
a suffix of the originally retained cells followed by finite blank padding.
The reserved caller boundary and its two preceding separators are retained. -/
theorem restoreStoredInput_terminates_after_input_moves
    (retained before : List (Option Bool)) (current : Option Bool)
    (right : List (Option Bool)) (output : Tape) (moves : Nat)
    (hSeparators : 2 ≤ retained.count none) :
    let input := (Tape.moveRight^[moves])
      ({ left := retained ++ none :: before, current := current, right := right } : Tape)
    ∃ finish used count padding,
      used ≤ 100 * (input.cells + output.cells) + 100 ∧
      RunsFor restoreStoredInput
        ({ inputTape := input, outputTape := output } : Configuration) finish used ∧
      finish.halted = true ∧ finish.outputTape = output ∧
      finish.inputTape.current :: finish.inputTape.right =
        (retained.reverse ++ current :: right ++ List.replicate padding none).drop count := by
  dsimp only
  let input := (Tape.moveRight^[moves])
    ({ left := retained ++ none :: before, current := current, right := right } : Tape)
  obtain ⟨after, padding, hLeft, hCount, hContents⟩ :=
    retained_prefix_after_moves retained before current right moves
  change input.left = _ at hLeft
  change after.reverse ++ input.current :: input.right = _ at hContents
  obtain ⟨finish, used, count, hBound, run, hHalted, hOutput, hSuffix⟩ :=
    restoreStoredInput_terminates_from_retained_prefix after before input.current input.right output
      (hSeparators.trans hCount)
  have hInput : ({ left := after ++ none :: before, current := input.current, right := input.right } : Tape) = input := by
    rw [← hLeft]
  rw [hInput] at hBound run
  exact ⟨finish, used, count, padding, hBound, run, hHalted, hOutput, by rw [← hContents]; exact hSuffix⟩

/-- A common padded budget covers every branch of the real restoration
program, independently of a successful stored-input layout. -/
theorem restoreStoredInput_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor restoreStoredInput
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (100 * (input.cells + output.cells) + 100)) : finish.halted = true := by
  obtain ⟨target, used, hBound, trace, hHalted, _⟩ :=
    restoreStoredInput_terminates_from_anyTape input output
  have hEval := trace.evalConfigWithin_eq_pure_of_no_randomBit restoreStoredInput_no_randomBit
  have hAt (c : Configuration) (hc : PaddedRunsFor restoreStoredInput
      ({ inputTape := input, outputTape := output } : Configuration) c used) : c.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr hc
    rw [hEval, PMF.mem_support_pure_iff] at hMem
    simpa only [hMem] using hHalted
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAt, hEval, PMF.mem_support_pure_iff] at hMem
  simpa only [hMem] using hHalted

end Machine
