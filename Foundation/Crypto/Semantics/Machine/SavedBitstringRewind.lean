import Foundation.Crypto.Semantics.Machine.BitstringRewind

namespace Machine

private def savedRewindState (output : Tape) (before : List (Option Bool))
    (left : List Bool) (current : Option Bool) (right : List (Option Bool)) : Configuration :=
  { inputTape := { left := left.map some ++ none :: before, current := current, right := right }
    outputTape := output }

private def savedRewindFinish (output : Tape) (before : List (Option Bool))
    (left : List Bool) (current : Option Bool) (right : List (Option Bool)) : Configuration :=
  { pc := 3
    halted := true
    inputTape := ({ left := before, right := left.reverse.map some ++ current :: right } : Tape).moveRight
    outputTape := output }

private theorem saved_rewind_run (output : Tape) (before : List (Option Bool))
    (left : List Bool) (current : Option Bool) (right : List (Option Bool)) :
    RunsFor rewindBitstring (savedRewindState output before left current right)
      (savedRewindFinish output before left current right) (2*left.length+4) := by
  induction left generalizing current right with
  | nil =>
    let start := savedRewindState output before [] current right
    let moved := { start with pc := 1, inputTape := start.inputTape.moveLeft }
    let selected := { moved with pc := 2 }
    let restored := { selected with pc := 3, inputTape := selected.inputTape.moveRight }
    have one : Step rewindBitstring start moved := by
      simp [Step, successors, next, rewindBitstring, start, moved,
        savedRewindState, Instruction.next, Configuration.advance, Configuration.updateTape]
    have two : Step rewindBitstring moved selected := by
      simp [Step, successors, next, rewindBitstring, start, moved, selected,
        savedRewindState, Tape.moveLeft, Instruction.next, Configuration.tape]
    have three : Step rewindBitstring selected restored := by
      simp [Step, successors, next, rewindBitstring, start, moved, selected, restored,
        savedRewindState, Instruction.next, Configuration.advance, Configuration.updateTape]
    have four : Step rewindBitstring restored (savedRewindFinish output before [] current right) := by
      simp [Step, successors, next, rewindBitstring, start, moved, selected, restored,
        savedRewindState, savedRewindFinish, Instruction.next, Tape.moveLeft, Tape.moveRight]
    exact ((((RunsFor.zero _).succ one).succ two).succ three).succ four
  | cons bit rest ih =>
    let start := savedRewindState output before (bit::rest) current right
    let moved := { start with pc := 1, inputTape := start.inputTape.moveLeft }
    have one : Step rewindBitstring start moved := by
      simp [Step, successors, next, rewindBitstring, start, moved,
        savedRewindState, Instruction.next, Configuration.advance, Configuration.updateTape]
    have two : Step rewindBitstring moved
        (savedRewindState output before rest (some bit) (current::right)) := by
      cases bit <;> simp [Step, successors, next, rewindBitstring, start, moved,
        savedRewindState, Tape.moveLeft, Instruction.next, Configuration.tape]
    have same : savedRewindFinish output before rest (some bit) (current::right) =
        savedRewindFinish output before (bit::rest) current right := by
      simp [savedRewindFinish, List.reverse_cons, List.map_append, List.append_assoc]
    have result := (((RunsFor.zero _).succ one).succ two).trans (ih (some bit) (current::right))
    rw [same] at result
    convert result using 1 <;> simp [List.length_cons] <;> omega

/-- Rewind one real bit block without crossing the blank protecting the
caller prefix. In particular, a saved width counter is not read or erased.
Every move and branch is charged to the original four-instruction program. -/
theorem rewindBitstring_runs_saved (bits : List Bool) (before : List (Option Bool))
    (current : Option Bool) (right : List (Option Bool)) (output : Tape) :
    RunsFor rewindBitstring
      ({ inputTape := { left := bits.reverse.map some ++ none :: before, current := current, right := right }
         outputTape := output } : Configuration)
      ({ pc := 3
         halted := true
         inputTape := ({ left := before, right := bits.map some ++ current :: right } : Tape).moveRight
         outputTape := output } : Configuration)
      (2*bits.length+4) := by
  simpa only [savedRewindState, savedRewindFinish, List.reverse_reverse, List.length_reverse] using
    saved_rewind_run output before bits.reverse current right

private theorem getD_append_blanks (cells : List (Option Bool)) (blanks i : Nat) :
    (cells ++ List.replicate blanks none).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => exact (Tape.blank_padding_equivalent [] blanks).2.2 i
  | cons cell rest ih =>
    cases i with
    | zero => rfl
    | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

/-- The returned head is at the first bit, with the protected prefix still
present. Only redundant right-hand blank cells differ from the bitstring
representation; the saved prefix is not discarded by this equivalence. -/
theorem rewindBitstring_saved_input_equivalent (bits : List Bool)
    (before : List (Option Bool)) (blanks : Nat) :
    (({ left := before, right := bits.map some ++ none :: List.replicate blanks none } : Tape).moveRight).Equivalent
      { Tape.ofBits bits with left := none :: before } := by
  cases bits with
  | nil =>
    simpa only [List.map_nil, List.nil_append, Tape.moveRight, Tape.ofBits,
      List.replicate_succ] using Tape.blank_padding_equivalent (none::before) blanks
  | cons bit rest =>
    refine ⟨rfl, fun _ => rfl, ?_⟩
    intro i
    change (rest.map some ++ none :: List.replicate blanks none).getD i none =
      (rest.map some).getD i none
    rw [← List.replicate_succ]
    exact getD_append_blanks (rest.map some) (blanks+1) i

end Machine
