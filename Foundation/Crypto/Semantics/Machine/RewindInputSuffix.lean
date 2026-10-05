import Foundation.Crypto.Semantics.Machine.BitstringRewind

namespace Machine

/-- Restore the start of a known nonempty prefix while preserving its
nonempty unread suffix and the other tape. Only redundant outer blanks
are ignored by the postcondition. -/
theorem rewindBitstring_runs_suffix (prefixBits tail : List Bool) (output : Tape)
    (hPrefix : prefixBits ≠ []) (hTail : tail ≠ []) :
    ∃ target, RunsFor rewindBitstring
      ({inputTape := {Tape.ofBits tail with left := prefixBits.reverse.map some}, outputTape := output} : Configuration)
      target (2*prefixBits.length+4) ∧ target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits (prefixBits++tail)) ∧ target.outputTape = output := by
  have run := rewindBitstring_runs_from prefixBits (Tape.ofBits tail).current (Tape.ofBits tail).right output
  refine ⟨_, run, rfl, ?_, rfl⟩
  cases prefixBits with
  | nil => exact False.elim (hPrefix rfl)
  | cons bit rest =>
      cases tail with
    | nil => exact False.elim (hTail rfl)
      | cons first following =>
        refine ⟨rfl, ?_, ?_⟩
        · intro i; cases i <;> rfl
        · intro i
          simp only [List.map_cons, List.cons_append, List.map_append, Tape.ofBits, Tape.moveRight]

end Machine
