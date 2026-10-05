import Foundation.Crypto.Semantics.Machine.NativeInvocation

namespace Machine

/-- Link two finite programs using relocated return jumps. Both physical
tapes pass directly from the first execution to the second execution. -/
def Program.followedBy (first second : Program) : Program :=
  first.asSubroutine 0 (first.length + 1) ++
    second.asSubroutine (first.length + 1) (first.length + second.length + 2) ++ [.halt]

theorem RunsFor.followedBy {first second : Program}
    {start middle finish : Configuration} {u v : Nat}
    (one : RunsFor first start middle u)
    (two : RunsFor second (middle.resumeAt 0) finish v)
    (hPc : start.pc ≤ first.length) (hActive : start.halted = false)
    (hMiddle : middle.halted = true) (hFinish : finish.halted = true) :
    ∃ used, used ≤ u + v + 1 ∧
      RunsFor (first.followedBy second) start
        { finish.resumeAt (first.length + second.length + 2) with halted := true } used := by
  let entry := first.length + 1
  let exit := first.length + second.length + 2
  let callerCode := first.asSubroutine 0 entry
  have firstLayout : first.followedBy second =
      Program.withSubroutine [] first (second.asSubroutine entry exit ++ [.halt]) entry := by
    simp [Program.followedBy, Program.withSubroutine, entry, exit]
  have secondLayout : first.followedBy second =
      Program.withSubroutine callerCode second [.halt] exit := by
    simp [Program.followedBy, Program.withSubroutine, callerCode, entry, exit, List.append_assoc]
  obtain ⟨a, ha, ra⟩ := one.withSubroutine_halted [] first
    (second.asSubroutine entry exit ++ [.halt]) entry hPc hActive hMiddle
  obtain ⟨b, hb, rb⟩ := two.withSubroutine_halted callerCode second [.halt] exit
    (Nat.zero_le _) rfl hFinish
  have firstRun : RunsFor (first.followedBy second) start (middle.resumeAt entry) a := by
    simpa [← firstLayout, Configuration.rebasePc] using ra
  have secondRun : RunsFor (first.followedBy second)
      (middle.resumeAt entry) (finish.resumeAt exit) b := by
    simpa [← secondLayout, callerCode, entry, Configuration.resumeAt,
      Configuration.rebasePc] using rb
  have lookup : (first.followedBy second)[exit]? = some .halt := by
    rw [secondLayout]
    have address : exit = callerCode.length + second.length + 1 + 0 := by
      simp [exit, callerCode, entry]
      omega
    rw [address, Program.withSubroutine_getElem?_suffix]
    rfl
  have stop : Step (first.followedBy second) (finish.resumeAt exit)
      { finish.resumeAt exit with halted := true } := by
    simp [Step, successors, next, Configuration.resumeAt, lookup, Instruction.next]
  exact ⟨a + b + 1, by omega, (firstRun.trans secondRun).succ stop⟩

theorem Program.followedBy_no_randomBit (first second : Program)
    (hFirst : ∀ tape, Instruction.randomBit tape ∉ first)
    (hSecond : ∀ tape, Instruction.randomBit tape ∉ second) (tape : TapeId) :
    Instruction.randomBit tape ∉ first.followedBy second := by
  simp only [Program.followedBy, List.mem_append, not_or]
  exact ⟨⟨Program.asSubroutine_no_randomBit first hFirst _ _ tape,
    Program.asSubroutine_no_randomBit second hSecond _ _ tape⟩, by simp⟩

/-- Invoke the second program on the actual returned tapes. Cellwise
equivalence only changes redundant blank representations; no tape is loaded
or reset at the call boundary. -/
theorem RunsFor.followedBy_equivalent {first second : Program}
    {start middle canonical finish : Configuration} {u v : Nat}
    (one : RunsFor first start middle u) (two : RunsFor second canonical finish v)
    (layout : canonical.Equivalent (middle.resumeAt 0))
    (hPc : start.pc ≤ first.length) (hActive : start.halted = false)
    (hMiddle : middle.halted = true) (hFinish : finish.halted = true) :
    ∃ (target : Configuration) (used : Nat), used ≤ u+v+1 ∧
      RunsFor (first.followedBy second) start target used ∧ target.halted = true ∧
      finish.inputTape.Equivalent target.inputTape ∧ finish.outputTape.Equivalent target.outputTape := by
  obtain ⟨actual, actualRun, hActual⟩ := two.exists_equivalent layout
  have stopped : actual.halted = true := hActual.2.1.symm.trans hFinish
  obtain ⟨used, hUsed, run⟩ := one.followedBy actualRun hPc hActive hMiddle stopped
  exact ⟨_, used, hUsed, run, rfl, hActual.2.2.1, hActual.2.2.2⟩

end Machine
