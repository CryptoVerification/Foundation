import Foundation.Crypto.Semantics.Machine.Subroutine
import Foundation.Crypto.Semantics.Machine.Execution

namespace Machine

open Foundation.Probability

/-- Move only the program counter into an embedded source block. The tapes
and halt flag retain their original values. -/
def Configuration.rebasePc (base : Nat) (c : Configuration) : Configuration :=
  { c with pc := base + c.pc }

@[simp] theorem Configuration.tape_rebasePc (base : Nat)
    (c : Configuration) (tape : TapeId) :
    (c.rebasePc base).tape tape = c.tape tape := by
  cases tape <;> rfl

@[simp] theorem Configuration.outputBits_rebasePc (base : Nat)
    (c : Configuration) :
    (c.rebasePc base).outputBits = c.outputBits := rfl

/-- Rebase both possible outcomes of a randomized instruction. -/
def rebaseStepResult (base : Nat) :
    Configuration ⊕ (Configuration × Configuration) →
      Configuration ⊕ (Configuration × Configuration)
  | .inl c => .inl (c.rebasePc base)
  | .inr (c₀, c₁) => .inr (c₀.rebasePc base, c₁.rebasePc base)

/-- Control-flow targets beyond the source code return to the caller. -/
def Configuration.relocatePc (base returnPc sourceLength : Nat)
    (c : Configuration) : Configuration :=
  { c with pc := subroutineAddress base returnPc sourceLength c.pc }

/-- A halted source invocation returns to active caller control, retaining
both tape contents and head positions. -/
def Configuration.resumeAt (returnPc : Nat) (c : Configuration) :
    Configuration :=
  { c with pc := returnPc, halted := false }

@[simp] theorem Configuration.outputBits_resumeAt (returnPc : Nat)
    (c : Configuration) :
    (c.resumeAt returnPc).outputBits = c.outputBits := rfl

@[simp] theorem Configuration.halted_resumeAt (returnPc : Nat)
    (c : Configuration) :
    (c.resumeAt returnPc).halted = false := rfl

/-- Returning to an explicit halt finishes the caller in one actual step. -/
theorem Step.resumeAt_halt {p : Program} (c : Configuration) (returnPc : Nat)
    (hLookup : p[returnPc]? = some .halt) :
    Step p (c.resumeAt returnPc) { c.resumeAt returnPc with halted := true } :=
  Step.halt rfl hLookup

/-- Sequential instructions leave control flow to the following address.
The branch, jump, and halt instructions require separate return cases. -/
def Instruction.IsSequential : Instruction → Prop
  | .moveLeft _ | .moveRight _ | .write _ _ | .erase _ |
    .randomBit _ => True
  | .halt | .branch _ _ _ _ | .jump _ => False

/-- A sequential source instruction takes the same tape step, including
both random-bit outcomes, after its program counter is rebased. -/
theorem Instruction.next_asSubroutine_sequential
    (i : Instruction) (base returnPc sourceLength : Nat)
    (c : Configuration) (hi : i.IsSequential) :
    (i.asSubroutine base returnPc sourceLength).next
        (c.rebasePc base) =
      rebaseStepResult base (i.next c) := by
  cases i <;> simp [Instruction.IsSequential] at hi
  all_goals
    cases c
    simp [Instruction.asSubroutine, Instruction.next,
      Configuration.rebasePc, rebaseStepResult,
      Configuration.advance, Configuration.updateTape]
    all_goals split <;> simp [Nat.add_assoc]

/-- A source jump targets the rebased address, or returns to the caller when
the original jump would leave the source code. -/
theorem Instruction.next_asSubroutine_jump
    (base returnPc sourceLength target : Nat) (c : Configuration) :
    ((Instruction.jump target).asSubroutine base returnPc sourceLength).next
        (c.rebasePc base) =
      .inl (({ c with pc := target }).relocatePc
        base returnPc sourceLength) := by
  rfl

/-- A branch reads the same tape cell and relocates only its selected
absolute target. -/
theorem Instruction.next_asSubroutine_branch
    (base returnPc sourceLength : Nat) (tape : TapeId)
    (blankPc zeroPc onePc : Nat) (c : Configuration) :
    ((Instruction.branch tape blankPc zeroPc onePc).asSubroutine
        base returnPc sourceLength).next (c.rebasePc base) =
      .inl (({ c with pc :=
        match (c.tape tape).current with
        | none => blankPc
        | some false => zeroPc
        | some true => onePc }).relocatePc
          base returnPc sourceLength) := by
  cases h : (c.tape tape).current with
  | none =>
      simp [Instruction.asSubroutine, Instruction.next,
        Configuration.relocatePc, h]; simp [Configuration.rebasePc]
  | some bit =>
      cases bit <;>
        simp [Instruction.asSubroutine, Instruction.next,
          Configuration.relocatePc, h] <;> simp [Configuration.rebasePc]

/-- Every operational outcome of a sequential source instruction remains an
operational outcome of the embedded copy, with only the program counter
rebased. In particular, both fair random-bit branches remain possible. -/
theorem Program.step_withSubroutine_sequential
    (pre source suffix : Program) (returnPc : Nat)
    {c d : Configuration}
    (hpc : c.pc < source.length)
    (hi : (source[c.pc]).IsSequential)
    (hstep : Step source c d) :
    Step (withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) (d.rebasePc pre.length) := by
  have hactive : c.halted = false := by
    cases h : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted h) hstep)
  have hsource : next source c = some ((source[c.pc]).next c) := by
    simp [next, hactive, List.getElem?_eq_getElem hpc]
  have htarget :
      next (withSubroutine pre source suffix returnPc)
          (c.rebasePc pre.length) =
        some (rebaseStepResult pre.length ((source[c.pc]).next c)) := by
    rw [Program.next_withSubroutine_source pre source suffix returnPc
      c.pc (c.rebasePc pre.length) hpc]
    · exact congrArg some
        ((source[c.pc]).next_asSubroutine_sequential
          pre.length returnPc source.length c hi)
    · simp [Configuration.rebasePc]
    · simpa [Configuration.rebasePc] using hactive
  unfold Step successors at hstep ⊢
  rw [hsource] at hstep
  rw [htarget]
  cases hnext : (source[c.pc]).next c with
  | inl target =>
      simp [rebaseStepResult, hnext] at hstep ⊢
      exact congrArg (Configuration.rebasePc pre.length) hstep
  | inr pair =>
      rcases pair with ⟨left, right⟩
      simp [rebaseStepResult, hnext] at hstep ⊢
      rcases hstep with rfl | rfl <;> simp

/-- An explicit jump of the source program becomes a jump to the relocated
address. Out-of-range source targets return to the caller. -/
theorem Program.step_withSubroutine_jump
    (pre source suffix : Program) (returnPc target : Nat)
    {c d : Configuration}
    (hpc : c.pc < source.length)
    (hi : source[c.pc] = .jump target)
    (hstep : Step source c d) :
    Step (withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length)
      (d.relocatePc pre.length returnPc source.length) := by
  have hactive : c.halted = false := by
    cases h : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted h) hstep)
  have hd : d = { c with pc := target } := by
    simpa [Step, successors, next, hactive,
      List.getElem?_eq_getElem hpc, hi, Instruction.next] using hstep
  subst d
  unfold Step successors
  rw [Program.next_withSubroutine_source pre source suffix returnPc
    c.pc (c.rebasePc pre.length) hpc
    (by simp [Configuration.rebasePc])
    (by simpa [Configuration.rebasePc] using hactive)]
  simp [hi, Instruction.next_asSubroutine_jump]

/-- A conditional source branch observes the same tape cell after embedding,
then relocates its selected address. -/
theorem Program.step_withSubroutine_branch
    (pre source suffix : Program) (returnPc : Nat)
    (tape : TapeId) (blankPc zeroPc onePc : Nat)
    {c d : Configuration}
    (hpc : c.pc < source.length)
    (hi : source[c.pc] = .branch tape blankPc zeroPc onePc)
    (hstep : Step source c d) :
    Step (withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length)
      (d.relocatePc pre.length returnPc source.length) := by
  have hactive : c.halted = false := by
    cases h : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted h) hstep)
  have hd : d = { c with pc :=
      match (c.tape tape).current with
      | none => blankPc
      | some false => zeroPc
      | some true => onePc } := by
    have hnext : next source c = some (.inl { c with pc :=
        match (c.tape tape).current with
        | none => blankPc
        | some false => zeroPc
        | some true => onePc }) := by
      simp [next, hactive, List.getElem?_eq_getElem hpc, hi,
        Instruction.next]
      rfl
    unfold Step successors at hstep
    rw [hnext] at hstep
    simpa using hstep
  subst d
  unfold Step successors
  rw [Program.next_withSubroutine_source pre source suffix returnPc
    c.pc (c.rebasePc pre.length) hpc
    (by simp [Configuration.rebasePc])
    (by simpa [Configuration.rebasePc] using hactive)]
  simp [hi, Instruction.next_asSubroutine_branch]

/-- A source jump beyond its code returns directly to the caller. The source
machine would need a further fall-off transition to become halted. -/
theorem Program.step_withSubroutine_jump_exit
    (pre source suffix : Program) (returnPc target : Nat)
    {c d : Configuration}
    (hpc : c.pc < source.length)
    (hi : source[c.pc] = .jump target)
    (hstep : Step source c d)
    (hout : source.length ≤ d.pc)
    (hactive : d.halted = false) :
    Step (withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) (d.resumeAt returnPc) := by
  have h := step_withSubroutine_jump pre source suffix returnPc target
    hpc hi hstep
  simpa [Configuration.relocatePc, Configuration.resumeAt,
    subroutineAddress_outOfRange _ _ _ _ hout, hactive] using h

/-- A conditional branch beyond the source code has the same direct-return
behavior. Its tape observation is already covered by the source step. -/
theorem Program.step_withSubroutine_branch_exit
    (pre source suffix : Program) (returnPc : Nat)
    (tape : TapeId) (blankPc zeroPc onePc : Nat)
    {c d : Configuration}
    (hpc : c.pc < source.length)
    (hi : source[c.pc] = .branch tape blankPc zeroPc onePc)
    (hstep : Step source c d)
    (hout : source.length ≤ d.pc)
    (hactive : d.halted = false) :
    Step (withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) (d.resumeAt returnPc) := by
  have h := step_withSubroutine_branch pre source suffix returnPc
    tape blankPc zeroPc onePc hpc hi hstep
  simpa [Configuration.relocatePc, Configuration.resumeAt,
    subroutineAddress_outOfRange _ _ _ _ hout, hactive] using h

/-- A source `halt` becomes a return to the caller in one step, preserving
the source's final tapes. -/
theorem Program.step_withSubroutine_halt
    (pre source suffix : Program) (returnPc : Nat)
    {c d : Configuration}
    (hpc : c.pc < source.length)
    (hi : source[c.pc] = .halt)
    (hstep : Step source c d) :
    Step (withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) (d.resumeAt returnPc) := by
  have hactive : c.halted = false := by
    cases h : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted h) hstep)
  have hd : d = { c with halted := true } := by
    simpa [Step, successors, next, hactive,
      List.getElem?_eq_getElem hpc, hi, Instruction.next] using hstep
  subst d
  unfold Step successors
  rw [Program.next_withSubroutine_source pre source suffix returnPc
    c.pc (c.rebasePc pre.length) hpc
    (by simp [Configuration.rebasePc])
    (by simpa [Configuration.rebasePc] using hactive)]
  simp [hi, Instruction.asSubroutine, Instruction.next,
    Configuration.rebasePc, Configuration.resumeAt, hactive]

/-- Falling off the source list also becomes an explicit return jump in one
step. The appended instruction is at source offset `source.length`. -/
theorem Program.step_withSubroutine_fallthrough
    (pre source suffix : Program) (returnPc : Nat)
    {c d : Configuration}
    (hpc : c.pc = source.length)
    (hstep : Step source c d) :
    Step (withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) (d.resumeAt returnPc) := by
  have hactive : c.halted = false := by
    cases h : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted h) hstep)
  have hd : d = { c with halted := true } := by
    have hnone : source[c.pc]? = none := by
      simp [hpc]
    simpa [Step, successors, next, hactive, hnone] using hstep
  subst d
  unfold Step successors
  rw [Program.next_withSubroutine_return pre source suffix returnPc
    (c.rebasePc pre.length)
    (by simp [Configuration.rebasePc, hpc])
    (by simpa [Configuration.rebasePc] using hactive)]
  simp [Configuration.rebasePc, Configuration.resumeAt, hactive]

/-- A source step that stays active inside the finite source code has a
matching wrapper step. This includes branches, jumps, and random outcomes. -/
theorem Program.step_withSubroutine_inside
    (pre source suffix : Program) (returnPc : Nat)
    {c d : Configuration}
    (hpc : c.pc < source.length)
    (hdpc : d.pc < source.length)
    (hdactive : d.halted = false)
    (hstep : Step source c d) :
    Step (withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) (d.rebasePc pre.length) := by
  cases hi : source[c.pc] with
  | halt =>
      have hactive : c.halted = false := by
        cases h : c.halted with
        | false => rfl
        | true => exact False.elim ((no_step_of_halted h) hstep)
      have hd : d = { c with halted := true } := by
        simpa [Step, successors, next, hactive,
          List.getElem?_eq_getElem hpc, hi, Instruction.next] using hstep
      simp [hd] at hdactive
  | jump target =>
      have hreloc := step_withSubroutine_jump pre source suffix
        returnPc target hpc hi hstep
      simpa [Configuration.relocatePc, Configuration.rebasePc,
        subroutineAddress_inRange _ _ _ _ hdpc] using hreloc
  | branch tape blankPc zeroPc onePc =>
      have hreloc := step_withSubroutine_branch pre source suffix
        returnPc tape blankPc zeroPc onePc hpc hi hstep
      simpa [Configuration.relocatePc, Configuration.rebasePc,
        subroutineAddress_inRange _ _ _ _ hdpc] using hreloc
  | moveLeft tape =>
      exact step_withSubroutine_sequential pre source suffix returnPc
        hpc (by simp [hi, Instruction.IsSequential]) hstep
  | moveRight tape =>
      exact step_withSubroutine_sequential pre source suffix returnPc
        hpc (by simp [hi, Instruction.IsSequential]) hstep
  | write tape bit =>
      exact step_withSubroutine_sequential pre source suffix returnPc
        hpc (by simp [hi, Instruction.IsSequential]) hstep
  | erase tape =>
      exact step_withSubroutine_sequential pre source suffix returnPc
        hpc (by simp [hi, Instruction.IsSequential]) hstep
  | randomBit tape =>
      exact step_withSubroutine_sequential pre source suffix returnPc
        hpc (by simp [hi, Instruction.IsSequential]) hstep

/-- A source trace whose intermediate configurations remain active inside
the source code. The terminal halt or fall-through step is recorded
separately, so this relation does not assume all programs are total. -/
inductive RunsInside (source : Program) :
    Configuration → Configuration → Nat → Prop where
  | zero (c : Configuration) : RunsInside source c c 0
  | succ {start middle finish : Configuration} {steps : Nat}
      (prior : RunsInside source start middle steps)
      (hMiddle : middle.pc < source.length)
      (hFinish : finish.pc < source.length)
      (hActive : finish.halted = false)
      (last : Step source middle finish) :
      RunsInside source start finish (steps + 1)

/-- Every internal source transition lifts to one transition of the
embedded code, with exactly the same transition count. -/
theorem RunsInside.withSubroutine
    (pre source suffix : Program) (returnPc : Nat)
    {start finish : Configuration} {steps : Nat}
    (run : RunsInside source start finish steps) :
    RunsFor (Program.withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) (finish.rebasePc pre.length) steps := by
  induction run with
  | zero => exact RunsFor.zero _
  | succ prior hMiddle hFinish hActive last ih =>
      exact RunsFor.succ ih
        (Program.step_withSubroutine_inside pre source suffix returnPc
          hMiddle hFinish hActive last)

/-- Append an explicit source `halt` to an internal trace. The target trace
ends at the caller continuation, with the source's final tapes. -/
theorem RunsInside.withSubroutine_halt
    (pre source suffix : Program) (returnPc : Nat)
    {start before finish : Configuration} {steps : Nat}
    (run : RunsInside source start before steps)
    (hpc : before.pc < source.length)
    (hi : source[before.pc] = .halt)
    (last : Step source before finish) :
    RunsFor (Program.withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) (finish.resumeAt returnPc)
      (steps + 1) :=
  RunsFor.succ (run.withSubroutine pre source suffix returnPc)
    (Program.step_withSubroutine_halt pre source suffix returnPc hpc hi last)

/-- A source trace that ends by falling off its instruction list likewise
returns to the caller in the same total number of transitions. -/
theorem RunsInside.withSubroutine_fallthrough
    (pre source suffix : Program) (returnPc : Nat)
    {start before finish : Configuration} {steps : Nat}
    (run : RunsInside source start before steps)
    (hpc : before.pc = source.length)
    (last : Step source before finish) :
    RunsFor (Program.withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) (finish.resumeAt returnPc)
      (steps + 1) :=
  RunsFor.succ (run.withSubroutine pre source suffix returnPc)
    (Program.step_withSubroutine_fallthrough pre source suffix returnPc hpc last)

/-- A sequential instruction at the end of the source code first reaches the
appended return instruction. The source's following fall-through halt then
corresponds to that return, so both executions use the same two transitions. -/
theorem RunsInside.withSubroutine_sequential_fallthrough
    (pre source suffix : Program) (returnPc : Nat)
    {start before outside finish : Configuration} {steps : Nat}
    (run : RunsInside source start before steps)
    (hpc : before.pc < source.length)
    (hi : (source[before.pc]).IsSequential)
    (nextStep : Step source before outside)
    (hout : outside.pc = source.length)
    (finalStep : Step source outside finish) :
    RunsFor (Program.withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) (finish.resumeAt returnPc)
      (steps + 2) := by
  have hInside := Program.step_withSubroutine_sequential pre source suffix
    returnPc hpc hi nextStep
  have hReturn := Program.step_withSubroutine_fallthrough pre source suffix
    returnPc hout finalStep
  simpa [Nat.add_assoc] using
    (RunsFor.succ (RunsFor.succ
      (run.withSubroutine pre source suffix returnPc) hInside) hReturn)

/-- A jump outside the source code uses one wrapper transition to return.
The source machine uses that jump and then a separate fall-off halt, so this
case shortens the wrapper trace by one transition without changing tapes. -/
theorem RunsInside.withSubroutine_jump_exit
    (pre source suffix : Program) (returnPc target : Nat)
    {start before outside finish : Configuration} {steps : Nat}
    (run : RunsInside source start before steps)
    (hpc : before.pc < source.length)
    (hi : source[before.pc] = .jump target)
    (jumpStep : Step source before outside)
    (hout : source.length ≤ outside.pc)
    (hactive : outside.halted = false)
    (haltStep : Step source outside finish) :
    RunsFor (Program.withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) (finish.resumeAt returnPc)
      (steps + 1) := by
  have hnone : source[outside.pc]? = none := by simp [hout]
  have hFinish : finish = { outside with halted := true } := by
    simpa [Step, successors, next, hactive, hnone] using haltStep
  have hReturn := Program.step_withSubroutine_jump_exit pre source suffix
    returnPc target hpc hi jumpStep hout hactive
  simpa [hFinish, Configuration.resumeAt] using
    (RunsFor.succ (run.withSubroutine pre source suffix returnPc) hReturn)

/-- The same one-step saving holds when a conditional branch leaves the
source code; its chosen branch is fixed by the source tape contents. -/
theorem RunsInside.withSubroutine_branch_exit
    (pre source suffix : Program) (returnPc : Nat)
    (tape : TapeId) (blankPc zeroPc onePc : Nat)
    {start before outside finish : Configuration} {steps : Nat}
    (run : RunsInside source start before steps)
    (hpc : before.pc < source.length)
    (hi : source[before.pc] = .branch tape blankPc zeroPc onePc)
    (branchStep : Step source before outside)
    (hout : source.length ≤ outside.pc)
    (hactive : outside.halted = false)
    (haltStep : Step source outside finish) :
    RunsFor (Program.withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) (finish.resumeAt returnPc)
      (steps + 1) := by
  have hnone : source[outside.pc]? = none := by simp [hout]
  have hFinish : finish = { outside with halted := true } := by
    simpa [Step, successors, next, hactive, hnone] using haltStep
  have hReturn := Program.step_withSubroutine_branch_exit pre source suffix
    returnPc tape blankPc zeroPc onePc hpc hi branchStep hout hactive
  simpa [hFinish, Configuration.resumeAt] using
    (RunsFor.succ (run.withSubroutine pre source suffix returnPc) hReturn)

/-- The first source copy in `withTwoSubroutines` returns to the middle
wrapper block after exactly the source trace's number of transitions. -/
theorem Program.withTwoSubroutines_first_run_halt
    (pre middle post source : Program)
    {start before finish : Configuration} {steps : Nat}
    (run : RunsInside source start before steps)
    (hpc : before.pc < source.length)
    (hi : source[before.pc] = .halt)
    (last : Step source before finish) :
    RunsFor (withTwoSubroutines pre middle post source)
      (start.rebasePc pre.length)
      (finish.resumeAt (pre.length + source.length + 1))
      (steps + 1) := by
  rw [withTwoSubroutines_first_layout]
  exact run.withSubroutine_halt pre source _ _ hpc hi last

/-- The second source copy has the same operational behavior, now returning
to the final wrapper block. The source program is the same finite code. -/
theorem Program.withTwoSubroutines_second_run_halt
    (pre middle post source : Program)
    {start before finish : Configuration} {steps : Nat}
    (run : RunsInside source start before steps)
    (hpc : before.pc < source.length)
    (hi : source[before.pc] = .halt)
    (last : Step source before finish) :
    RunsFor (withTwoSubroutines pre middle post source)
      (start.rebasePc (pre.length + source.length + 1 + middle.length))
      (finish.resumeAt (pre.length + source.length + 1 +
        middle.length + source.length + 1))
      (steps + 1) := by
  rw [withTwoSubroutines_second_layout]
  simpa only [List.length_append, asSubroutine_length, Nat.add_assoc]
    using run.withSubroutine_halt
      (pre ++ source.asSubroutine pre.length
        (pre.length + source.length + 1) ++ middle)
      source post
      (pre.length + source.length + 1 + middle.length +
        source.length + 1) hpc hi last

/-- A sequential source transition increments the program counter once and
keeps the machine active, for either outcome of a random-bit instruction. -/
theorem Program.step_sequential_control
    {source : Program} {c d : Configuration}
    (hpc : c.pc < source.length) (hactive : c.halted = false)
    (hseq : (source[c.pc]).IsSequential) (hstep : Step source c d) :
    d.pc = c.pc + 1 ∧ d.halted = false := by
  have hnext : next source c = some ((source[c.pc]).next c) := by
    simp [next, hactive, List.getElem?_eq_getElem hpc]
  unfold Step successors at hstep
  rw [hnext] at hstep
  cases hi : source[c.pc] <;> simp [Instruction.IsSequential, hi] at hseq
  all_goals simp [hi, Instruction.next] at hstep
  all_goals
    first
    | (subst d; simp [Configuration.advance, Configuration.updateTape, hactive])
    | (rcases hstep with rfl | rfl <;>
        simp [Configuration.advance, Configuration.updateTape, hactive])
  all_goals split <;> simp

private theorem resumed_eq_of_outside_run
    {source : Program} {start finish : Configuration} {steps : Nat}
    (run : RunsFor source start finish steps)
    (hout : source.length ≤ start.pc) (hactive : start.halted = false)
    (returnPc : Nat) :
    finish.resumeAt returnPc = start.resumeAt returnPc := by
  cases steps with
  | zero => cases run; rfl
  | succ steps =>
      obtain ⟨middle, first, rest⟩ := run.head
      have hnone : source[start.pc]? = none := by simp [hout]
      have hMiddle : middle = { start with halted := true } := by
        simpa [Step, successors, next, hactive, hnone] using first
      subst middle
      obtain ⟨_, hFinish⟩ := rest.eq_of_halted_start rfl
      subst finish
      rfl

private theorem subroutine_step_cases
    (pre source suffix : Program) (returnPc : Nat)
    {c d : Configuration} (hpcLe : c.pc ≤ source.length)
    (hactive : c.halted = false) (hstep : Step source c d) :
    (d.halted = false ∧ d.pc ≤ source.length ∧
      Step (Program.withSubroutine pre source suffix returnPc)
        (c.rebasePc pre.length) (d.rebasePc pre.length)) ∨
    ((d.halted = true ∨ source.length ≤ d.pc) ∧
      Step (Program.withSubroutine pre source suffix returnPc)
        (c.rebasePc pre.length) (d.resumeAt returnPc)) := by
  by_cases hpc : c.pc < source.length
  · have hseqCase (hseq : (source[c.pc]).IsSequential) :
        (d.halted = false ∧ d.pc ≤ source.length ∧
          Step (Program.withSubroutine pre source suffix returnPc)
            (c.rebasePc pre.length) (d.rebasePc pre.length)) ∨
        ((d.halted = true ∨ source.length ≤ d.pc) ∧
          Step (Program.withSubroutine pre source suffix returnPc)
            (c.rebasePc pre.length) (d.resumeAt returnPc)) := by
      obtain ⟨hdpc, hdactive⟩ := Program.step_sequential_control hpc hactive hseq hstep
      exact Or.inl ⟨hdactive, by omega,
        Program.step_withSubroutine_sequential pre source suffix returnPc
          hpc hseq hstep⟩
    cases hi : source[c.pc] with
    | halt =>
        have hd : d = { c with halted := true } := by
          simpa [Step, successors, next, hactive,
            List.getElem?_eq_getElem hpc, hi, Instruction.next] using hstep
        exact Or.inr ⟨Or.inl (by simp [hd]),
          Program.step_withSubroutine_halt pre source suffix returnPc hpc hi hstep⟩
    | jump target =>
        have hd : d = { c with pc := target } := by
          simpa [Step, successors, next, hactive,
            List.getElem?_eq_getElem hpc, hi, Instruction.next] using hstep
        have hdactive : d.halted = false := by simp [hd, hactive]
        by_cases hdpc : d.pc < source.length
        · exact Or.inl ⟨hdactive, Nat.le_of_lt hdpc,
            Program.step_withSubroutine_inside pre source suffix returnPc
              hpc hdpc hdactive hstep⟩
        · have hout : source.length ≤ d.pc := by omega
          exact Or.inr ⟨Or.inr hout,
            Program.step_withSubroutine_jump_exit pre source suffix returnPc
              target hpc hi hstep hout hdactive⟩
    | branch tape blankPc zeroPc onePc =>
        have hnext : next source c = some (.inl { c with pc :=
            match (c.tape tape).current with
            | none => blankPc
            | some false => zeroPc
            | some true => onePc }) := by
          simp [next, hactive, List.getElem?_eq_getElem hpc, hi, Instruction.next]
          rfl
        have hd : d = { c with pc :=
            match (c.tape tape).current with
            | none => blankPc
            | some false => zeroPc
            | some true => onePc } := by
          simpa [Step, successors, hnext] using hstep
        have hdactive : d.halted = false := by simp [hd, hactive]
        by_cases hdpc : d.pc < source.length
        · exact Or.inl ⟨hdactive, Nat.le_of_lt hdpc,
            Program.step_withSubroutine_inside pre source suffix returnPc
              hpc hdpc hdactive hstep⟩
        · have hout : source.length ≤ d.pc := by omega
          exact Or.inr ⟨Or.inr hout,
            Program.step_withSubroutine_branch_exit pre source suffix returnPc
              tape blankPc zeroPc onePc hpc hi hstep hout hdactive⟩
    | moveLeft tape => exact hseqCase (by simp [hi, Instruction.IsSequential])
    | moveRight tape => exact hseqCase (by simp [hi, Instruction.IsSequential])
    | write tape bit => exact hseqCase (by simp [hi, Instruction.IsSequential])
    | erase tape => exact hseqCase (by simp [hi, Instruction.IsSequential])
    | randomBit tape => exact hseqCase (by simp [hi, Instruction.IsSequential])
  · have heq : c.pc = source.length := by omega
    have hd : d = { c with halted := true } := by
      simpa [Step, successors, next, hactive, heq] using hstep
    exact Or.inr ⟨Or.inl (by simp [hd]),
      Program.step_withSubroutine_fallthrough pre source suffix returnPc heq hstep⟩

/-- Any halted source trace starting within its code (or at its fall-through
address) has a returning wrapper trace with no more actual transitions.
Both final tapes and head positions are retained. No assumption restricts the
source's branch addresses or random choices. -/
theorem RunsFor.withSubroutine_halted
    (pre source suffix : Program) (returnPc : Nat)
    {start finish : Configuration} {steps : Nat}
    (run : RunsFor source start finish steps)
    (hpc : start.pc ≤ source.length) (hactive : start.halted = false)
    (hfinish : finish.halted = true) :
    ∃ used, used ≤ steps ∧
      RunsFor (Program.withSubroutine pre source suffix returnPc)
        (start.rebasePc pre.length) (finish.resumeAt returnPc) used := by
  induction steps generalizing start with
  | zero =>
      cases run
      simp [hactive] at hfinish
  | succ steps ih =>
      obtain ⟨middle, first, rest⟩ := run.head
      rcases subroutine_step_cases pre source suffix returnPc hpc hactive first with
        ⟨hmactive, hmpc, hnext⟩ | ⟨hExit, hreturn⟩
      · obtain ⟨used, hUsed, hRest⟩ := ih rest hmpc hmactive
        refine ⟨1 + used, by omega, ?_⟩
        exact (RunsFor.succ (RunsFor.zero _) hnext).trans hRest
      · have hResume : finish.resumeAt returnPc = middle.resumeAt returnPc := by
          rcases hExit with hmhalted | hmoutside
          · obtain ⟨_, hEq⟩ := rest.eq_of_halted_start hmhalted
            simp [hEq]
          · cases hm : middle.halted with
            | true =>
                obtain ⟨_, hEq⟩ := rest.eq_of_halted_start hm
                simp [hEq]
            | false => exact resumed_eq_of_outside_run rest hmoutside hm returnPc
        refine ⟨1, by omega, ?_⟩
        rw [hResume]
        exact RunsFor.succ (RunsFor.zero _) hreturn

/-- A complete standalone source execution gives a returning invocation with
the same output and at most the source's number of transitions. This is a
trace simulation; a universal wrapper-branch bound additionally needs the
reverse simulation up to the caller continuation. -/
theorem HaltsWith.withSubroutine_returns
    (pre source suffix : Program) (returnPc : Nat)
    {input output : List Bool} {steps : Nat}
    (halts : HaltsWith source input output steps) :
    ∃ returned used, used ≤ steps ∧
      RunsFor (Program.withSubroutine pre source suffix returnPc)
        ((Configuration.initial input).rebasePc pre.length) returned used ∧
      returned.pc = returnPc ∧ returned.halted = false ∧
      returned.outputBits = output := by
  obtain ⟨finish, run, hHalted, hOutput⟩ := halts
  obtain ⟨used, hUsed, hRun⟩ := run.withSubroutine_halted
    pre source suffix returnPc (by simp [Configuration.initial]) rfl hHalted
  exact ⟨finish.resumeAt returnPc, used, hUsed, hRun,
    rfl, rfl, hOutput⟩

/-- A sequential embedded instruction preserves the entire one-step
probability distribution, including the fair probabilities of `randomBit`.
Only the program counter is rebased. -/
theorem Program.stepPMF_withSubroutine_sequential
    (pre source suffix : Program) (returnPc : Nat)
    (c : Configuration)
    (hpc : c.pc < source.length)
    (hactive : c.halted = false)
    (hi : (source[c.pc]).IsSequential) :
    stepPMF (withSubroutine pre source suffix returnPc)
        (c.rebasePc pre.length) =
      (stepPMF source c).map (Configuration.rebasePc pre.length) := by
  have hsource : next source c = some ((source[c.pc]).next c) := by
    simp [next, hactive, List.getElem?_eq_getElem hpc]
  have htarget :
      next (withSubroutine pre source suffix returnPc)
          (c.rebasePc pre.length) =
        some (rebaseStepResult pre.length ((source[c.pc]).next c)) := by
    rw [Program.next_withSubroutine_source pre source suffix returnPc
      c.pc (c.rebasePc pre.length) hpc]
    · exact congrArg some
        ((source[c.pc]).next_asSubroutine_sequential
          pre.length returnPc source.length c hi)
    · simp [Configuration.rebasePc]
    · simpa [Configuration.rebasePc] using hactive
  cases hnext : (source[c.pc]).next c with
  | inl target =>
      simp [stepPMF, hsource, htarget, hnext,
        rebaseStepResult, PMF.pure_map]
  | inr pair =>
      rcases pair with ⟨left, right⟩
      simp only [stepPMF, hsource, htarget, hnext, rebaseStepResult]
      rw [PMF.map_comp]
      congr 1
      funext b
      cases b <;> rfl

/-- A jump's deterministic probability distribution is preserved after
relocating its destination. -/
theorem Program.stepPMF_withSubroutine_jump
    (pre source suffix : Program) (returnPc target : Nat)
    (c : Configuration) (hpc : c.pc < source.length)
    (hactive : c.halted = false)
    (hi : source[c.pc] = .jump target) :
    stepPMF (withSubroutine pre source suffix returnPc)
        (c.rebasePc pre.length) =
      (stepPMF source c).map
        (Configuration.relocatePc pre.length returnPc source.length) := by
  have hsource : next source c = some (.inl { c with pc := target }) := by
    simp [next, hactive, List.getElem?_eq_getElem hpc, hi,
      Instruction.next]
  have htarget : next (withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) =
      some (.inl (({ c with pc := target }).relocatePc
        pre.length returnPc source.length)) := by
    rw [Program.next_withSubroutine_source pre source suffix returnPc
      c.pc (c.rebasePc pre.length) hpc
      (by simp [Configuration.rebasePc])
      (by simpa [Configuration.rebasePc] using hactive)]
    simp [hi, Instruction.next_asSubroutine_jump]
  simp [stepPMF, hsource, htarget, PMF.pure_map]

/-- A conditional branch has the same deterministic distribution after its
selected destination is relocated. -/
theorem Program.stepPMF_withSubroutine_branch
    (pre source suffix : Program) (returnPc : Nat)
    (tape : TapeId) (blankPc zeroPc onePc : Nat)
    (c : Configuration) (hpc : c.pc < source.length)
    (hactive : c.halted = false)
    (hi : source[c.pc] = .branch tape blankPc zeroPc onePc) :
    stepPMF (withSubroutine pre source suffix returnPc)
        (c.rebasePc pre.length) =
      (stepPMF source c).map
        (Configuration.relocatePc pre.length returnPc source.length) := by
  let d : Configuration := { c with pc :=
    match (c.tape tape).current with
    | none => blankPc
    | some false => zeroPc
    | some true => onePc }
  have hsource : next source c = some (.inl d) := by
    dsimp [d]
    simp [next, hactive, List.getElem?_eq_getElem hpc, hi,
      Instruction.next]
    rfl
  have htarget : next (withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) =
      some (.inl (d.relocatePc pre.length returnPc source.length)) := by
    rw [Program.next_withSubroutine_source pre source suffix returnPc
      c.pc (c.rebasePc pre.length) hpc
      (by simp [Configuration.rebasePc])
      (by simpa [Configuration.rebasePc] using hactive)]
    simpa [hi, d] using Instruction.next_asSubroutine_branch
      pre.length returnPc source.length tape blankPc zeroPc onePc c
  simp [stepPMF, hsource, htarget, PMF.pure_map]

/-- A source halt's point mass is carried to the resumed caller state. -/
theorem Program.stepPMF_withSubroutine_halt
    (pre source suffix : Program) (returnPc : Nat)
    (c : Configuration) (hpc : c.pc < source.length)
    (hactive : c.halted = false)
    (hi : source[c.pc] = .halt) :
    stepPMF (withSubroutine pre source suffix returnPc)
        (c.rebasePc pre.length) =
      (stepPMF source c).map (Configuration.resumeAt returnPc) := by
  have hsource : next source c =
      some (.inl { c with halted := true }) := by
    simp [next, hactive, List.getElem?_eq_getElem hpc, hi,
      Instruction.next]
  have htarget : next (withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) =
      some (.inl (({ c with halted := true }).resumeAt returnPc)) := by
    rw [Program.next_withSubroutine_source pre source suffix returnPc
      c.pc (c.rebasePc pre.length) hpc
      (by simp [Configuration.rebasePc])
      (by simpa [Configuration.rebasePc] using hactive)]
    simp [hi, Instruction.asSubroutine, Instruction.next,
      Configuration.rebasePc, Configuration.resumeAt, hactive]
  simp [stepPMF, hsource, htarget, PMF.pure_map]

/-- A source fall-through's point mass is also carried to the caller. -/
theorem Program.stepPMF_withSubroutine_fallthrough
    (pre source suffix : Program) (returnPc : Nat)
    (c : Configuration) (hpc : c.pc = source.length)
    (hactive : c.halted = false) :
    stepPMF (withSubroutine pre source suffix returnPc)
        (c.rebasePc pre.length) =
      (stepPMF source c).map (Configuration.resumeAt returnPc) := by
  have hsource : next source c =
      some (.inl { c with halted := true }) := by
    simp [next, hactive, hpc]
  have htarget : next (withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) =
      some (.inl (({ c with halted := true }).resumeAt returnPc)) := by
    rw [Program.next_withSubroutine_return pre source suffix returnPc
      (c.rebasePc pre.length)
      (by simp [Configuration.rebasePc, hpc])
      (by simpa [Configuration.rebasePc] using hactive)]
    simp [Configuration.rebasePc, Configuration.resumeAt, hactive]
  simp [stepPMF, hsource, htarget, PMF.pure_map]

/-- A trace ending in an active configuration stays inside the source
whenever active source steps cannot leave its code. This records the
control invariant needed to lift exact deterministic subroutine traces. -/
theorem RunsFor.toRunsInside_of_closed {source : Program}
    {start finish : Configuration} {steps : Nat}
    (run : RunsFor source start finish steps) (hStart : start.pc < source.length)
    (hClosed : ∀ c d, c.pc < source.length → Step source c d →
      d.halted = false → d.pc < source.length) (hFinish : finish.halted = false) :
    RunsInside source start finish steps ∧ finish.pc < source.length := by
  revert hFinish
  induction run with
  | zero => intro _; exact ⟨RunsInside.zero _, hStart⟩
  | @succ middle finish steps prior last ih =>
      intro hFinish
      have hMiddle : middle.halted = false := by
        cases hh : middle.halted with
        | false => rfl
        | true => exact False.elim ((no_step_of_halted hh) last)
      obtain ⟨inside, hPc⟩ := ih hMiddle
      have hNextPc := hClosed middle finish hPc last hFinish
      exact ⟨RunsInside.succ inside hPc hNextPc hFinish last, hNextPc⟩

private theorem asSubroutine_eq_randomBit_iff (i : Instruction)
    (base returnPc sourceLength : Nat) (tape : TapeId) :
    i.asSubroutine base returnPc sourceLength = .randomBit tape ↔ i = .randomBit tape := by
  cases i <;> simp [Instruction.asSubroutine]

/-- A deterministic instruction in the embedded block still has an exact
point-mass transition if surrounding caller code contains randomness. -/
theorem Program.stepPMF_withSubroutine_inside_of_no_randomBit
    (pre source suffix : Program) (returnPc : Nat)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ source)
    {c d : Configuration} (hpc : c.pc < source.length) (hdpc : d.pc < source.length)
    (hActive : d.halted = false) (step : Step source c d) :
    stepPMF (withSubroutine pre source suffix returnPc) (c.rebasePc pre.length) =
      PMF.pure (d.rebasePc pre.length) := by
  apply stepPMF_eq_pure_of_not_randomBit_at
    (step_withSubroutine_inside pre source suffix returnPc hpc hdpc hActive step)
  intro tape hWrong
  have hLookup := withSubroutine_getElem?_source pre source suffix returnPc c.pc hpc
  change (withSubroutine pre source suffix returnPc)[pre.length + c.pc]? =
    some (.randomBit tape) at hWrong
  rw [hLookup, List.getElem?_eq_getElem hpc, Option.map_some] at hWrong
  have hSource : source[c.pc] = .randomBit tape :=
    (asSubroutine_eq_randomBit_iff _ _ _ _ tape).mp (Option.some.inj hWrong)
  exact hNoRandom tape (by rw [← hSource]; exact List.getElem_mem hpc)

theorem RunsInside.evalConfigWithin_withSubroutine_of_no_randomBit
    (pre source suffix : Program) (returnPc : Nat)
    {start finish : Configuration} {steps : Nat}
    (run : RunsInside source start finish steps)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ source) :
    evalConfigWithin (Program.withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) steps = PMF.pure (finish.rebasePc pre.length) := by
  induction run with
  | zero => rfl
  | succ prior hMiddle hFinish hActive last ih =>
      simp only [evalConfigWithin, ih, PMF.pure_bind]
      exact Program.stepPMF_withSubroutine_inside_of_no_randomBit
        pre source suffix returnPc hNoRandom hMiddle hFinish hActive last

theorem RunsInside.evalConfigWithin_withSubroutine_halt_of_no_randomBit
    (pre source suffix : Program) (returnPc : Nat)
    {start before finish : Configuration} {steps : Nat}
    (run : RunsInside source start before steps)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ source)
    (hPc : before.pc < source.length) (hi : source[before.pc] = .halt)
    (last : Step source before finish) :
    evalConfigWithin (Program.withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) (steps + 1) = PMF.pure (finish.resumeAt returnPc) := by
  have hActive : before.halted = false := by
    cases hh : before.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) last)
  rw [evalConfigWithin,
    run.evalConfigWithin_withSubroutine_of_no_randomBit pre source suffix returnPc hNoRandom,
    PMF.pure_bind, Program.stepPMF_withSubroutine_halt pre source suffix returnPc before hPc
      hActive hi, stepPMF_eq_pure_of_no_randomBit hNoRandom last, PMF.pure_map]

/-- A transition that halts from an address inside the code executes an
explicit halt instruction, rather than falling off the code. -/
theorem Program.halt_instruction_of_step {source : Program} {c d : Configuration}
    (hPc : c.pc < source.length) (step : Step source c d) (hHalt : d.halted = true) :
    source[c.pc] = .halt := by
  have hActive : c.halted = false := by
    cases hh : c.halted with
    | false => rfl
    | true => exact False.elim ((no_step_of_halted hh) step)
  cases hi : source[c.pc] with
  | halt => rfl
  | jump target =>
      have hd : d = { c with pc := target } := by
        simpa [Step, successors, next, hActive, List.getElem?_eq_getElem hPc,
          hi, Instruction.next] using step
      simp [hd, hActive] at hHalt
  | branch tape blank zeroPc one =>
      have hNext : next source c = some (.inl { c with pc :=
          match (c.tape tape).current with
          | none => blank | some false => zeroPc | some true => one }) := by
        simp [next, hActive, List.getElem?_eq_getElem hPc, hi, Instruction.next]
        rfl
      have hd : d = { c with pc := match (c.tape tape).current with
          | none => blank | some false => zeroPc | some true => one } := by
        simpa [Step, successors, hNext] using step
      simp [hd, hActive] at hHalt
  | moveLeft tape | moveRight tape | write tape bit | erase tape | randomBit tape =>
      have hSequential : (source[c.pc]).IsSequential := by
        simp [hi, Instruction.IsSequential]
      have hRunning := (Program.step_sequential_control hPc hActive hSequential step).2
      simp [hRunning] at hHalt

/-- A closed, deterministic subroutine returns with exactly the source
trace's transition count and configuration distribution. Caller instructions
outside the embedded block may use randomness. -/
theorem RunsFor.evalConfigWithin_withSubroutine_halted_of_closed
    (pre source suffix : Program) (returnPc : Nat)
    {start finish : Configuration} {steps : Nat}
    (run : RunsFor source start finish steps)
    (hStart : start.pc < source.length) (hActive : start.halted = false)
    (hFinish : finish.halted = true)
    (hClosed : ∀ c d, c.pc < source.length → Step source c d →
      d.halted = false → d.pc < source.length)
    (hNoRandom : ∀ tape, Instruction.randomBit tape ∉ source) :
    evalConfigWithin (Program.withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) steps = PMF.pure (finish.resumeAt returnPc) := by
  cases run with
  | zero => simp [hActive] at hFinish
  | @succ before finish steps prior last =>
      have hBefore : before.halted = false := by
        cases hh : before.halted with
        | false => rfl
        | true => exact False.elim ((no_step_of_halted hh) last)
      obtain ⟨inside, hPc⟩ := prior.toRunsInside_of_closed hStart hClosed hBefore
      exact inside.evalConfigWithin_withSubroutine_halt_of_no_randomBit
        pre source suffix returnPc hNoRandom hPc
        (Program.halt_instruction_of_step hPc last hFinish) last

/-- Explicit in-code halting retains the exact operational transition count
when the source is embedded as a returning subroutine. -/
theorem RunsFor.withSubroutine_halted_of_closed
    (pre source suffix : Program) (returnPc : Nat)
    {start finish : Configuration} {steps : Nat}
    (run : RunsFor source start finish steps)
    (hStart : start.pc < source.length) (hActive : start.halted = false)
    (hFinish : finish.halted = true)
    (hClosed : ∀ c d, c.pc < source.length → Step source c d →
      d.halted = false → d.pc < source.length) :
    RunsFor (Program.withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) (finish.resumeAt returnPc) steps := by
  cases run with
  | zero => simp [hActive] at hFinish
  | @succ before finish steps prior last =>
      have hBefore : before.halted = false := by
        cases hh : before.halted with
        | false => rfl
        | true => exact False.elim ((no_step_of_halted hh) last)
      obtain ⟨inside, hPc⟩ := prior.toRunsInside_of_closed hStart hClosed hBefore
      exact inside.withSubroutine_halt pre source suffix returnPc hPc
        (Program.halt_instruction_of_step hPc last hFinish) last

end Machine
