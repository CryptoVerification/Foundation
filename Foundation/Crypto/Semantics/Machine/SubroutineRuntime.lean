import Foundation.Crypto.Semantics.Machine.SubroutineSimulation

namespace Machine

/-- Execute a caller invocation until its return address is reached. At that
address only a bookkeeping stutter is permitted; it is not an extra machine
transition and does not execute the caller's continuation. -/
def ReturnStep (p : Program) (returnPc : Nat)
    (c d : Configuration) : Prop :=
  (c.pc ≠ returnPc ∧ Step p c d) ∨ (c.pc = returnPc ∧ d = c)

inductive ReturnRunsFor (p : Program) (returnPc : Nat) :
    Configuration → Configuration → Nat → Prop where
  | zero (c : Configuration) : ReturnRunsFor p returnPc c c 0
  | succ {start middle finish : Configuration} {steps : Nat}
      (prior : ReturnRunsFor p returnPc start middle steps)
      (last : ReturnStep p returnPc middle finish) :
      ReturnRunsFor p returnPc start finish (steps + 1)

/-- Discard the bookkeeping padding: the same final configuration is reached
by at most this many actual machine transitions. -/
theorem ReturnRunsFor.toRunsFor {p : Program} {returnPc : Nat}
    {start finish : Configuration} {steps : Nat}
    (run : ReturnRunsFor p returnPc start finish steps) :
    ∃ used, used ≤ steps ∧ RunsFor p start finish used := by
  induction run with
  | zero => exact ⟨0, Nat.le_refl _, RunsFor.zero _⟩
  | succ prior last ih =>
      obtain ⟨used, hle, hrun⟩ := ih
      rcases last with ⟨_, hstep⟩ | ⟨_, rfl⟩
      · exact ⟨used + 1, Nat.add_le_add_right hle 1,
          RunsFor.succ hrun hstep⟩
      · exact ⟨used, by omega, hrun⟩

/-- Every random branch of an invocation reaches the continuation by this
bound. Padding after return permits a common bound without charging the
caller continuation to the source subroutine. -/
def ReturnsWithin (p : Program) (start : Configuration)
    (returnPc bound : Nat) : Prop :=
  ∀ finish, ReturnRunsFor p returnPc start finish bound → finish.pc = returnPc

private theorem sequential_step_source
    (pre source suffix : Program) (returnPc : Nat)
    {c target : Configuration} (hpc : c.pc < source.length)
    (hactive : c.halted = false) (hseq : (source[c.pc]).IsSequential)
    (hstep : Step (Program.withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) target) :
    ∃ d, Step source c d ∧ target = d.rebasePc pre.length := by
  have hsource : next source c = some ((source[c.pc]).next c) := by
    simp [next, hactive, List.getElem?_eq_getElem hpc]
  have htarget : next (Program.withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) =
      some (rebaseStepResult pre.length ((source[c.pc]).next c)) := by
    rw [Program.next_withSubroutine_source pre source suffix returnPc
      c.pc (c.rebasePc pre.length) hpc
      (by simp [Configuration.rebasePc])
      (by simpa [Configuration.rebasePc] using hactive)]
    exact congrArg some ((source[c.pc]).next_asSubroutine_sequential
      pre.length returnPc source.length c hseq)
  unfold Step successors at hstep
  rw [htarget] at hstep
  cases hresult : (source[c.pc]).next c with
  | inl d =>
      simp [hresult, rebaseStepResult] at hstep
      exact ⟨d, by simp [Step, successors, hsource, hresult], hstep⟩
  | inr pair =>
      rcases pair with ⟨left, right⟩
      simp [hresult, rebaseStepResult] at hstep
      rcases hstep with hleft | hright
      · exact ⟨left, by simp [Step, successors, hsource, hresult], hleft⟩
      · exact ⟨right, by simp [Step, successors, hsource, hresult], hright⟩

private theorem control_step_source
    (pre source suffix : Program) (returnPc : Nat)
    {c d target : Configuration}
    (hsource : next source c = some (.inl d))
    (htarget : next (Program.withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) =
      some (.inl (d.relocatePc pre.length returnPc source.length)))
    (hdactive : d.halted = false)
    (hstep : Step (Program.withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) target)
    (hNoReturn : target.pc ≠ returnPc) :
    ∃ d, Step source c d ∧ d.halted = false ∧ d.pc ≤ source.length ∧
      target = d.rebasePc pre.length := by
  have hEq : target = d.relocatePc pre.length returnPc source.length := by
    simpa [Step, successors, htarget] using hstep
  have hdpc : d.pc < source.length := by
    by_contra hout
    have hReturn : target.pc = returnPc := by
      simp [hEq, Configuration.relocatePc, subroutineAddress, hout]
    exact hNoReturn hReturn
  refine ⟨d, by simp [Step, successors, hsource], hdactive,
    Nat.le_of_lt hdpc, ?_⟩
  simpa [Configuration.relocatePc, Configuration.rebasePc,
    subroutineAddress_inRange _ _ _ _ hdpc] using hEq

/-- Every embedded transition whose result has not returned is an actual
source transition. The source state remains active and lies inside its code
or at its one fall-through address. This covers both random-bit outcomes. -/
theorem Program.step_withSubroutine_before_return
    (pre source suffix : Program) (returnPc : Nat)
    {c target : Configuration} (hpcLe : c.pc ≤ source.length)
    (hactive : c.halted = false)
    (hstep : Step (Program.withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) target)
    (hNoReturn : target.pc ≠ returnPc) :
    ∃ d, Step source c d ∧ d.halted = false ∧ d.pc ≤ source.length ∧
      target = d.rebasePc pre.length := by
  by_cases hpc : c.pc < source.length
  · have hseqCase (hseq : (source[c.pc]).IsSequential) :
        ∃ d, Step source c d ∧ d.halted = false ∧ d.pc ≤ source.length ∧
          target = d.rebasePc pre.length := by
      obtain ⟨d, hSourceStep, hEq⟩ := sequential_step_source
        pre source suffix returnPc hpc hactive hseq hstep
      obtain ⟨hdpc, hdactive⟩ :=
        Program.step_sequential_control hpc hactive hseq hSourceStep
      exact ⟨d, hSourceStep, hdactive, by omega, hEq⟩
    have hWrapperNext := Program.next_withSubroutine_source pre source suffix
      returnPc c.pc (c.rebasePc pre.length) hpc
      (by simp [Configuration.rebasePc])
      (by simpa [Configuration.rebasePc] using hactive)
    cases hi : source[c.pc] with
    | halt =>
        have hEq : target = { c.rebasePc pre.length with pc := returnPc } := by
          simpa [Step, successors, hWrapperNext, hi,
            Instruction.asSubroutine, Instruction.next] using hstep
        exact False.elim (hNoReturn (by simp [hEq]))
    | jump address =>
        let d : Configuration := { c with pc := address }
        have hsource : next source c = some (.inl d) := by
          simp [next, hactive, List.getElem?_eq_getElem hpc,
            hi, Instruction.next, d]
        have htarget : next (Program.withSubroutine pre source suffix returnPc)
            (c.rebasePc pre.length) =
            some (.inl (d.relocatePc pre.length returnPc source.length)) := by
          rw [hWrapperNext]
          simp [hi, Instruction.next_asSubroutine_jump, d]
        exact control_step_source pre source suffix returnPc hsource htarget
          (by simp [d, hactive]) hstep hNoReturn
    | branch tape blankPc zeroPc onePc =>
        let d : Configuration := { c with pc :=
          match (c.tape tape).current with
          | none => blankPc
          | some false => zeroPc
          | some true => onePc }
        have hsource : next source c = some (.inl d) := by
          simp [next, hactive, List.getElem?_eq_getElem hpc,
            hi, Instruction.next, d]
          rfl
        have htarget : next (Program.withSubroutine pre source suffix returnPc)
            (c.rebasePc pre.length) =
            some (.inl (d.relocatePc pre.length returnPc source.length)) := by
          rw [hWrapperNext, hi, Instruction.next_asSubroutine_branch]
          rfl
        exact control_step_source pre source suffix returnPc hsource htarget
          (by simp [d, hactive]) hstep hNoReturn
    | moveLeft tape => exact hseqCase (by simp [hi, Instruction.IsSequential])
    | moveRight tape => exact hseqCase (by simp [hi, Instruction.IsSequential])
    | write tape bit => exact hseqCase (by simp [hi, Instruction.IsSequential])
    | erase tape => exact hseqCase (by simp [hi, Instruction.IsSequential])
    | randomBit tape => exact hseqCase (by simp [hi, Instruction.IsSequential])
  · have heq : c.pc = source.length := by omega
    have hnext := Program.next_withSubroutine_return pre source suffix returnPc
      (c.rebasePc pre.length) (by simp [Configuration.rebasePc, heq])
      (by simpa [Configuration.rebasePc] using hactive)
    have hEq : target = { c.rebasePc pre.length with pc := returnPc } := by
      simpa [Step, successors, hnext] using hstep
    exact False.elim (hNoReturn (by simp [hEq]))

/-- Embedded instructions remain active, including their return jumps. The
caller's own halt instruction is outside this invocation relation. -/
theorem Program.step_withSubroutine_active
    (pre source suffix : Program) (returnPc : Nat)
    {c target : Configuration} (hpcLe : c.pc ≤ source.length)
    (hactive : c.halted = false)
    (hstep : Step (Program.withSubroutine pre source suffix returnPc)
      (c.rebasePc pre.length) target) : target.halted = false := by
  by_cases hpc : c.pc < source.length
  · have hnext := Program.next_withSubroutine_source pre source suffix
      returnPc c.pc (c.rebasePc pre.length) hpc
      (by simp [Configuration.rebasePc])
      (by simpa [Configuration.rebasePc] using hactive)
    unfold Step successors at hstep
    rw [hnext] at hstep
    cases hi : source[c.pc] <;>
      simp [hi, Instruction.asSubroutine, Instruction.next] at hstep
    all_goals
      first
      | (subst target; simp [Configuration.rebasePc, Configuration.advance,
          Configuration.updateTape, hactive])
      | (rcases hstep with rfl | rfl <;>
          simp [Configuration.rebasePc, Configuration.advance,
            Configuration.updateTape, hactive])
    all_goals split <;> simp_all
  · have heq : c.pc = source.length := by omega
    have hnext := Program.next_withSubroutine_return pre source suffix returnPc
      (c.rebasePc pre.length) (by simp [Configuration.rebasePc, heq])
      (by simpa [Configuration.rebasePc] using hactive)
    have hEq : target = { c.rebasePc pre.length with pc := returnPc } := by
      simpa [Step, successors, hnext] using hstep
    simp [hEq, Configuration.rebasePc, hactive]

/-- A wrapper branch that has not returned corresponds to an active source
branch with the same number of actual transitions. Return padding cannot
occur on such a branch. -/
theorem ReturnRunsFor.source_of_not_returned
    (pre source suffix : Program) (returnPc : Nat)
    {start finish : Configuration} {steps : Nat}
    (run : ReturnRunsFor (Program.withSubroutine pre source suffix returnPc)
      returnPc (start.rebasePc pre.length) finish steps)
    (hpc : start.pc ≤ source.length) (hactive : start.halted = false)
    (hNoReturn : finish.pc ≠ returnPc) :
    ∃ d, RunsFor source start d steps ∧ d.halted = false ∧
      d.pc ≤ source.length ∧ finish = d.rebasePc pre.length := by
  induction steps generalizing finish with
  | zero =>
      cases run
      exact ⟨start, RunsFor.zero _, hactive, hpc, rfl⟩
  | succ steps ih =>
      cases run with
      | succ prior last =>
          rcases last with ⟨hMiddleNoReturn, hStep⟩ | ⟨hReturned, hEq⟩
          · obtain ⟨middle, hSourceRun, hmactive, hmpc, hMiddle⟩ :=
              ih prior hMiddleNoReturn
            rw [hMiddle] at hStep
            obtain ⟨d, hSourceStep, hdactive, hdpc, hFinish⟩ :=
              Program.step_withSubroutine_before_return pre source suffix
                returnPc hmpc hmactive hStep hNoReturn
            exact ⟨d, RunsFor.succ hSourceRun hSourceStep,
              hdactive, hdpc, hFinish⟩
          · subst finish
            exact False.elim (hNoReturn hReturned)

/-- Source invocations never halt the enclosing program: returning transfers
control to an active caller configuration. -/
theorem ReturnRunsFor.withSubroutine_active
    (pre source suffix : Program) (returnPc : Nat)
    {start finish : Configuration} {steps : Nat}
    (run : ReturnRunsFor (Program.withSubroutine pre source suffix returnPc)
      returnPc (start.rebasePc pre.length) finish steps)
    (hpc : start.pc ≤ source.length) (hactive : start.halted = false) :
    finish.halted = false := by
  induction steps generalizing finish with
  | zero => cases run; simpa [Configuration.rebasePc] using hactive
  | succ steps ih =>
      cases run with
      | succ prior last =>
          rcases last with ⟨hNoReturn, hStep⟩ | ⟨_, rfl⟩
          · obtain ⟨middle, _, hmactive, hmpc, hEq⟩ :=
              prior.source_of_not_returned pre source suffix returnPc
                hpc hactive hNoReturn
            rw [hEq] at hStep
            exact Program.step_withSubroutine_active pre source suffix
              returnPc hmpc hmactive hStep
          · exact ih prior

private theorem step_exists_active (p : Program) (c : Configuration)
    (hactive : c.halted = false) : ∃ d, Step p c d := by
  have hnext : ∃ result, next p c = some result := by
    simp [next, hactive]
  obtain ⟨result, hresult⟩ := hnext
  cases result with
  | inl d => exact ⟨d, by simp [Step, successors, hresult]⟩
  | inr pair => exact ⟨pair.1, by simp [Step, successors, hresult]⟩

/-- Invocation traces exist at every finite bound. An active embedded
configuration has an actual successor; after return only padding is needed.
Thus a universal return bound cannot hold merely because no traces exist. -/
theorem ReturnRunsFor.exists_withSubroutine
    (pre source suffix : Program) (returnPc steps : Nat)
    {start : Configuration} (hpc : start.pc ≤ source.length)
    (hactive : start.halted = false) :
    ∃ finish, ReturnRunsFor
      (Program.withSubroutine pre source suffix returnPc) returnPc
      (start.rebasePc pre.length) finish steps := by
  induction steps with
  | zero => exact ⟨_, ReturnRunsFor.zero _⟩
  | succ steps ih =>
      obtain ⟨middle, hrun⟩ := ih
      by_cases hReturn : middle.pc = returnPc
      · exact ⟨middle, ReturnRunsFor.succ hrun (Or.inr ⟨hReturn, rfl⟩)⟩
      · obtain ⟨d, _, hdactive, _, hmiddle⟩ := hrun.source_of_not_returned
          pre source suffix returnPc hpc hactive hReturn
        have hmactive : middle.halted = false := by
          simpa [hmiddle, Configuration.rebasePc] using hdactive
        obtain ⟨finish, hstep⟩ := step_exists_active _ middle hmactive
        exact ⟨finish, ReturnRunsFor.succ hrun (Or.inl ⟨hReturn, hstep⟩)⟩

/-- A worst-case standalone source step bound also bounds the time to return
on every random branch of its embedded invocation. The continuation itself
is not executed by `ReturnRunsFor`. No branch restriction or expectation is
used: a non-returned wrapper branch would give an active source branch at
the very bound where `HaltsWithin` requires every source branch to halt. -/
theorem HaltsWithin.withSubroutine_returnsWithin
    (pre source suffix : Program) (returnPc : Nat)
    {input : List Bool} {bound : Nat}
    (halts : HaltsWithin source input bound) :
    ReturnsWithin (Program.withSubroutine pre source suffix returnPc)
      ((Configuration.initial input).rebasePc pre.length) returnPc bound := by
  intro finish run
  by_contra hNoReturn
  obtain ⟨d, hSourceRun, hActive, _, _⟩ := run.source_of_not_returned
    pre source suffix returnPc (by simp [Configuration.initial]) rfl hNoReturn
  have hHalted := halts d hSourceRun.toPadded
  simp [hActive] at hHalted

/-- In addition to the all-branch bound, there is a returning execution using
at most the bound's number of actual machine transitions. No choice of
program or branch family is used. -/
theorem HaltsWithin.withSubroutine_return_actual
    (pre source suffix : Program) (returnPc : Nat)
    {input : List Bool} {bound : Nat}
    (halts : HaltsWithin source input bound) :
    ∃ finish used, used ≤ bound ∧
      RunsFor (Program.withSubroutine pre source suffix returnPc)
        ((Configuration.initial input).rebasePc pre.length) finish used ∧
      finish.pc = returnPc := by
  obtain ⟨finish, hrun⟩ := ReturnRunsFor.exists_withSubroutine
    pre source suffix returnPc bound (start := Configuration.initial input)
    (by simp [Configuration.initial]) rfl
  obtain ⟨used, hle, hactual⟩ := hrun.toRunsFor
  exact ⟨finish, used, hle, hactual,
    halts.withSubroutine_returnsWithin pre source suffix returnPc finish hrun⟩

/-- The first invocation of a two-copy wrapper has the source's worst-case
bound, provided the caller prepares the same initial tapes. -/
theorem HaltsWithin.withTwoSubroutines_first_returnsWithin
    (pre middle post source : Program) {input : List Bool} {bound : Nat}
    (halts : HaltsWithin source input bound) :
    ReturnsWithin (Program.withTwoSubroutines pre middle post source)
      ((Configuration.initial input).rebasePc pre.length)
      (pre.length + source.length + 1) bound := by
  rw [Program.withTwoSubroutines_first_layout]
  exact halts.withSubroutine_returnsWithin pre source _ _

/-- The second invocation has the same bound once its input/output tapes are
prepared afresh. This does not assert that intervening caller code performs
that preparation. -/
theorem HaltsWithin.withTwoSubroutines_second_returnsWithin
    (pre middle post source : Program) {input : List Bool} {bound : Nat}
    (halts : HaltsWithin source input bound) :
    ReturnsWithin (Program.withTwoSubroutines pre middle post source)
      ((Configuration.initial input).rebasePc
        (pre.length + source.length + 1 + middle.length))
      (pre.length + source.length + 1 + middle.length + source.length + 1)
      bound := by
  rw [Program.withTwoSubroutines_second_layout]
  simpa only [List.length_append, Program.asSubroutine_length,
    Nat.add_assoc] using halts.withSubroutine_returnsWithin
      (pre ++ source.asSubroutine pre.length
        (pre.length + source.length + 1) ++ middle) source post _

/-- Use the existing fair-bit probability semantics until the invocation
returns. Absorption at the continuation is bookkeeping, not a caller step. -/
noncomputable def returnStepPMF (p : Program) (returnPc : Nat)
    (c : Configuration) : PMF Configuration :=
  if c.pc = returnPc then PMF.pure c else stepPMF p c

theorem mem_support_returnStepPMF_iff (p : Program) (returnPc : Nat)
    (c d : Configuration) (hactive : c.halted = false) :
    d ∈ (returnStepPMF p returnPc c).support ↔ ReturnStep p returnPc c d := by
  by_cases hReturn : c.pc = returnPc
  · simp [returnStepPMF, ReturnStep, hReturn, eq_comm]
  · simp only [returnStepPMF, hReturn, ↓reduceIte]
    rw [mem_support_stepPMF_iff]
    simp [PaddedStep, ReturnStep, hactive, hReturn]

/-- A configuration distribution at a common invocation bound. Once control
has reached the continuation, no continuation instructions are evaluated. -/
noncomputable def evalReturnWithin (p : Program) (returnPc : Nat)
    (start : Configuration) : Nat → PMF Configuration
  | 0 => PMF.pure start
  | steps + 1 => (evalReturnWithin p returnPc start steps).bind
      (returnStepPMF p returnPc)

/-- Probability support coincides with all invocation traces, including both
outcomes of each fair random bit. The active-state invariant rules out a
spurious halted-state stutter before the return address. -/
theorem mem_support_evalReturnWithin_iff
    (pre source suffix : Program) (returnPc : Nat)
    {start : Configuration} (hpc : start.pc ≤ source.length)
    (hactive : start.halted = false) (finish : Configuration) (steps : Nat) :
    finish ∈ (evalReturnWithin
      (Program.withSubroutine pre source suffix returnPc) returnPc
      (start.rebasePc pre.length) steps).support ↔
    ReturnRunsFor (Program.withSubroutine pre source suffix returnPc)
      returnPc (start.rebasePc pre.length) finish steps := by
  induction steps generalizing finish with
  | zero =>
      constructor
      · intro h
        have hEq : finish = start.rebasePc pre.length := by
          simpa [evalReturnWithin] using h
        subst finish
        exact ReturnRunsFor.zero _
      · intro h
        cases h
        simp [evalReturnWithin]
  | succ steps ih =>
      rw [evalReturnWithin, PMF.mem_support_bind_iff]
      constructor
      · rintro ⟨middle, hMiddle, hFinish⟩
        have hPrior := (ih middle).mp hMiddle
        have hmactive := hPrior.withSubroutine_active pre source suffix
          returnPc hpc hactive
        exact ReturnRunsFor.succ hPrior
          ((mem_support_returnStepPMF_iff _ returnPc middle finish hmactive).mp
            hFinish)
      · intro h
        cases h with
        | succ prior last =>
            refine ⟨_, (ih _).mpr prior, ?_⟩
            have hmactive := prior.withSubroutine_active pre source suffix
              returnPc hpc hactive
            exact (mem_support_returnStepPMF_iff _ returnPc _ _ hmactive).mpr last

/-- The universal source stopping bound excludes non-returned configurations
from the embedded invocation distribution's support. -/
theorem HaltsWithin.withSubroutine_return_support
    (pre source suffix : Program) (returnPc : Nat)
    {input : List Bool} {bound : Nat}
    (halts : HaltsWithin source input bound) {finish : Configuration}
    (hSupport : finish ∈ (evalReturnWithin
      (Program.withSubroutine pre source suffix returnPc) returnPc
      ((Configuration.initial input).rebasePc pre.length) bound).support) :
    finish.pc = returnPc := by
  have hRun := (mem_support_evalReturnWithin_iff pre source suffix returnPc
    (by simp [Configuration.initial]) rfl finish bound).mp hSupport
  exact halts.withSubroutine_returnsWithin pre source suffix returnPc finish hRun

/-- If the continuation is a halt instruction, a still-active operational
trace cannot have passed it. Its steps therefore also form an invocation
trace. No probabilistic branch is discarded by this conversion. -/
theorem PaddedRunsFor.toReturnRunsFor_of_active
    {p : Program} {returnPc : Nat} {start finish : Configuration} {steps : Nat}
    (run : PaddedRunsFor p start finish steps)
    (hHalt : p[returnPc]? = some .halt) (hActive : finish.halted = false) :
    ReturnRunsFor p returnPc start finish steps := by
  induction run with
  | zero => exact ReturnRunsFor.zero _
  | @succ middle finish steps prior last ih =>
      rcases last with step | ⟨hStopped, rfl⟩
      · have hm : middle.halted = false := by
          cases hh : middle.halted with
          | false => rfl
          | true => exact False.elim ((no_step_of_halted hh) step)
        have hNotReturn : middle.pc ≠ returnPc := by
          intro hReturn
          have hInstr : p[middle.pc]? = some .halt := hReturn ▸ hHalt
          have hFinish : finish = { middle with halted := true } := by
            simpa [Step, successors, next, hm, hInstr, Instruction.next] using step
          rw [hFinish] at hActive
          cases hActive
        exact ReturnRunsFor.succ (ih hm) (Or.inl ⟨hNotReturn, step⟩)
      · simp [hStopped] at hActive

/-- An all-branch return bound followed by one actual halt instruction
gives an all-branch machine halting bound. The final `+1` is charged; return
padding is not reinterpreted as a machine transition. -/
theorem ReturnsWithin.all_branches_halted_after_halt
    {p : Program} {start : Configuration} {returnPc bound : Nat}
    (returns : ReturnsWithin p start returnPc bound)
    (hHalt : p[returnPc]? = some .halt) :
    ∀ finish, PaddedRunsFor p start finish (bound + 1) → finish.halted = true := by
  intro finish run
  cases run with
  | @succ middle _ _ prior last =>
      cases hm : middle.halted with
      | true =>
          rcases last with step | ⟨_, rfl⟩
          · exact False.elim ((no_step_of_halted hm) step)
          · exact hm
      | false =>
          have hReturn := returns middle (prior.toReturnRunsFor_of_active hHalt hm)
          have hInstr : p[middle.pc]? = some .halt := hReturn ▸ hHalt
          rcases last with step | ⟨hStopped, _⟩
          · have hFinish : finish = { middle with halted := true } := by
              simpa [Step, successors, next, hm, hInstr, Instruction.next] using step
            simp [hFinish]
          · simp [hm] at hStopped

end Machine
