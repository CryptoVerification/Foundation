import Foundation.Crypto.Semantics.Machine.SubroutineRuntime

namespace Machine

theorem evalConfigWithin_succ_head (p : Program) (c : Configuration)
    (steps : Nat) :
    evalConfigWithin p c (steps + 1) =
      (stepPMF p c).bind (fun d => evalConfigWithin p d steps) := by
  induction steps with
  | zero => simp [evalConfigWithin]
  | succ steps ih =>
      rw [evalConfigWithin, ih, PMF.bind_bind]
      rfl

theorem evalReturnWithin_succ_head (p : Program) (returnPc : Nat)
    (c : Configuration) (steps : Nat) :
    evalReturnWithin p returnPc c (steps + 1) =
      (returnStepPMF p returnPc c).bind
        (fun d => evalReturnWithin p returnPc d steps) := by
  induction steps with
  | zero => simp [evalReturnWithin]
  | succ steps ih =>
      rw [evalReturnWithin, ih, PMF.bind_bind]
      rfl

theorem evalReturnWithin_of_returned (p : Program) (returnPc : Nat)
    (c : Configuration) (steps : Nat) (hReturn : c.pc = returnPc) :
    evalReturnWithin p returnPc c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalReturnWithin, ih, returnStepPMF, hReturn]

private theorem evalConfigWithin_output_of_terminal (p : Program)
    (c : Configuration) (steps : Nat)
    (hTerminal : c.halted = true ∨ p.length ≤ c.pc) :
    (evalConfigWithin p c steps).map Configuration.outputBits =
      PMF.pure c.outputBits := by
  induction steps generalizing c with
  | zero => simp [evalConfigWithin, PMF.pure_map]
  | succ steps ih =>
      rw [evalConfigWithin_succ_head, PMF.map_bind]
      cases hHalted : c.halted with
      | true =>
          have hStep : stepPMF p c = PMF.pure c := by
            simp [stepPMF, next, hHalted]
          rw [hStep, PMF.pure_bind]
          exact ih c (Or.inl hHalted)
      | false =>
          have hOutside : p.length ≤ c.pc := by
            rcases hTerminal with h | h
            · simp [hHalted] at h
            · exact h
          have hStep : stepPMF p c =
              PMF.pure { c with halted := true } := by
            simp [stepPMF, next, hHalted, List.getElem?_eq_none hOutside]
          rw [hStep, PMF.pure_bind]
          exact ih _ (Or.inl rfl)

private theorem evalConfigWithin_tapes_of_terminal (p : Program)
    (c : Configuration) (steps : Nat)
    (hTerminal : c.halted = true ∨ p.length ≤ c.pc) :
    (evalConfigWithin p c steps).map (fun c => (c.inputTape, c.outputTape)) =
      PMF.pure (c.inputTape, c.outputTape) := by
  induction steps generalizing c with
  | zero => simp [evalConfigWithin, PMF.pure_map]
  | succ steps ih =>
      rw [evalConfigWithin_succ_head, PMF.map_bind]
      cases hHalted : c.halted with
      | true =>
          have hStep : stepPMF p c = PMF.pure c := by
            simp [stepPMF, next, hHalted]
          rw [hStep, PMF.pure_bind]
          exact ih c (Or.inl hHalted)
      | false =>
          have hOutside : p.length ≤ c.pc := by
            rcases hTerminal with h | h
            · simp [hHalted] at h
            · exact h
          have hStep : stepPMF p c =
              PMF.pure { c with halted := true } := by
            simp [stepPMF, next, hHalted, List.getElem?_eq_none hOutside]
          rw [hStep, PMF.pure_bind]
          exact ih _ (Or.inl rfl)

/-- An invocation must stop outside the embedded instruction block, including
its appended return jump. Otherwise a source instruction may be mistaken for
the caller continuation. No restriction is imposed on source jump addresses:
out-of-range jumps may return one transition earlier, without changing either tape. Both outcomes and probabilities of every fair random bit are retained.
Both tape layouts are retained, including their head positions. This theorem
concerns the invocation alone, not caller tape preparation. -/
theorem Program.evalReturnWithin_tapes_eq
    (pre source suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ source.length → pre.length + pc ≠ returnPc)
    (c : Configuration) (hpc : c.pc ≤ source.length)
    (hactive : c.halted = false) (steps : Nat) :
    (evalReturnWithin (withSubroutine pre source suffix returnPc) returnPc
      (c.rebasePc pre.length) steps).map (fun c => (c.inputTape, c.outputTape)) =
      (evalConfigWithin source c steps).map (fun c => (c.inputTape, c.outputTape)) := by
  induction steps generalizing c with
  | zero => simp [evalReturnWithin, evalConfigWithin, PMF.pure_map, Configuration.rebasePc]
  | succ steps ih =>
      have hNoReturn : (c.rebasePc pre.length).pc ≠ returnPc := hLayout c.pc hpc
      rw [evalReturnWithin_succ_head, evalConfigWithin_succ_head,
        PMF.map_bind, PMF.map_bind]
      simp only [returnStepPMF, hNoReturn, ↓reduceIte]
      by_cases hInside : c.pc < source.length
      · have hSequential (hi : (source[c.pc]).IsSequential) :
            ((stepPMF (withSubroutine pre source suffix returnPc)
                (c.rebasePc pre.length)).bind fun d =>
                  (evalReturnWithin (withSubroutine pre source suffix returnPc)
                    returnPc d steps).map (fun c => (c.inputTape, c.outputTape))) =
              (stepPMF source c).bind (fun d =>
                (evalConfigWithin source d steps).map (fun c => (c.inputTape, c.outputTape))) := by
          rw [stepPMF_withSubroutine_sequential pre source suffix returnPc
            c hInside hactive hi, PMF.bind_map]
          rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
          congr 1
          funext d hd
          have hStep : Step source c d := by
            rcases (mem_support_stepPMF_iff source c d).mp hd with h | ⟨h, _⟩
            · exact h
            · simp [hactive] at h
          obtain ⟨hNextPc, hNextActive⟩ :=
            step_sequential_control hInside hactive hi hStep
          exact ih d (by omega) hNextActive
        have hControl (d : Configuration) (hdactive : d.halted = false)
            (hSource : stepPMF source c = PMF.pure d)
            (hTarget : stepPMF (withSubroutine pre source suffix returnPc)
              (c.rebasePc pre.length) =
                PMF.pure (d.relocatePc pre.length returnPc source.length)) :
            ((stepPMF (withSubroutine pre source suffix returnPc)
                (c.rebasePc pre.length)).bind fun d =>
                  (evalReturnWithin (withSubroutine pre source suffix returnPc)
                    returnPc d steps).map (fun c => (c.inputTape, c.outputTape))) =
              (stepPMF source c).bind (fun d =>
                (evalConfigWithin source d steps).map (fun c => (c.inputTape, c.outputTape))) := by
          rw [hSource, hTarget, PMF.pure_bind, PMF.pure_bind]
          by_cases hdpc : d.pc < source.length
          · have hRelocate : d.relocatePc pre.length returnPc source.length =
                d.rebasePc pre.length := by
              simp [Configuration.relocatePc, Configuration.rebasePc,
                subroutineAddress, hdpc]
            rw [hRelocate]
            exact ih d (Nat.le_of_lt hdpc) hdactive
          · have hRelocate : d.relocatePc pre.length returnPc source.length =
                d.resumeAt returnPc := by
              simp [Configuration.relocatePc, Configuration.resumeAt,
                subroutineAddress, hdpc, hdactive]
            rw [hRelocate, evalReturnWithin_of_returned _ returnPc
                (d.resumeAt returnPc) steps rfl,
              PMF.pure_map, evalConfigWithin_tapes_of_terminal source d steps
                (Or.inr (by omega))]
            rfl
        cases hi : source[c.pc] with
        | halt =>
            rw [stepPMF_withSubroutine_halt pre source suffix returnPc
              c hInside hactive hi]
            have hSource : stepPMF source c =
                PMF.pure { c with halted := true } := by
              simp [stepPMF, next, hactive, List.getElem?_eq_getElem hInside,
                hi, Instruction.next]
            rw [hSource, PMF.pure_map, PMF.pure_bind, PMF.pure_bind,
              evalReturnWithin_of_returned _ returnPc
                (({ c with halted := true } : Configuration).resumeAt returnPc)
                steps rfl, PMF.pure_map,
              evalConfigWithin_tapes_of_terminal source _ steps (Or.inl rfl)]
            rfl
        | jump address =>
            let d : Configuration := { c with pc := address }
            have hSource : stepPMF source c = PMF.pure d := by
              simp [d, stepPMF, next, hactive, List.getElem?_eq_getElem hInside,
                hi, Instruction.next]
            apply hControl d (by simp [d, hactive]) hSource
            rw [stepPMF_withSubroutine_jump pre source suffix returnPc address
              c hInside hactive hi, hSource, PMF.pure_map]
        | branch tape blankPc zeroPc onePc =>
            let d : Configuration := { c with pc :=
              match (c.tape tape).current with
              | none => blankPc
              | some false => zeroPc
              | some true => onePc }
            have hSource : stepPMF source c = PMF.pure d := by
              simp [d, stepPMF, next, hactive, List.getElem?_eq_getElem hInside,
                hi, Instruction.next]
              rfl
            apply hControl d (by simp [d, hactive]) hSource
            rw [stepPMF_withSubroutine_branch pre source suffix returnPc tape
              blankPc zeroPc onePc c hInside hactive hi, hSource, PMF.pure_map]
        | moveLeft tape => exact hSequential (by simp [hi, Instruction.IsSequential])
        | moveRight tape => exact hSequential (by simp [hi, Instruction.IsSequential])
        | write tape bit => exact hSequential (by simp [hi, Instruction.IsSequential])
        | erase tape => exact hSequential (by simp [hi, Instruction.IsSequential])
        | randomBit tape => exact hSequential (by simp [hi, Instruction.IsSequential])
      · have hEnd : c.pc = source.length := by omega
        rw [stepPMF_withSubroutine_fallthrough pre source suffix returnPc
          c hEnd hactive]
        have hSource : stepPMF source c =
            PMF.pure { c with halted := true } := by
          simp [stepPMF, next, hactive, hEnd]
        rw [hSource, PMF.pure_map, PMF.pure_bind, PMF.pure_bind,
          evalReturnWithin_of_returned _ returnPc
            (({ c with halted := true } : Configuration).resumeAt returnPc)
            steps rfl, PMF.pure_map,
          evalConfigWithin_tapes_of_terminal source _ steps (Or.inl rfl)]
        rfl

/-- The existing output law follows by observing the output tape in the
full two-tape invocation law. No tape decoding or copying is performed here. -/
theorem Program.evalReturnWithin_output_eq
    (pre source suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ source.length → pre.length + pc ≠ returnPc)
    (c : Configuration) (hpc : c.pc ≤ source.length)
    (hactive : c.halted = false) (steps : Nat) :
    (evalReturnWithin (withSubroutine pre source suffix returnPc) returnPc
      (c.rebasePc pre.length) steps).map Configuration.outputBits =
      (evalConfigWithin source c steps).map Configuration.outputBits := by
  have h := congrArg (fun distribution : PMF (Tape × Tape) =>
      distribution.map (fun tapes => tapes.2.bits))
    (evalReturnWithin_tapes_eq pre source suffix returnPc hLayout c hpc hactive steps)
  change (evalReturnWithin (withSubroutine pre source suffix returnPc) returnPc
    (c.rebasePc pre.length) steps).map (fun c => c.outputTape.bits) =
      (evalConfigWithin source c steps).map (fun c => c.outputTape.bits)
  simpa only [PMF.map_comp, Function.comp_def] using h

private theorem map_eq_on_support {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  change (p.bind fun a => PMF.pure (f a)) =
    (p.bind fun a => PMF.pure (g a))
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext a ha
  rw [h a ha]

/-- At an all-branch source stopping bound, the invocation distribution
retains both complete tapes and resumes at the active caller continuation.
Stopping at that address is bookkeeping only; this theorem does not execute
the continuation or give it a free time budget. -/
theorem Program.evalReturnWithin_configuration_eq_of_halted
    (pre source suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ source.length → pre.length + pc ≠ returnPc)
    (start : Configuration) (hpc : start.pc ≤ source.length)
    (hactive : start.halted = false) (steps : Nat)
    (halts : ∀ finish, PaddedRunsFor source start finish steps → finish.halted = true) :
    evalReturnWithin (withSubroutine pre source suffix returnPc) returnPc
      (start.rebasePc pre.length) steps =
      (evalConfigWithin source start steps).map (fun c => c.resumeAt returnPc) := by
  let invocation := evalReturnWithin (withSubroutine pre source suffix returnPc) returnPc
    (start.rebasePc pre.length) steps
  have hReturns : ReturnsWithin (withSubroutine pre source suffix returnPc)
      (start.rebasePc pre.length) returnPc steps := by
    intro finish run
    by_contra hNotReturned
    obtain ⟨d, hRun, hdActive, _, _⟩ := run.source_of_not_returned
      pre source suffix returnPc hpc hactive hNotReturned
    have hdHalted := halts d hRun.toPadded
    simp [hdActive] at hdHalted
  have hNormalize : invocation.map (fun c => c.resumeAt returnPc) = invocation := by
    have h := map_eq_on_support invocation (fun c => c.resumeAt returnPc) id (by
      intro c hc
      have hRun := (mem_support_evalReturnWithin_iff pre source suffix returnPc
        hpc hactive c steps).mp hc
      have hcPc := hReturns c hRun
      have hcActive := hRun.withSubroutine_active pre source suffix returnPc hpc hactive
      cases c
      simp_all [Configuration.resumeAt])
    simpa only [PMF.map_id] using h
  have hTapes := evalReturnWithin_tapes_eq pre source suffix returnPc
    hLayout start hpc hactive steps
  have hFull := congrArg (fun distribution : PMF (Tape × Tape) =>
      distribution.map (fun tapes => ({
        pc := returnPc
        inputTape := tapes.1
        outputTape := tapes.2 } : Configuration))) hTapes
  have hResume : invocation.map (fun c => c.resumeAt returnPc) =
      (evalConfigWithin source start steps).map (fun c => c.resumeAt returnPc) := by
    simpa only [PMF.map_comp, Function.comp_def, Configuration.resumeAt] using hFull
  rw [hNormalize] at hResume
  exact hResume

/-- At the source's all-branch stopping bound the invocation's decoded output
distribution, including its timeout convention, equals the standalone source
distribution. The return test excludes the caller continuation from execution.
Fresh initial tapes and a disjoint return address are explicit hypotheses. -/
theorem HaltsWithin.withSubroutine_evalReturn
    (pre source suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc ≤ source.length → pre.length + pc ≠ returnPc)
    {input : List Bool} {bound : Nat} (halts : HaltsWithin source input bound) :
    (evalReturnWithin (Program.withSubroutine pre source suffix returnPc)
      returnPc ((Configuration.initial input).rebasePc pre.length) bound).map
        (fun c => if c.pc = returnPc then some c.outputBits else none) =
      evalWithin source input bound := by
  let invocation := evalReturnWithin
    (Program.withSubroutine pre source suffix returnPc) returnPc
    ((Configuration.initial input).rebasePc pre.length) bound
  have hReturned : invocation.map
      (fun c => if c.pc = returnPc then some c.outputBits else none) =
        invocation.map (fun c => some c.outputBits) := by
    apply map_eq_on_support
    intro c hc
    rw [halts.withSubroutine_return_support pre source suffix returnPc hc]
    simp
  have hHalted : evalWithin source input bound =
      (evalConfigWithin source (Configuration.initial input) bound).map
        (fun c => some c.outputBits) := by
    apply map_eq_on_support
    intro c hc
    have h := halts c ((mem_support_evalConfigWithin_iff source _ c bound).mp hc)
    simp [h]
  rw [hReturned, hHalted]
  have hOutput := Program.evalReturnWithin_output_eq pre source suffix returnPc
    hLayout (Configuration.initial input) (by simp [Configuration.initial]) rfl bound
  have hSome := congrArg (fun p : PMF (List Bool) => p.map some) hOutput
  simpa only [PMF.map_comp, Function.comp_def] using hSome

/-- The first copied invocation has the standalone source distribution when
the caller has prepared its fresh input and blank output tapes. -/
theorem HaltsWithin.withTwoSubroutines_first_evalReturn
    (pre middle post source : Program) {input : List Bool} {bound : Nat}
    (halts : HaltsWithin source input bound) :
    (evalReturnWithin (Program.withTwoSubroutines pre middle post source)
      (pre.length + source.length + 1)
      ((Configuration.initial input).rebasePc pre.length) bound).map
        (fun c => if c.pc = pre.length + source.length + 1
          then some c.outputBits else none) = evalWithin source input bound := by
  rw [Program.withTwoSubroutines_first_layout]
  exact halts.withSubroutine_evalReturn pre source _ _ (by intro pc hpc; omega)

/-- The second copied invocation has the same standalone distribution under
its own fresh-input hypothesis. This theorem does not assert that caller code
resets dirty tapes or preserves the first call's state. -/
theorem HaltsWithin.withTwoSubroutines_second_evalReturn
    (pre middle post source : Program) {input : List Bool} {bound : Nat}
    (halts : HaltsWithin source input bound) :
    (evalReturnWithin (Program.withTwoSubroutines pre middle post source)
      (pre.length + source.length + 1 + middle.length + source.length + 1)
      ((Configuration.initial input).rebasePc
        (pre.length + source.length + 1 + middle.length)) bound).map
        (fun c => if c.pc =
            pre.length + source.length + 1 + middle.length + source.length + 1
          then some c.outputBits else none) = evalWithin source input bound := by
  rw [Program.withTwoSubroutines_second_layout]
  simpa only [List.length_append, Program.asSubroutine_length, Nat.add_assoc] using
    halts.withSubroutine_evalReturn
      (pre ++ source.asSubroutine pre.length
        (pre.length + source.length + 1) ++ middle) source post _
      (by intro pc hpc; simp only [List.length_append,
        Program.asSubroutine_length]; omega)

/-- If the caller continuation is a halt instruction, actually executing
that halt preserves the invocation's output distribution. Absorption in
`evalReturnWithin` is only bookkeeping, while the ordinary evaluator still
charges the halt transition. This equality also covers every random branch. -/
theorem Program.evalConfigWithin_output_eq_evalReturnWithin_of_halt
    (p : Program) (returnPc : Nat) (hHalt : p[returnPc]? = some .halt)
    (c : Configuration) (steps : Nat) :
    (evalConfigWithin p c steps).map Configuration.outputBits =
      (evalReturnWithin p returnPc c steps).map Configuration.outputBits := by
  induction steps generalizing c with
  | zero => rfl
  | succ steps ih =>
      by_cases hReturn : c.pc = returnPc
      · rw [evalReturnWithin_of_returned p returnPc c _ hReturn, PMF.pure_map]
        cases hStopped : c.halted with
        | true => exact evalConfigWithin_output_of_terminal p c _ (Or.inl hStopped)
        | false =>
            have hInstr : p[c.pc]? = some .halt := hReturn ▸ hHalt
            rw [evalConfigWithin_succ_head, PMF.map_bind]
            simp only [stepPMF, next, hStopped, Bool.false_eq_true, ↓reduceIte,
              hInstr, Instruction.next, PMF.pure_bind]
            exact evalConfigWithin_output_of_terminal p _ steps (Or.inl rfl)
      · rw [evalConfigWithin_succ_head, evalReturnWithin_succ_head,
          PMF.map_bind, PMF.map_bind]
        simp only [returnStepPMF, hReturn, ↓reduceIte]
        congr 1
        funext d
        exact ih d

/-- Reaching the continuation early does not create free steps: ordinary
evaluation executes it immediately. If its observation has stabilized after
`tail`, ordinary execution for `steps + tail` has the same law as stopping the
invocation at the return address and then executing the charged continuation
for `tail`. The stability hypothesis covers each possible returned state. -/
theorem evalConfigWithin_after_return {α : Type*}
    (p : Program) (returnPc : Nat) (start : Configuration) (steps tail : Nat)
    (observe : Configuration → α)
    (stable : ∀ d ∈ (evalReturnWithin p returnPc start steps).support,
      d.pc = returnPc → ∀ extra,
        (evalConfigWithin p d (tail + extra)).map observe =
          (evalConfigWithin p d tail).map observe) :
    (evalConfigWithin p start (steps + tail)).map observe =
      (evalReturnWithin p returnPc start steps).bind
        (fun d => (evalConfigWithin p d tail).map observe) := by
  induction steps generalizing start with
  | zero => simp [evalReturnWithin]
  | succ steps ih =>
      by_cases hReturn : start.pc = returnPc
      · rw [evalReturnWithin_of_returned p returnPc start _ hReturn, PMF.pure_bind]
        have hMember : start ∈ (evalReturnWithin p returnPc start (steps + 1)).support := by
          rw [evalReturnWithin_of_returned p returnPc start _ hReturn]
          simp
        simpa only [Nat.add_comm] using stable start hMember hReturn (steps + 1)
      · rw [show steps + 1 + tail = (steps + tail) + 1 by omega,
          evalConfigWithin_succ_head, PMF.map_bind, evalReturnWithin_succ_head,
          returnStepPMF, if_neg hReturn, PMF.bind_bind]
        rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
        congr 1
        funext d hd
        apply ih d
        intro finish hFinish hPc extra
        apply stable finish ?_ hPc extra
        rw [evalReturnWithin_succ_head, returnStepPMF, if_neg hReturn,
          PMF.mem_support_bind_iff]
        exact ⟨d, hd, hFinish⟩

/-- Ordinary execution of an embedded call followed by one explicit caller
halt. The source stopping transition becomes a return jump; the additional
halt is charged, including on branches which return earlier than the common
source bound. Complete tape configurations are preserved in the PMF. -/
theorem Program.evalConfigWithin_withSubroutine_final_halt
    (pre source : Program) (start : Configuration) (hpc : start.pc ≤ source.length)
    (hactive : start.halted = false) (steps : Nat)
    (halts : ∀ finish, PaddedRunsFor source start finish steps → finish.halted = true) :
    let returnPc := pre.length + source.length + 1
    evalConfigWithin (withSubroutine pre source [.halt] returnPc)
      (start.rebasePc pre.length) (steps + 1) =
      (evalConfigWithin source start steps).map
        (fun c => { c with pc := returnPc, halted := true }) := by
  dsimp only
  let returnPc := pre.length + source.length + 1
  let caller := withSubroutine pre source [.halt] returnPc
  have hLayout : ∀ pc, pc ≤ source.length → pre.length + pc ≠ returnPc := by
    intro pc h
    dsimp [returnPc]
    omega
  have hReturn := evalReturnWithin_configuration_eq_of_halted pre source [.halt]
    returnPc hLayout start hpc hactive steps halts
  have hInstruction : caller[returnPc]? = some .halt := by
    have h := withSubroutine_getElem?_suffix pre source [.halt] returnPc 0
    simpa only [Nat.add_zero, List.getElem?_cons_zero] using h
  have hHalted (c : Configuration) (hc : c.halted = true) (extra : Nat) :
      evalConfigWithin caller c extra = PMF.pure c := by
    induction extra with
    | zero => rfl
    | succ extra ih => simp [evalConfigWithin, ih, stepPMF, next, hc]
  have hTail (d : Configuration) (hd : d.pc = returnPc) (extra : Nat) :
      evalConfigWithin caller d (1 + extra) = PMF.pure { d with halted := true } := by
    have hSingle : evalConfigWithin caller d 1 = PMF.pure { d with halted := true } := by
      cases d with
      | mk pc input output active =>
          cases active <;>
            simp_all [evalConfigWithin, stepPMF, next, Instruction.next]
    rw [evalConfigWithin_add, hSingle, PMF.pure_bind]
    exact hHalted _ rfl extra
  have hAfter := evalConfigWithin_after_return caller returnPc (start.rebasePc pre.length)
    steps 1 id (by
      intro d _hd hPc extra
      rw [hTail d hPc extra, hTail d hPc 0])
  simp only [PMF.map_id] at hAfter
  rw [hAfter, hReturn, PMF.bind_map]
  change (evalConfigWithin source start steps).bind _ = _
  simp only [Function.comp_def]
  have hTailReturned (c : Configuration) := hTail (c.resumeAt returnPc) rfl 0
  simp_rw [hTailReturned]
  simp only [Configuration.resumeAt]
  rfl

/-- Complete configuration law for ordinary two-stage execution. The actual
caller changes only the final control address/halt flag relative to the
second subroutine's result. Both physical tapes and all their retained cells
are available to subsequent layout and storage proofs. Early return is
handled by return semantics, rather than resetting at the first budget. -/
theorem Program.evalConfigWithin_twoStages_configuration (first second : Program)
    (start : Configuration) (hPc : start.pc = 0) (hActive : start.halted = false)
    (t₁ t₂ : Nat)
    (hFirst : ∀ c, PaddedRunsFor first start c t₁ → c.halted = true)
    (hSecond : ∀ c ∈ (evalConfigWithin first start t₁).support,
      ∀ d, PaddedRunsFor second (c.resumeAt 0) d t₂ → d.halted = true) :
    let returnPc := first.length + 1
    let pre := first.asSubroutine 0 returnPc
    let finalPc := pre.length + second.length + 1
    let caller := Program.withSubroutine pre second [.halt] finalPc
    evalConfigWithin caller start (t₁ + (t₂ + 1)) =
      (evalConfigWithin first start t₁).bind
        (fun c => (evalConfigWithin second (c.resumeAt 0) t₂).map
          (fun d => { d with pc := finalPc, halted := true })) := by
  dsimp only
  let returnPc := first.length + 1
  let pre := first.asSubroutine 0 returnPc
  let finalPc := pre.length + second.length + 1
  let caller := Program.withSubroutine pre second [.halt] finalPc
  have hPre : pre.length = returnPc := Program.asSubroutine_length _ _ _
  have hProgram : Program.withSubroutine [] first
      (second.asSubroutine returnPc finalPc ++ [.halt]) returnPc = caller := by
    simp only [caller, Program.withSubroutine, List.length_nil, List.nil_append,
      pre, hPre, List.append_assoc]
  have hStart : start.rebasePc 0 = start := by
    cases start
    simp [Configuration.rebasePc]
  have hReturn := Program.evalReturnWithin_configuration_eq_of_halted [] first
    (second.asSubroutine returnPc finalPc ++ [.halt]) returnPc
    (by intro pc hpc; simp only [List.length_nil, Nat.zero_add]; dsimp [returnPc]; omega)
    start (by omega) hActive t₁ hFirst
  simp only [List.length_nil, hStart] at hReturn
  rw [hProgram] at hReturn
  have hTail (c : Configuration) (hc : c ∈ (evalConfigWithin first start t₁).support) :
      evalConfigWithin caller (c.resumeAt returnPc) (t₂ + 1) =
        (evalConfigWithin second (c.resumeAt 0) t₂).map
          (fun d => { d with pc := finalPc, halted := true }) := by
    have h := Program.evalConfigWithin_withSubroutine_final_halt pre second
      (c.resumeAt 0) (by change 0 ≤ second.length; omega) rfl t₂ (hSecond c hc)
    dsimp only at h
    have hEntry : (c.resumeAt 0).rebasePc pre.length = c.resumeAt returnPc := by
      simp [Configuration.resumeAt, Configuration.rebasePc, hPre]
    simpa only [hEntry] using h
  have stable (d : Configuration)
      (hd : d ∈ (evalReturnWithin caller returnPc start t₁).support)
      (_hpc : d.pc = returnPc) (extra : Nat) :
      evalConfigWithin caller d (t₂ + 1 + extra) =
        evalConfigWithin caller d (t₂ + 1) := by
    rw [hReturn, PMF.mem_support_map_iff] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    rw [evalConfigWithin_add, hTail c hc, PMF.bind_map]
    change (evalConfigWithin second (c.resumeAt 0) t₂).bind _ = _
    have hHalted (e : Configuration) :
        evalConfigWithin caller { e with pc := finalPc, halted := true } extra =
          PMF.pure { e with pc := finalPc, halted := true } := by
      induction extra with
      | zero => rfl
      | succ remaining ih => simp [evalConfigWithin, stepPMF, next, ih]
    simp only [Function.comp_def]
    simp_rw [hHalted]
    rfl
  have hAfter := evalConfigWithin_after_return caller returnPc start t₁ (t₂ + 1) id (by
    intro d hd hpc extra
    simpa only [PMF.map_id] using stable d hd hpc extra)
  simp only [PMF.map_id] at hAfter
  rw [hAfter, hReturn, PMF.bind_map]
  simp only [Function.comp_def]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext c hc
  exact hTail c hc

/-- Ordinary-execution composition of two finite native subroutines. Early return may execute
the continuation before the common first-stage bound; actual halting of the
second stage makes the remaining padded steps harmless. -/
theorem Program.evalConfigWithin_twoStages (first second : Program) (start : Configuration)
    (hPc : start.pc = 0) (hActive : start.halted = false) (t₁ t₂ : Nat)
    (hFirst : ∀ c, PaddedRunsFor first start c t₁ → c.halted = true)
    (hSecond : ∀ c ∈ (evalConfigWithin first start t₁).support,
      ∀ d, PaddedRunsFor second (c.resumeAt 0) d t₂ → d.halted = true) :
    let returnPc := first.length + 1
    let pre := first.asSubroutine 0 returnPc
    let caller := Program.withSubroutine pre second [.halt]
      (pre.length + second.length + 1)
    (evalConfigWithin caller start (t₁ + (t₂ + 1))).map
      (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin first start t₁).bind
        (fun c => (evalConfigWithin second (c.resumeAt 0) t₂).map
          (fun d => (d.halted, d.outputBits))) := by
  dsimp only
  have h := Program.evalConfigWithin_twoStages_configuration first second start
    hPc hActive t₁ t₂ hFirst hSecond
  dsimp only at h
  rw [h, PMF.map_bind]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext c hc
  rw [PMF.map_comp]
  change (evalConfigWithin second (c.resumeAt 0) t₂).bind _ =
    (evalConfigWithin second (c.resumeAt 0) t₂).bind _
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext d hd
  have hHalt := hSecond c hc d ((mem_support_evalConfigWithin_iff _ _ _ _).mp hd)
  simp [Function.comp_def, Configuration.outputBits, hHalt]

/-- Specialize native two-stage execution to a deterministic first result.
The returned physical tapes become the continuation's input; the extra
caller halt is still charged. -/
theorem Program.evalConfigWithin_twoStages_of_pure (first second : Program)
    (start finish : Configuration) (hPc : start.pc = 0) (hActive : start.halted = false)
    (t₁ t₂ : Nat) (hEval : evalConfigWithin first start t₁ = PMF.pure finish)
    (hFinish : finish.halted = true)
    (hSecond : ∀ d, PaddedRunsFor second (finish.resumeAt 0) d t₂ → d.halted = true) :
    let pre := first.asSubroutine 0 (first.length + 1)
    (evalConfigWithin (Program.withSubroutine pre second [.halt]
      (pre.length + second.length + 1)) start (t₁ + (t₂ + 1))).map
        (fun c => (c.halted, c.outputBits)) =
      (evalConfigWithin second (finish.resumeAt 0) t₂).map
        (fun c => (c.halted, c.outputBits)) := by
  have hFirst : ∀ c, PaddedRunsFor first start c t₁ → c.halted = true := by
    intro c run
    have hc := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
    rw [hEval, PMF.mem_support_pure_iff] at hc
    subst c
    exact hFinish
  have h := Program.evalConfigWithin_twoStages first second start hPc hActive t₁ t₂ hFirst (by
    intro c hc
    rw [hEval, PMF.mem_support_pure_iff] at hc
    subst c
    exact hSecond)
  simpa only [hEval, PMF.pure_bind] using h

end Machine
