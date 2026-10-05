import Foundation.Machine.SubroutineProbability

namespace Machine

private def invocationState (base returnPc : Nat) (c : Configuration) : Configuration :=
  if c.halted then c.resumeAt returnPc else c.rebasePc base

private theorem eval_halted (p : Program) (c : Configuration) (steps : Nat)
    (h : c.halted = true) : evalConfigWithin p c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

/-- A closed source block has exactly the same full configuration law when
called as a native subroutine. Halting becomes return to the continuation;
active configurations retain their actual instruction offset. Unlike a
comparison of tape laws alone, this also identifies the probability of
returning by each finite budget. No every-branch stopping bound is required. -/
theorem Program.evalReturnWithin_configuration_eq_of_closed
    (pre source suffix : Program) (returnPc : Nat)
    (hLayout : ∀ pc, pc < source.length → pre.length + pc ≠ returnPc)
    (hClosed : ∀ c d, c.pc < source.length → Step source c d →
      d.halted = false → d.pc < source.length)
    (c : Configuration) (hpc : c.pc < source.length)
    (hactive : c.halted = false) (steps : Nat) :
    evalReturnWithin (withSubroutine pre source suffix returnPc) returnPc
      (c.rebasePc pre.length) steps =
      (evalConfigWithin source c steps).map
        (fun d => if d.halted then d.resumeAt returnPc else d.rebasePc pre.length) := by
  change _ = (evalConfigWithin source c steps).map (invocationState pre.length returnPc)
  induction steps generalizing c with
  | zero => simp [evalReturnWithin, evalConfigWithin, PMF.pure_map, invocationState, hactive]
  | succ steps ih =>
    have hNoReturn : (c.rebasePc pre.length).pc ≠ returnPc := hLayout c.pc hpc
    rw [evalReturnWithin_succ_head, evalConfigWithin_succ_head, PMF.map_bind]
    simp only [returnStepPMF, hNoReturn, ↓reduceIte]
    have hSequential (hi : (source[c.pc]).IsSequential) :
        (stepPMF (withSubroutine pre source suffix returnPc) (c.rebasePc pre.length)).bind
          (fun d => evalReturnWithin (withSubroutine pre source suffix returnPc) returnPc d steps) =
        (stepPMF source c).bind
          (fun d => (evalConfigWithin source d steps).map (invocationState pre.length returnPc)) := by
      rw [stepPMF_withSubroutine_sequential pre source suffix returnPc c hpc hactive hi,
        PMF.bind_map]
      rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext d hd
      have hStep : Step source c d := by
        rcases (mem_support_stepPMF_iff source c d).mp hd with h | ⟨h, _⟩
        · exact h
        · simp [hactive] at h
      have hNextActive := (step_sequential_control hpc hactive hi hStep).2
      exact ih d (hClosed c d hpc hStep hNextActive) hNextActive
    have hControl (d : Configuration) (hdactive : d.halted = false)
        (hSource : stepPMF source c = PMF.pure d)
        (hTarget : stepPMF (withSubroutine pre source suffix returnPc) (c.rebasePc pre.length) =
          PMF.pure (d.relocatePc pre.length returnPc source.length)) :
        (stepPMF (withSubroutine pre source suffix returnPc) (c.rebasePc pre.length)).bind
          (fun d => evalReturnWithin (withSubroutine pre source suffix returnPc) returnPc d steps) =
        (stepPMF source c).bind
          (fun d => (evalConfigWithin source d steps).map (invocationState pre.length returnPc)) := by
      have hStep : Step source c d := by
        have hd : d ∈ (stepPMF source c).support := by rw [hSource]; simp
        rcases (mem_support_stepPMF_iff source c d).mp hd with h | ⟨h, _⟩
        · exact h
        · simp [hactive] at h
      have hdpc := hClosed c d hpc hStep hdactive
      have hRelocate : d.relocatePc pre.length returnPc source.length = d.rebasePc pre.length := by
        simp [Configuration.relocatePc, Configuration.rebasePc, subroutineAddress, hdpc]
      rw [hSource, hTarget, PMF.pure_bind, PMF.pure_bind, hRelocate]
      exact ih d hdpc hdactive
    cases hi : source[c.pc] with
    | halt =>
      rw [stepPMF_withSubroutine_halt pre source suffix returnPc c hpc hactive hi]
      have hSource : stepPMF source c = PMF.pure {c with halted := true} := by
        simp [stepPMF, next, hactive, List.getElem?_eq_getElem hpc, hi, Instruction.next]
      rw [hSource, PMF.pure_map, PMF.pure_bind, PMF.pure_bind,
        evalReturnWithin_of_returned _ returnPc
          (({c with halted := true} : Configuration).resumeAt returnPc) steps rfl,
        eval_halted source _ steps rfl, PMF.pure_map]
      rfl
    | jump address =>
      let d : Configuration := {c with pc := address}
      have hSource : stepPMF source c = PMF.pure d := by
        simp [d, stepPMF, next, hactive, List.getElem?_eq_getElem hpc, hi, Instruction.next]
      apply hControl d (by simp [d, hactive]) hSource
      rw [stepPMF_withSubroutine_jump pre source suffix returnPc address c hpc hactive hi,
        hSource, PMF.pure_map]
    | branch tape blankPc zeroPc onePc =>
      let d : Configuration := {c with pc := match (c.tape tape).current with
        | none => blankPc | some false => zeroPc | some true => onePc}
      have hSource : stepPMF source c = PMF.pure d := by
        simp [d, stepPMF, next, hactive, List.getElem?_eq_getElem hpc, hi, Instruction.next]
        rfl
      apply hControl d (by simp [d, hactive]) hSource
      rw [stepPMF_withSubroutine_branch pre source suffix returnPc tape blankPc zeroPc onePc
        c hpc hactive hi, hSource, PMF.pure_map]
    | moveLeft tape => exact hSequential (by simp [hi, Instruction.IsSequential])
    | moveRight tape => exact hSequential (by simp [hi, Instruction.IsSequential])
    | write tape bit => exact hSequential (by simp [hi, Instruction.IsSequential])
    | erase tape => exact hSequential (by simp [hi, Instruction.IsSequential])
    | randomBit tape => exact hSequential (by simp [hi, Instruction.IsSequential])

end Machine
