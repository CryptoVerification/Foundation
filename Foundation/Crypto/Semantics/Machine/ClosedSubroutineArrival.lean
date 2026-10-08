import Foundation.Crypto.Semantics.Machine.ClosedSubroutineProbability
import Foundation.Crypto.Semantics.BoundaryInvariantSimulation

/-! Closed native invocation preserves the complete first-arrival state /
actual-cost law at every finite fuel. Halt becomes an active return at the
same step. No continuation step is charged inside the source component. -/
namespace Machine
open Foundation.Probability TimedExecution

def Program.subroutineState (base returnPc : Nat) (state : Configuration) : Configuration :=
  if state.halted then state.resumeAt returnPc else state.rebasePc base

theorem Program.stepPMF_subroutineState (pre source suffix : Program) (returnPc : Nat)
    (layout : ∀ pc, pc < source.length → pre.length + pc ≠ returnPc)
    (closed : ∀ start next, start.pc < source.length → Step source start next →
      next.halted = false → next.pc < source.length)
    (start : Configuration) (inside : start.pc < source.length) (active : start.halted = false) :
    stepPMF (withSubroutine pre source suffix returnPc) (start.rebasePc pre.length) =
      (stepPMF source start).map (subroutineState pre.length returnPc) := by
  change stepPMF (withSubroutine pre source suffix returnPc) (start.rebasePc pre.length) =
    (stepPMF source start).map (fun state => if state.halted then state.resumeAt returnPc else state.rebasePc pre.length)
  have h := Program.evalReturnWithin_configuration_eq_of_closed pre source suffix returnPc layout closed start inside active 1
  have noReturn : (start.rebasePc pre.length).pc ≠ returnPc := layout start.pc inside
  simpa only [evalReturnWithin, evalConfigWithin, PMF.pure_bind, returnStepPMF, noReturn, ↓reduceIte,
    subroutineState] using h

theorem Program.runToBoundary_subroutineState (pre source suffix : Program) (returnPc : Nat)
    (layout : ∀ pc, pc < source.length → pre.length + pc ≠ returnPc)
    (closed : ∀ start next, start.pc < source.length → Step source start next →
      next.halted = false → next.pc < source.length)
    (start : Configuration) (inside : start.pc < source.length) (active : start.halted = false) (fuel : Nat) :
    runToBoundary (stepPMF (withSubroutine pre source suffix returnPc)) (fun state => state.pc == returnPc)
      fuel (start.rebasePc pre.length) =
    (runToBoundary (stepPMF source) Configuration.halted fuel start).map
      (fun result => (subroutineState pre.length returnPc result.1, result.2)) := by
  have h := runToBoundary_map_on_invariant (stepPMF source)
    (stepPMF (withSubroutine pre source suffix returnPc)) Configuration.halted (fun state => state.pc == returnPc)
    (subroutineState pre.length returnPc) (fun state => state.halted = true ∨ state.pc < source.length)
    (by
      intro state hValid hActive next hNext
      have hInside : state.pc < source.length := hValid.resolve_left (by simp [hActive])
      have hStep : Step source state next := by
        rcases (mem_support_stepPMF_iff source state next).mp hNext with h | ⟨h, _⟩
        · exact h
        · simp [hActive] at h
      cases hHalt : next.halted with
      | true => exact Or.inl rfl
      | false => exact Or.inr (closed state next hInside hStep hHalt))
    (by
      intro state hValid
      cases hHalt : state.halted with
      | true => simp [subroutineState, hHalt, Configuration.resumeAt]
      | false =>
          have hInside : state.pc < source.length := hValid.resolve_left (by simp [hHalt])
          simp [subroutineState, hHalt, Configuration.rebasePc, layout state.pc hInside])
    (by
      intro state hValid hActive
      have hInside : state.pc < source.length := hValid.resolve_left (by simp [hActive])
      simpa only [subroutineState, hActive, Bool.false_eq_true, ↓reduceIte] using
        Program.stepPMF_subroutineState pre source suffix returnPc layout closed state hInside hActive)
    fuel start (Or.inr inside)
  simpa only [subroutineState, active, Bool.false_eq_true, ↓reduceIte] using h

end Machine
