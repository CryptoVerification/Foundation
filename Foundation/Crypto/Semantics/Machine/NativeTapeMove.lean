import Foundation.Crypto.Semantics.Machine.NativeFixedComponent

/-! Actual one-cell head movement followed by halt, as a native component.
This changes the full inherited configuration; no tape normalization occurs. -/
namespace Machine.NativeTapeMove
open Foundation.Probability

def code (which : TapeId) (left : Bool) : Program :=
  [if left then .moveLeft which else .moveRight which, .halt]

def finish (which : TapeId) (left : Bool) (machine : Configuration) : Configuration :=
  {(machine.updateTape which (if left then Tape.moveLeft else Tape.moveRight)).resumeAt 1 with halted := true}

theorem run (which : TapeId) (left : Bool) (machine : Configuration) :
    evalConfigWithin (code which left) (machine.resumeAt 0) 2 = PMF.pure (finish which left machine) := by
  cases which <;> cases left <;>
    simp [code, finish, evalConfigWithin, stepPMF, Machine.next, Instruction.next,
      Configuration.resumeAt, Configuration.updateTape, Configuration.advance, PMF.pure_bind]

noncomputable def component (which : TapeId) (left : Bool) : NativeComponent Configuration Configuration :=
  NativeComponent.ofFixed (code which left) (fun machine => machine.resumeAt 0)
    (fun _ output => output) (fun machine => PMF.pure (finish which left machine)) (fun _ => 2)
    (fun machine => by simpa only [PMF.pure_map] using run which left machine)
    (by cases which <;> cases left <;> decide)
    (fun _ => by change 0 < 2; decide) (fun _ => rfl)
    (by
      intro input output h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl)

end Machine.NativeTapeMove
