import Foundation.Machine.ChoosePowerReset

namespace Machine.ChoosePowerDispatch

/-- Read the real power status immediately left of the input head, restore
that head, and jump to one of two caller continuations. Neither scratch nor
the saved request is erased here; both branches can invoke the same reset.
The targets are absolute addresses in the caller containing this dispatch. -/
def dispatch (acceptPc rejectPc : Nat) : Program :=
  [.moveLeft .input, .branch .input 4 4 2,
   .moveRight .input, .jump acceptPc,
   .moveRight .input, .jump rejectPc]

/-- Four actual transitions inspect the status and preserve both physical
tapes exactly. A continuation may contain arbitrary instructions: none of
those continuation instructions is executed within this trace. -/
theorem eval_dispatch (acceptPc rejectPc : Nat) (suffix : Program)
    (saved right : List (Option Bool)) (current : Option Bool)
    (output : Tape) (status : Bool) :
    let start : Configuration :=
      { inputTape := { left := some status :: saved, current := current, right := right }, outputTape := output }
    evalConfigWithin (dispatch acceptPc rejectPc ++ suffix) start 4 =
      PMF.pure (start.resumeAt (if status then acceptPc else rejectPc)) := by
  cases status <;>
    simp [evalConfigWithin, stepPMF, next, dispatch, Instruction.next,
      Configuration.resumeAt, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.moveLeft, Tape.moveRight, PMF.pure_bind]

/-- The caller may have arbitrary finite physical padding. Reading the
actual left cell is enough; both tapes are restored exactly before control
passes to the selected continuation. -/
theorem runs_tapes (acceptPc rejectPc : Nat) (suffix : Program)
    (input output : Tape) (status : Bool)
    (hStatus : input.left.getD 0 none = some status) :
    let start : Configuration := { inputTape := input, outputTape := output }
    ∃ used, used ≤ 4 ∧
      RunsFor (dispatch acceptPc rejectPc ++ suffix) start
        (start.resumeAt (if status then acceptPc else rejectPc)) used := by
  cases input with
  | mk left current right =>
    cases left with
    | nil => simp at hStatus
    | cons head saved =>
      have hHead : head = some status := by simpa using hStatus
      subst head
      have hEval := eval_dispatch acceptPc rejectPc suffix saved right current output status
      have hSupport :
          ({ inputTape := { left := some status :: saved, current := current, right := right },
             outputTape := output } : Configuration).resumeAt (if status then acceptPc else rejectPc) ∈
          (evalConfigWithin (dispatch acceptPc rejectPc ++ suffix)
            { inputTape := { left := some status :: saved, current := current, right := right },
              outputTape := output } 4).support := by
        rw [hEval]
        simp
      exact ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le

/-- The branch acts on the actual post-power layout, with its protected
original request and both scratch blocks unchanged. -/
theorem runs_saved (acceptPc rejectPc : Nat) (suffix : Program)
    (request scratch : List Bool) (status : Bool) (padding : Nat) :
    ∃ used, used ≤ 4 ∧
      RunsFor (dispatch acceptPc rejectPc ++ suffix)
        (ChoosePowerReset.start request scratch status padding)
        ((ChoosePowerReset.start request scratch status padding).resumeAt
          (if status then acceptPc else rejectPc)) used := by
  have hEval := eval_dispatch acceptPc rejectPc suffix
    (none :: request.reverse.map some) (List.replicate padding none) none
    ({ left := savedOutputBlocks [[status], scratch] } : Tape) status
  have hSupport :
      ((ChoosePowerReset.start request scratch status padding).resumeAt
        (if status then acceptPc else rejectPc)) ∈
      (evalConfigWithin (dispatch acceptPc rejectPc ++ suffix)
        (ChoosePowerReset.start request scratch status padding) 4).support := by
    have hEval' : evalConfigWithin (dispatch acceptPc rejectPc ++ suffix)
        (ChoosePowerReset.start request scratch status padding) 4 =
      PMF.pure ((ChoosePowerReset.start request scratch status padding).resumeAt
        (if status then acceptPc else rejectPc)) := hEval
    rw [hEval']
    simp
  exact ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le

/-- Apply the dispatch to the actual guarded return layout. The same status
read by these instructions is the one produced by the core, and the entire
protected request remains available to either continuation. -/
theorem runs_returned (core : Program) (columns request : List Bool)
    (c : Configuration) (status : Bool) (hStatus : c.outputBits = [status])
    (acceptPc rejectPc : Nat) (suffix : Program) :
    let returned := ((GuardedCompiler.rawResultFrom core columns [none]
      (none :: request.reverse.map some) c).swapTapes).resumeAt 0
    ∃ used, used ≤ 4 ∧
      RunsFor (dispatch acceptPc rejectPc ++ suffix) returned
        (returned.resumeAt (if status then acceptPc else rejectPc)) used := by
  dsimp only
  rw [ChoosePowerReset.returned_start core columns request c status hStatus]
  exact runs_saved acceptPc rejectPc suffix request
    (GuardedCompiler.storedSourceScratchBits columns c.inputTape) status
    (2*c.outputTape.cells+2-1)

end Machine.ChoosePowerDispatch
