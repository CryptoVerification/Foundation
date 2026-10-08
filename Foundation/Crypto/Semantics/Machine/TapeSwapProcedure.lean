import Foundation.Crypto.Semantics.Machine.NativeComponent
import Foundation.Crypto.Semantics.Machine.TapeSwap

/-! Lift tape-operand relabeling from code to native contracts and components.
This compiles a different fixed program for the opposite physical layout;
it does not execute a whole-tape exchange at a runtime boundary. Logical
results and actual costs are unchanged, while physical endpoints are relabeled. -/
namespace Machine.Procedure
open Foundation.Probability TimedExecution
universe u v
variable {Input : Type u} {Output : Type v} (P : Machine.Procedure Input Output)

noncomputable def swapTapes : Machine.Procedure Input Output :=
  ⟨P.code.swapTapes, P.execution.transport (stepPMF P.code.swapTapes) Configuration.swapTapes
    (stepPMF_swapTapes P.code)⟩

theorem swapTapes_code : P.swapTapes.code = P.code.swapTapes := rfl

theorem swapTapes_entry (input : Input) :
    P.swapTapes.execution.entry input = (P.execution.entry input).swapTapes := rfl

theorem swapTapes_exit (input : Input) (output : Output) :
    P.swapTapes.execution.exit input output = (P.execution.exit input output).swapTapes := rfl

theorem swapTapes_budget (input : Input) : P.swapTapes.execution.budget input = P.execution.budget input := rfl

theorem swapTapes_semantics (input : Input) : P.swapTapes.execution.semantics input = P.execution.semantics input := rfl

theorem swapTapes_costed (input : Input) : P.swapTapes.execution.costed input = P.execution.costed input := rfl

/-- Both full physical tapes and their correlations with actual time remain. -/
theorem swapTapes_physical_costed (input : Input) :
    (P.swapTapes.execution.costed input).map (fun result =>
      (P.swapTapes.execution.exit input result.1, result.2)) =
    ((P.execution.costed input).map (fun result => (P.execution.exit input result.1, result.2))).map
      (fun result => (result.1.swapTapes, result.2)) := by
  rw [PMF.map_comp]
  rfl

theorem swapTapes_operational (hP : TimedExecution.Procedure.Operational P.execution) :
    TimedExecution.Procedure.Operational P.swapTapes.execution :=
  TimedExecution.Procedure.operational_transport P.execution hP _ _ (stepPMF_swapTapes P.code)

theorem swapTapes_run (input : Input) (horizon : Nat) :
    evalConfigWithin P.swapTapes.code (P.swapTapes.execution.entry input) horizon =
      (evalConfigWithin P.code (P.execution.entry input) horizon).map Configuration.swapTapes :=
  evalConfigWithin_swapTapes _ _ _

end Machine.Procedure

namespace Machine.NativeComponent
open Foundation.Probability
universe u v
variable {Input : Type u} {Output : Type v} (P : NativeComponent Input Output)

noncomputable def swapTapes : NativeComponent Input Output where
  procedure := P.procedure.swapTapes
  closed := Program.controlClosed_swapTapes P.procedure.code P.closed
  entry := fun input => by
    simpa only [Procedure.swapTapes_entry, Procedure.swapTapes_code, Program.swapTapes_length,
      Configuration.swapTapes] using P.entry input
  active := P.active
  halted := P.halted

theorem swapTapes_code_length : P.swapTapes.procedure.code.length = P.procedure.code.length :=
  Program.swapTapes_length _

end Machine.NativeComponent

namespace Machine.Configuration

theorem tapeCells_swapTapes (machine : Configuration) : machine.swapTapes.tapeCells = machine.tapeCells := by
  exact Nat.add_comm _ _

end Machine.Configuration

namespace Machine.Procedure
open Foundation.Probability TimedExecution
universe u v
variable {Input : Type u} {Output : Type v} (P : Machine.Procedure Input Output)

/-- Storage counts the relabeled code itself. Its bit encoding need not
have the same length as the old code's encoding. -/
theorem swapTapes_storage_peak (input : Input) (elapsed limit : Nat) (hElapsed : elapsed ≤ limit)
    (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF P.code.swapTapes) elapsed
      (P.execution.entry input).swapTapes).support) :
    (NativeEncodedResources.completeEncoding.encode (P.code.swapTapes, target)).length ≤
      NativeEncodedResources.bound P.code.swapTapes (P.execution.entry input).pc
        (P.execution.entry input).tapeCells limit := by
  have h := NativeEncodedResources.peak P.code.swapTapes _ elapsed hElapsed _ target hTarget
  rw [Configuration.tapeCells_swapTapes] at h
  exact h

theorem swapTapes_storage_costed (hP : TimedExecution.Procedure.Operational P.execution)
    (input : Input) (result : Output × Nat) (hResult : result ∈ (P.execution.costed input).support) :
    (NativeEncodedResources.completeEncoding.encode
      (P.code.swapTapes, (P.execution.exit input result.1).swapTapes)).length ≤
      NativeEncodedResources.bound P.code.swapTapes (P.execution.entry input).pc
        (P.execution.entry input).tapeCells result.2 :=
  P.swapTapes_storage_peak input result.2 result.2 (Nat.le_refl _) _
    (P.swapTapes_operational hP input result hResult)

end Machine.Procedure
