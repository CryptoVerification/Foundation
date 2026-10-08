import Foundation.Crypto.Semantics.Machine.NativeComponent

/-! Change the logical input interface without introducing a runtime loader.
The new entry is exactly the old entry at the supplied input view. -/
namespace Machine.NativeComponent
open Foundation.Probability
universe u v w
variable {Input : Type u} {Output : Type v} {NewInput : Type w}

noncomputable def reindex (P : NativeComponent Input Output) (view : NewInput → Input) :
    NativeComponent NewInput Output where
  procedure := ⟨P.procedure.code, P.procedure.execution.reindex view⟩
  closed := P.closed
  entry := fun input => P.entry (view input)
  active := fun input => P.active (view input)
  halted := fun input => P.halted (view input)

variable (P : NativeComponent Input Output) (view : NewInput → Input)

theorem reindex_code : (P.reindex view).procedure.code = P.procedure.code := rfl

theorem reindex_entry (input : NewInput) :
    (P.reindex view).procedure.execution.entry input = P.procedure.execution.entry (view input) := rfl

theorem reindex_budget (input : NewInput) :
    (P.reindex view).procedure.execution.budget input = P.procedure.execution.budget (view input) := rfl

theorem reindex_semantics (input : NewInput) :
    (P.reindex view).procedure.execution.semantics input = P.procedure.execution.semantics (view input) := rfl

theorem reindex_costed (input : NewInput) :
    (P.reindex view).procedure.execution.costed input = P.procedure.execution.costed (view input) := rfl

theorem reindex_operational (hP : TimedExecution.Procedure.Operational P.procedure.execution) :
    TimedExecution.Procedure.Operational (P.reindex view).procedure.execution :=
  TimedExecution.Procedure.operational_reindex P.procedure.execution hP view

end Machine.NativeComponent
