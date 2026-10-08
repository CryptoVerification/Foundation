import Foundation.Crypto.Semantics.Machine.CopyContracts
import Foundation.Crypto.Semantics.Machine.ProcedureCall

/-! A charged native copy with arbitrary retained prefixes and suffixes,
while an entire caller configuration remains isolated. Payload preparation
is a physical entry precondition and is not inferred from this contract. -/
namespace Foundation.CopyContractExamples
open Foundation.Probability TimedExecution
open Machine CopyContracts

noncomputable def savedCopy := ProcedureCall.savedProcedure Configuration segment
  (fun _ _ _ => rfl) (fun _ _ => ()) (fun _ output => by cases output; rfl)

theorem budget (input : SegmentInput) (caller : Configuration) :
    savedCopy.budget (input, caller) ≤ 6 * input.payload.length + 3 := by
  change segment.execution.budget input + 1 ≤ _
  have h := segment_budget input
  omega

theorem run (input : SegmentInput) (caller : Configuration) :
    eval (framedStep (ProcedureCall.step segment.code))
      (segment.execution.budget input + 1) (.running (segment.execution.entry input), caller) =
    PMF.pure (ProcedureCall.Control.returned (copySegmentFinish input.beforeInput input.beforeOutput
      input.afterInput input.payload input.blanks), caller) := by
  have h := ProcedureCall.saved_run segment (fun _ _ _ => rfl) (fun _ _ => ())
    (fun _ output => by cases output; rfl) input caller _ (Nat.le_refl _)
  simpa only [CopyContracts.segment, Machine.Procedure.ofFixed, TimedExecution.Procedure.ofFixed, PMF.pure_map] using h

theorem retained_call (input : RetainedInput) :
    eval (ProcedureCall.step retained.code) (8 * input.payload.length + 6)
      (.running (retained.execution.entry input)) =
    PMF.pure (ProcedureCall.Control.returned (RetainedCopy.finish input.payload input.before)) := by
  have h := ProcedureCall.run retained (fun _ _ _ => rfl) (fun _ _ => ())
    (fun _ output => by cases output; rfl) input (8 * input.payload.length + 6)
    (by change 8 * input.payload.length + 5 + 1 ≤ 8 * input.payload.length + 6; omega)
  simpa only [retained, Machine.Procedure.ofFixed, TimedExecution.Procedure.ofFixed, PMF.pure_map] using h

end Foundation.CopyContractExamples
