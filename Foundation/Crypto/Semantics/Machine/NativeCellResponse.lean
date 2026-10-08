import Foundation.Crypto.Semantics.Machine.CellResponseExport
import Foundation.Crypto.Semantics.ProcedureInvariant

/-! Execute any certified native component and export its actual output
packet. Reachable layout obligations suffice. The output and actual native
first-halt time remain correlated, and every export transition is charged.
The component entry is an explicit precondition; request loading is separate. -/
namespace Machine.NativeCellResponse
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false

variable {Argument : Type u} {Result : Type v} (P : NativeComponent Argument Result)

def boundary : CellResponseExport.Control → Bool
  | .running machine => machine.halted
  | _ => true

noncomputable def body :=
  P.continueIn (CellResponseExport.step P.procedure.code) boundary ResponseExport.Control.running
    (fun _ => rfl) (fun machine h => by simp [CellResponseExport.step, h])

def Valid (cap : Nat) (machine : Configuration) : Prop :=
  machine.halted = true ∧
    machine.outputTape.Equivalent (ResponseExport.endTape machine.outputBits) ∧
    machine.outputBits.length ≤ cap

variable (argument : Argument) (cap : Nat)
    (hValid : ∀ result ∈ (P.procedure.execution.semantics argument).support,
      Valid cap (P.procedure.execution.exit argument result))

include hValid in
private theorem supported (unitArg : Unit) (machine : Configuration)
    (h : machine ∈ (((body P).reindex (fun _ : Unit => argument)).semantics unitArg).support) :
    Valid cap machine := by
  change machine ∈ ((P.procedure.execution.semantics argument).map
    (P.procedure.execution.exit argument)).support at h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨result, hr, rfl⟩ := h
  exact hValid result hr

noncomputable def certified :=
  ((body P).reindex (fun _ : Unit => argument)).certify (Valid cap) (supported P argument cap hValid)

noncomputable def delivery :
    TimedExecution.Procedure (CellResponseExport.step P.procedure.code) {machine // Valid cap machine} (List Bool) :=
  (CellResponseExport.procedure P.procedure.code).reindex (fun machine =>
    ⟨machine.val, machine.val.outputBits, machine.property.1, machine.property.2.1⟩)

noncomputable def whole :=
  (certified P argument cap hValid).seq (delivery P cap) (fun _ _ _ => rfl)
    (fun _ => 3 * cap + 4) (fun _ machine _ => by
      change 3 * machine.val.outputBits.length + 4 ≤ 3 * cap + 4
      have h := machine.property.2.2
      omega)

theorem entry : (whole P argument cap hValid).entry () =
    .running (P.procedure.execution.entry argument) := rfl

theorem budget : (whole P argument cap hValid).budget () =
    P.procedure.execution.budget argument + (3 * cap + 4) := rfl

theorem semantics :
    ((whole P argument cap hValid).semantics ()).map (fun result => result.2) =
      (P.procedure.execution.semantics argument).map
        (fun result => (P.procedure.execution.exit argument result).outputBits) := by
  change (((certified P argument cap hValid).semantics ()).bind _).map _ = _
  simp only [delivery, CellResponseExport.procedure, TimedExecution.Procedure.reindex,
    TimedExecution.Procedure.ofFixed, PMF.map_bind, PMF.pure_map, PMF.pure_bind, Function.comp_def]
  change ((certified P argument cap hValid).semantics ()).map (fun result => result.val.outputBits) = _
  have h := congrArg (fun distribution => distribution.map Configuration.outputBits)
    (((body P).reindex (fun _ : Unit => argument)).certify_semantics
      (Valid cap) (supported P argument cap hValid) ())
  change (((certified P argument cap hValid).semantics ()).map Subtype.val).map
    Configuration.outputBits =
      ((P.procedure.execution.semantics argument).map (P.procedure.execution.exit argument)).map
        Configuration.outputBits at h
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- Actual duration is native first-halt time plus the packet-dependent
export time. Replacing either duration by the declared cap is unnecessary. -/
theorem costed :
    ((whole P argument cap hValid).costed ()).map (fun result => (result.1.2, result.2)) =
      (P.firstArrival.procedure.execution.costed argument).map
        (fun result => (result.1.outputBits, result.2 + (3 * result.1.outputBits.length + 4))) := by
  change (((certified P argument cap hValid).costed ()).bind _).map _ = _
  simp only [delivery, CellResponseExport.procedure, TimedExecution.Procedure.reindex,
    TimedExecution.Procedure.ofFixed, PMF.map_bind, PMF.pure_map, PMF.pure_bind, Function.comp_def]
  change ((certified P argument cap hValid).costed ()).map
    (fun result => (result.1.val.outputBits, result.2 + (3 * result.1.val.outputBits.length + 4))) = _
  have h := congrArg (fun distribution => distribution.map
    (fun result : Configuration × Nat =>
      (result.1.outputBits, result.2 + (3 * result.1.outputBits.length + 4))))
    (((body P).reindex (fun _ : Unit => argument)).certify_costed
      (Valid cap) (supported P argument cap hValid) ())
  simp only [PMF.map_comp, Function.comp_def] at h
  change _ = (((body P).costed argument).map _) at h
  have hb := P.continueIn_costed (CellResponseExport.step P.procedure.code) boundary
    ResponseExport.Control.running (fun _ => rfl)
    (fun machine h => by simp [CellResponseExport.step, h]) argument
  change (body P).costed argument = P.firstArrival.procedure.execution.costed argument at hb
  rw [hb] at h
  exact h

include hValid in
theorem run (horizon : Nat)
    (hTime : P.procedure.execution.budget argument + (3 * cap + 4) ≤ horizon) :
    eval (CellResponseExport.step P.procedure.code) horizon (.running (P.procedure.execution.entry argument)) =
      (P.procedure.execution.semantics argument).map
        (fun result => .returned (P.procedure.execution.exit argument result).outputBits) := by
  have h := (whole P argument cap hValid).final_run () (fun _ _ => rfl) horizon hTime
  rw [entry] at h
  rw [h]
  change ((whole P argument cap hValid).semantics ()).map
    (fun result => ResponseExport.Control.returned result.2) = _
  have hs := congrArg (fun distribution => distribution.map ResponseExport.Control.returned)
    (semantics P argument cap hValid)
  simpa only [PMF.map_comp, Function.comp_def] using hs

end Machine.NativeCellResponse
