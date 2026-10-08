import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.Machine.ResponseExport
import Foundation.Crypto.Semantics.ProcedurePhysical
import Foundation.Crypto.Semantics.ProcedureInvariant

/-! Turn supported physical export invariants into a typed native result.
No machine step, tape, code or elapsed cost changes. Impossible configurations
need not satisfy the export contract. Reading a result is proof metadata and
is not an added native instruction. -/
namespace Machine.ExportedProcedure
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

variable {Input : Type u} {Output : Type v} {Key : Type w}

def Valid (project : Configuration → Key) (encode : Key → List Bool) (machine : Configuration) : Prop :=
  machine.halted = true ∧ machine.outputTape = ResponseExport.endTape (encode (project machine))

abbrev Result (project : Configuration → Key) (encode : Key → List Bool) :=
  {machine : Configuration // Valid project encode machine}

variable (P : Machine.Procedure Input Output) (project : Configuration → Key) (encode : Key → List Bool)
    (hExport : ∀ input output, output ∈ (P.execution.semantics input).support →
      Valid project encode (P.execution.exit input output))

include hExport in
private theorem physical_valid (input : Input) (machine : Configuration)
    (h : machine ∈ (P.execution.physical.semantics input).support) : Valid project encode machine := by
  change machine ∈ ((P.execution.semantics input).map (P.execution.exit input)).support at h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨output, ho, rfl⟩ := h
  exact hExport input output ho

noncomputable def native : Machine.Procedure Input (Result project encode) :=
  ⟨P.code, P.execution.physical.certify (Valid project encode) (physical_valid P project encode hExport)⟩

theorem code : (native P project encode hExport).code = P.code := rfl

theorem entry (input : Input) :
    (native P project encode hExport).execution.entry input = P.execution.entry input := rfl

theorem budget (input : Input) :
    (native P project encode hExport).execution.budget input = P.execution.budget input := rfl

theorem exit (input : Input) (result : Result project encode) :
    (native P project encode hExport).execution.exit input result = result.val := rfl

theorem halted (input : Input) (result : Result project encode) :
    ((native P project encode hExport).execution.exit input result).halted = true := result.property.1

theorem tape (input : Input) (result : Result project encode) :
    ((native P project encode hExport).execution.exit input result).outputTape =
      ResponseExport.endTape (encode (project result.val)) := result.property.2

/-- Erasure preserves the full physical endpoint and its original cost. -/
theorem costed (input : Input) :
    ((native P project encode hExport).execution.costed input).map
      (fun result => (result.1.val, result.2)) =
      (P.execution.costed input).map (fun result => (P.execution.exit input result.1, result.2)) :=
  P.execution.physical.certify_costed (Valid project encode) (physical_valid P project encode hExport) input

theorem semantics (input : Input) :
    ((native P project encode hExport).execution.semantics input).map Subtype.val =
      (P.execution.semantics input).map (P.execution.exit input) :=
  P.execution.physical.certify_semantics (Valid project encode) (physical_valid P project encode hExport) input

theorem key_distribution (input : Input) :
    ((native P project encode hExport).execution.semantics input).map (fun result => project result.val) =
      (P.execution.semantics input).map (fun result => project (P.execution.exit input result)) := by
  have h := congrArg (fun distribution => distribution.map project) (semantics P project encode hExport input)
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- The fallback is used only outside the certified physical endpoint type.
It is a total mathematical decoder, not an operational branch or free copy. -/
noncomputable def read (input : Input) (machine : Configuration) : Result project encode := by
  classical
  exact if h : Valid project encode machine then ⟨machine, h⟩ else
    ((native P project encode hExport).execution.semantics input).support_nonempty.choose

theorem read_exit (input : Input) (result : Result project encode) :
    read P project encode hExport input ((native P project encode hExport).execution.exit input result) = result := by
  classical
  simp only [exit, read, dif_pos result.property]

end Machine.ExportedProcedure
