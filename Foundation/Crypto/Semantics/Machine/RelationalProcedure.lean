import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.ProcedurePhysical
import Foundation.Crypto.Semantics.ProcedureRelation

/-! Native contracts with arbitrary input-dependent physical postconditions.
The result retains the complete physical endpoint. Input labels and proofs
are mathematical metadata, not additional tapes, advice, or instructions. -/
namespace Machine.RelationalProcedure
open Foundation.Probability TimedExecution
universe u v
variable {Input : Type u} {Output : Type v}

abbrev Result (relation : Input → Configuration → Prop) :=
  TimedExecution.Procedure.RelatedResult relation

variable (P : Machine.Procedure Input Output) (relation : Input → Configuration → Prop)
    (hRelation : ∀ input output, output ∈ (P.execution.semantics input).support →
      relation input (P.execution.exit input output))

include hRelation in
private theorem physical_relation (input : Input) (machine : Configuration)
    (h : machine ∈ (P.execution.physical.semantics input).support) : relation input machine := by
  change machine ∈ ((P.execution.semantics input).map (P.execution.exit input)).support at h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨output, ho, rfl⟩ := h
  exact hRelation input output ho

noncomputable def native : Machine.Procedure Input (Result relation) :=
  ⟨P.code, P.execution.physical.certifyRelation relation (physical_relation P relation hRelation)⟩

theorem code : (native P relation hRelation).code = P.code := rfl

theorem entry (input : Input) :
    (native P relation hRelation).execution.entry input = P.execution.entry input := rfl

theorem budget (input : Input) :
    (native P relation hRelation).execution.budget input = P.execution.budget input := rfl

theorem exit (input : Input) (result : Result relation) :
    (native P relation hRelation).execution.exit input result = result.val.2 := rfl

theorem costed (input : Input) :
    ((native P relation hRelation).execution.costed input).map
      (fun result => (result.1.val.2, result.2)) =
      (P.execution.costed input).map (fun result => (P.execution.exit input result.1, result.2)) :=
  P.execution.physical.certifyRelation_costed relation (physical_relation P relation hRelation) input

theorem semantics (input : Input) :
    ((native P relation hRelation).execution.semantics input).map (fun result => result.val.2) =
      (P.execution.semantics input).map (P.execution.exit input) :=
  P.execution.physical.certifyRelation_semantics relation (physical_relation P relation hRelation) input

theorem input_tag (input : Input) (result : Result relation)
    (h : result ∈ ((native P relation hRelation).execution.semantics input).support) :
    result.val.1 = input :=
  P.execution.physical.certifyRelation_input relation (physical_relation P relation hRelation) input result h

/-- The input-dependent postcondition holds at the actual physical exit. -/
theorem postcondition (input : Input) (result : Result relation)
    (h : result ∈ ((native P relation hRelation).execution.semantics input).support) :
    relation input ((native P relation hRelation).execution.exit input result) := by
  rw [exit, ← input_tag P relation hRelation input result h]
  exact result.property

/-- Any physical observation, including a noninjective key projection, has
exactly the original distribution. This does not discard the stored state. -/
theorem observation {Value : Type*} (observe : Configuration → Value) (input : Input) :
    ((native P relation hRelation).execution.semantics input).map
      (fun result => observe result.val.2) =
      (P.execution.semantics input).map (fun result => observe (P.execution.exit input result)) := by
  have h := congrArg (fun distribution => distribution.map observe) (semantics P relation hRelation input)
  simpa only [PMF.map_comp, Function.comp_def] using h

end Machine.RelationalProcedure
