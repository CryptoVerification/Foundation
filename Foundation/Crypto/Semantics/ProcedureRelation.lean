import Foundation.Crypto.Semantics.ProcedureInvariant

/-! Input-dependent postconditions for probabilistic execution contracts.
The certified result retains the original input as proof metadata. Erasure
preserves the joint output/time law; no input is copied into machine memory. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v w
variable {State : Type u} {Input : Type v} {Output : Type w}
    {step : State → PMF State}

abbrev RelatedResult (relation : Input → Output → Prop) :=
  {result : Input × Output // relation result.1 result.2}

variable (P : Procedure step Input Output) (relation : Input → Output → Prop)
    (hRelation : ∀ input output, output ∈ (P.semantics input).support → relation input output)

include hRelation in
private theorem remembered_relation : ∀ input result,
    result ∈ (P.remember.semantics input).support → relation result.1 result.2 := by
    intro input result hr
    change result ∈ ((P.semantics input).map (fun output => (input, output))).support at hr
    rw [PMF.mem_support_map_iff] at hr
    obtain ⟨output, ho, rfl⟩ := hr
    exact hRelation input output ho

noncomputable def certifyRelation : Procedure step Input (RelatedResult relation) :=
  P.remember.certify (fun result => relation result.1 result.2)
    (remembered_relation P relation hRelation)

theorem certifyRelation_budget (input : Input) :
    (P.certifyRelation relation hRelation).budget input = P.budget input := rfl

theorem certifyRelation_entry (input : Input) :
    (P.certifyRelation relation hRelation).entry input = P.entry input := rfl

theorem certifyRelation_exit (input : Input) (result : RelatedResult relation) :
    (P.certifyRelation relation hRelation).exit input result = P.exit result.val.1 result.val.2 := rfl

/-- Input tags are proof metadata, and erasing them preserves time correlations. -/
theorem certifyRelation_costed (input : Input) :
    ((P.certifyRelation relation hRelation).costed input).map
      (fun result => (result.1.val.2, result.2)) = P.costed input := by
  have h := P.remember.certify_costed (fun result => relation result.1 result.2)
    (remembered_relation P relation hRelation) input
  have he := congrArg (fun distribution => distribution.map
    (fun result : (Input × Output) × Nat => (result.1.2, result.2))) h
  have hEta : (fun result : Output × Nat => (result.1, result.2)) = id := by
    funext result
    cases result
    rfl
  simpa only [certifyRelation, remember, PMF.map_comp, Function.comp_def, hEta, PMF.map_id] using he

theorem certifyRelation_semantics (input : Input) :
    ((P.certifyRelation relation hRelation).semantics input).map
      (fun result => result.val.2) = P.semantics input := by
  have h := congrArg (fun distribution => distribution.map Prod.fst)
    (P.certifyRelation_costed relation hRelation input)
  simpa only [PMF.map_comp, Function.comp_def, ← Procedure.correct] using h

/-- Only supported results have the current input tag. This is deliberately
not asserted of arbitrary inhabitants of the refined result type. -/
theorem certifyRelation_input (input : Input) (result : RelatedResult relation)
    (h : result ∈ ((P.certifyRelation relation hRelation).semantics input).support) :
    result.val.1 = input := by
  have hs : result.val ∈ (P.remember.semantics input).support := by
    rw [← P.remember.certify_semantics (fun result => relation result.1 result.2)
      (remembered_relation P relation hRelation),
      PMF.mem_support_map_iff]
    exact ⟨result, h, rfl⟩
  change result.val ∈ ((P.semantics input).map (fun output => (input, output))).support at hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨output, _, he⟩ := hs
  exact (congrArg Prod.fst he).symm

end Foundation.Probability.TimedExecution.Procedure
