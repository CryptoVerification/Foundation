import Foundation.Crypto.Semantics.Machine.TypedNativeComposition
import Foundation.Crypto.Semantics.Machine.RelationalProcedure

/-! Relational postconditions for actual compiled native sequences.
The premises concern supported component outcomes. No condition on malformed
layouts or impossible output labels is added by the composition rule. -/
namespace Machine.TypedNativeComposition.Link
open Foundation.Probability TimedExecution
universe u v w x
variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}
    {P : Machine.Procedure Input Output} {Q : Machine.Procedure NextInput NextOutput}
    (L : Link P Q)

/-- A relational consequence rule for the compiled, physically halted result. -/
theorem postcondition (relation : Input → Configuration → Prop)
    (hRelation : ∀ input output, output ∈ (P.execution.semantics input).support →
      ∀ result ∈ (Q.execution.semantics (L.adapt input output)).support,
        relation input
          {(Q.execution.exit (L.adapt input output) result).resumeAt L.finalPc with halted := true})
    (input : Input) (machine : Configuration)
    (h : machine ∈ (L.native.execution.semantics input).support) : relation input machine := by
  rw [L.semantics, PMF.mem_support_bind_iff] at h
  obtain ⟨output, ho, h⟩ := h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨result, hr, rfl⟩ := h
  exact hRelation input output ho result hr

noncomputable def refined (relation : Input → Configuration → Prop)
    (hRelation : ∀ input output, output ∈ (P.execution.semantics input).support →
      ∀ result ∈ (Q.execution.semantics (L.adapt input output)).support,
        relation input
          {(Q.execution.exit (L.adapt input output) result).resumeAt L.finalPc with halted := true}) :
    Machine.Procedure Input (RelationalProcedure.Result relation) :=
  RelationalProcedure.native L.native relation (L.postcondition relation hRelation)

/-- Refinement preserves the actual finite source, not just its semantics. -/
theorem refined_code (relation : Input → Configuration → Prop) (hRelation) :
    (L.refined relation hRelation).code = P.code.followedBy Q.code := rfl

theorem refined_budget (relation : Input → Configuration → Prop) (hRelation) (input : Input) :
    (L.refined relation hRelation).execution.budget input =
      P.execution.budget input + L.cap input + 1 := rfl

theorem refined_costed (relation : Input → Configuration → Prop) (hRelation) (input : Input) :
    ((L.refined relation hRelation).execution.costed input).map
      (fun result => (result.1.val.2, result.2)) = L.native.execution.costed input := by
  have h := RelationalProcedure.costed L.native relation (L.postcondition relation hRelation) input
  have hEta : (fun result : Configuration × Nat => (result.1, result.2)) = id := by
    funext result
    cases result
    rfl
  change _ = (L.native.execution.costed input).map (fun result => (result.1, result.2)) at h
  simpa only [refined, hEta, PMF.map_id] using h

/-- Any observation of the two physical tapes can be passed through the
actual handoff. Control relocation and the final halt do not change tapes. -/
theorem tapes_frame {Value : Type*} (observe : Tape → Tape → Value) (frame : Input → Value)
    (hFirst : ∀ input output, output ∈ (P.execution.semantics input).support →
      observe (P.execution.exit input output).inputTape (P.execution.exit input output).outputTape = frame input)
    (hSecond : ∀ input output, output ∈ (Q.execution.semantics input).support →
      observe (Q.execution.exit input output).inputTape (Q.execution.exit input output).outputTape =
        observe (Q.execution.entry input).inputTape (Q.execution.entry input).outputTape)
    (input : Input) (machine : Configuration)
    (h : machine ∈ (L.native.execution.semantics input).support) :
    observe machine.inputTape machine.outputTape = frame input := by
  apply L.postcondition (fun input machine =>
    observe machine.inputTape machine.outputTape = frame input) _ input machine h
  intro input output ho result hr
  have hEntry := congrArg (fun machine => observe machine.inputTape machine.outputTape)
    (L.handoff input output ho)
  change observe (Q.execution.entry (L.adapt input output)).inputTape
    (Q.execution.entry (L.adapt input output)).outputTape =
    observe (P.execution.exit input output).inputTape (P.execution.exit input output).outputTape at hEntry
  change observe (Q.execution.exit (L.adapt input output) result).inputTape
    (Q.execution.exit (L.adapt input output) result).outputTape = _
  exact (hSecond _ _ hr).trans (hEntry.trans (hFirst _ _ ho))

/-- A frame rule for input tapes. The first component establishes a chosen
input-dependent layout; the second preserves its own input tape. Physical
handoff identifies these layouts despite different logical input types. -/
theorem inputTape_frame (frame : Input → Tape)
    (hFirst : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).inputTape = frame input)
    (hSecond : ∀ input output, output ∈ (Q.execution.semantics input).support →
      (Q.execution.exit input output).inputTape = (Q.execution.entry input).inputTape)
    (input : Input) (machine : Configuration)
    (h : machine ∈ (L.native.execution.semantics input).support) :
    machine.inputTape = frame input :=
  L.tapes_frame (fun input _ => input) frame hFirst hSecond input machine h

theorem outputTape_frame (frame : Input → Tape)
    (hFirst : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).outputTape = frame input)
    (hSecond : ∀ input output, output ∈ (Q.execution.semantics input).support →
      (Q.execution.exit input output).outputTape = (Q.execution.entry input).outputTape)
    (input : Input) (machine : Configuration)
    (h : machine ∈ (L.native.execution.semantics input).support) :
    machine.outputTape = frame input :=
  L.tapes_frame (fun _ output => output) frame hFirst hSecond input machine h

theorem inputTape_preserved
    (hFirst : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).inputTape = (P.execution.entry input).inputTape)
    (hSecond : ∀ input output, output ∈ (Q.execution.semantics input).support →
      (Q.execution.exit input output).inputTape = (Q.execution.entry input).inputTape)
    (input : Input) (machine : Configuration)
    (h : machine ∈ (L.native.execution.semantics input).support) :
    machine.inputTape = (P.execution.entry input).inputTape :=
  L.inputTape_frame (fun input => (P.execution.entry input).inputTape) hFirst hSecond input machine h

/-- A reusable typed contract for the preserved original input tape. -/
noncomputable def preservingInput
    (hFirst : ∀ input output, output ∈ (P.execution.semantics input).support →
      (P.execution.exit input output).inputTape = (P.execution.entry input).inputTape)
    (hSecond : ∀ input output, output ∈ (Q.execution.semantics input).support →
      (Q.execution.exit input output).inputTape = (Q.execution.entry input).inputTape) :
    Machine.Procedure Input (RelationalProcedure.Result
      (fun input machine => machine.inputTape = (P.execution.entry input).inputTape)) :=
  RelationalProcedure.native L.native _ (L.inputTape_preserved hFirst hSecond)

end Machine.TypedNativeComposition.Link
