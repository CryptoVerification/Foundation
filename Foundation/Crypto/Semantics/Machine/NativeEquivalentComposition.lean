import Foundation.Crypto.Semantics.Machine.NativeRepresentationRelation

/-! Append a component when the actual previous result is cell-equivalent
to its canonical entry. Supported results execute from their actual tapes.
The fallback for impossible logical results only makes the adapter total;
no support test or normalization is added to the compiled program. -/
namespace Machine.TypedNativeComposition.Link
open Foundation.Probability TimedExecution
universe u v w x y z
variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}
    {P : Machine.Procedure Input Output} {Q : Machine.Procedure NextInput NextOutput}
    (L : Link P Q) {LastInput : Type y} {LastOutput : Type z}
    (R : NativeComponent LastInput LastOutput)
    (adapt : Input → Configuration → LastInput)
    (equivalent : ∀ input output, output ∈ (L.native.execution.semantics input).support →
      (output.resumeAt 0).Equivalent (R.procedure.execution.entry (adapt input output)))

noncomputable def equivalentInput (input : Input) (output : Configuration) : R.EquivalentInput := by
  classical
  exact if h : output ∈ (L.native.execution.semantics input).support then
    ⟨adapt input output, output.resumeAt 0, equivalent input output h⟩
  else
    ⟨adapt input output, R.procedure.execution.entry (adapt input output), Configuration.Equivalent.refl _⟩

theorem equivalentInput_logical (input : Input) (output : Configuration) :
    (L.equivalentInput R adapt equivalent input output).logical = adapt input output := by
  classical
  unfold equivalentInput
  split <;> rfl

theorem equivalentInput_actual (input : Input) (output : Configuration)
    (hOutput : output ∈ (L.native.execution.semantics input).support) :
    (L.equivalentInput R adapt equivalent input output).actual = output.resumeAt 0 := by
  classical
  simp only [equivalentInput, dif_pos hOutput]

noncomputable def appendEquivalent (cap : Input → Nat)
    (bounded : ∀ input output, output ∈ (L.native.execution.semantics input).support →
      R.procedure.execution.budget (adapt input output) ≤ cap input) :
    Link L.native R.equivalentEntries.procedure :=
  L.append R.equivalentEntries (L.equivalentInput R adapt equivalent)
    (by
      intro input output hOutput
      rw [R.equivalentEntries_entry, L.equivalentInput_actual R adapt equivalent input output hOutput]
      simp only [Configuration.resumeAt, Configuration.rebasePc, Nat.add_zero])
    cap (by
      intro input output hOutput
      rw [R.equivalentEntries_budget, L.equivalentInput_logical]
      exact bounded input output hOutput)

theorem appendEquivalent_code (cap) (bounded) :
    (L.appendEquivalent R adapt equivalent cap bounded).code = L.code.followedBy R.procedure.code := rfl

theorem appendEquivalent_budget (cap) (bounded) (input : Input) :
    (L.appendEquivalent R adapt equivalent cap bounded).native.execution.budget input =
      L.native.execution.budget input + cap input + 1 := by
  rw [Link.budget]
  rfl

end Machine.TypedNativeComposition.Link
