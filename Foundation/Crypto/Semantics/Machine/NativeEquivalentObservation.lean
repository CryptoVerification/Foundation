import Foundation.Crypto.Semantics.Machine.NativeEquivalentComposition

/-! Observe an appended component using its original distribution theorem.
Actual blank-padded states continue to execute the actual compiled code;
only cell-invariant observations are transferred to the canonical contract. -/
namespace Machine.TypedNativeComposition.Link
open Foundation.Probability
universe u v w x y z a
variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}
    {P : Machine.Procedure Input Output} {Q : Machine.Procedure NextInput NextOutput}
    (L : Link P Q) {LastInput : Type y} {LastOutput : Type z}
    (R : NativeComponent LastInput LastOutput)
    (adapt : Input → Configuration → LastInput)
    (equivalent : ∀ input output, output ∈ (L.native.execution.semantics input).support →
      (output.resumeAt 0).Equivalent (R.procedure.execution.entry (adapt input output)))

theorem appendEquivalent_observe (cap) (bounded) {Value : Type a}
    (observe : Configuration → Value)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second)
    (input : Input) :
    ((L.appendEquivalent R adapt equivalent cap bounded).native.execution.semantics input).map observe =
      (L.native.execution.semantics input).bind (fun middle =>
        (R.procedure.execution.semantics (adapt input middle)).map (fun result =>
          observe {(R.procedure.execution.exit (adapt input middle) result).resumeAt
            (L.appendEquivalent R adapt equivalent cap bounded).finalPc with halted := true})) := by
  rw [Link.semantics, PMF.map_bind]
  congr 1
  funext middle
  rw [PMF.map_comp]
  change (R.equivalentEntries.procedure.execution.semantics (L.equivalentInput R adapt equivalent input middle)).map
    (fun state => observe {state.resumeAt (L.appendEquivalent R adapt equivalent cap bounded).finalPc with halted := true}) = _
  rw [R.equivalentEntries_observe _ _ (fun first second h =>
    invariant _ _ ((h.resumeAt _).withHalted true)), L.equivalentInput_logical]

end Machine.TypedNativeComposition.Link
