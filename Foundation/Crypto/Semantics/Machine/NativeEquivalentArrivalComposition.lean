import Foundation.Crypto.Semantics.Machine.NativeEquivalentComposition
import Foundation.Crypto.Semantics.Machine.NativeLinkFirstArrival

/-! Expose the physical first-arrival law of appending a component on the
actual inherited tapes. The canonical input selects only the proved time
bound. No layout normalization or caller-side input loader is performed.
Costs may be variable and correlated with either stage's full state. -/
namespace Machine.TypedNativeComposition.Link
open Foundation.Probability TimedExecution
universe u v w x y z
set_option backward.isDefEq.respectTransparency false
variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}
    {P : Machine.Procedure Input Output} {Q : Machine.Procedure NextInput NextOutput}
    (L : Link P Q) {LastInput : Type y} {LastOutput : Type z}
    (R : NativeComponent LastInput LastOutput)
    (adapt : Input → Configuration → LastInput)
    (equivalent : ∀ input output, output ∈ (L.native.execution.semantics input).support →
      (output.resumeAt 0).Equivalent (R.procedure.execution.entry (adapt input output)))
    (cap : Input → Nat)
    (bounded : ∀ input output, output ∈ (L.native.execution.semantics input).support →
      R.procedure.execution.budget (adapt input output) ≤ cap input)

theorem appendEquivalent_firstArrival_physical (input : Input) :
    (L.appendEquivalent R adapt equivalent cap bounded).component.firstArrival.procedure.execution.costed input =
      (L.component.firstArrival.procedure.execution.costed input).bind (fun first =>
        (runToBoundary (stepPMF R.procedure.code) Configuration.halted
          (R.procedure.execution.budget (adapt input first.1)) (first.1.resumeAt 0)).map (fun second =>
            ({second.1.resumeAt (L.appendEquivalent R adapt equivalent cap bounded).finalPc with halted := true},
              first.2 + second.2 + 1))) := by
  let linked := L.appendEquivalent R adapt equivalent cap bounded
  rw [linked.firstArrival_costed_from_components]
  change (L.component.firstArrival.procedure.execution.costed input).bind _ = _
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext first hFirst
  have hState := L.component.firstArrival.procedure.execution.result_support input first hFirst
  change first.1 ∈ ((L.native.execution.semantics input).map id).support at hState
  rw [PMF.map_id] at hState
  have hRecover := L.recover_return input first.1 hState
  change L.recover (first.1.resumeAt linked.entryPc) = first.1 at hRecover
  change (R.equivalentEntries.firstArrival.procedure.execution.costed
    (L.equivalentInput R adapt equivalent input (L.recover (first.1.resumeAt linked.entryPc)))).map _ = _
  rw [hRecover, R.equivalentEntries.firstArrival_costed, R.equivalentEntries_budget,
    R.equivalentEntries_entry, L.equivalentInput_logical,
    L.equivalentInput_actual R adapt equivalent input first.1 hState]
  rfl

end Machine.TypedNativeComposition.Link
