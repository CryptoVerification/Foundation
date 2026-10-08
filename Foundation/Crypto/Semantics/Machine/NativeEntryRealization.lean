import Foundation.Crypto.Semantics.Machine.NativeEquivalentEntry

/-! Recover an exact physical semantics from a cell-equivalent entry adapter.
A second contract may describe richer saved context with a different input
and output type. If it uses the same code and the actual entry, its exact
exit law replaces the adapter's evaluation semantics, without normalizing
storage or adding instructions. -/
namespace Machine.NativeComponent
open Foundation.Probability TimedExecution
universe u v w x
variable {Input : Type u} {Output : Type v} {ExactInput : Type w} {ExactOutput : Type x}

/-- Transfer a full-state contract across an entry adapter. Budget inequality
is enough: once the exact contract has halted, extra analysis fuel is inert. -/
theorem equivalentEntries_realize (P : NativeComponent Input Output)
    (Q : NativeComponent ExactInput ExactOutput) (input : P.EquivalentInput) (exactInput : ExactInput)
    (sameCode : Q.procedure.code = P.procedure.code)
    (sameEntry : Q.procedure.execution.entry exactInput = input.actual)
    (budget : Q.procedure.execution.budget exactInput ≤ P.procedure.execution.budget input.logical) :
    P.equivalentEntries.procedure.execution.semantics input =
      (Q.procedure.execution.semantics exactInput).map (Q.procedure.execution.exit exactInput) := by
  change evalConfigWithin P.procedure.code input.actual (P.procedure.execution.budget input.logical) = _
  have h := Q.procedure.final_run exactInput (Q.halted exactInput)
    (P.procedure.execution.budget input.logical) budget
  simpa only [sameCode, sameEntry] using h

end Machine.NativeComponent
