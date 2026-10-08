import Foundation.Crypto.Semantics.Machine.NativeLinkFirstArrivalTime
import Foundation.Crypto.Semantics.Machine.NativeLinkFirstArrival
import Foundation.Crypto.Semantics.Machine.NativeFirstArrivalTimeTransport
import Foundation.Crypto.Semantics.Machine.NativeEquivalentComposition

/-! Append a component on actual inherited tapes and preserve fixed first-
halt times. The second input may depend on the preceding supported result.
All source proofs are first-arrival proofs, rather than budget equalities. -/
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
    (capBound : ∀ input output, output ∈ (L.native.execution.semantics input).support →
      R.procedure.execution.budget (adapt input output) ≤ cap input)

theorem appendEquivalent_firstArrival_fixed_time_of_sources (input : Input) (firstTime lastTime : Nat)
    (fixedFirst : ∀ result, result ∈ (L.component.firstArrival.procedure.execution.costed input).support → result.2 = firstTime)
    (fixedLast : ∀ output, output ∈ (L.native.execution.semantics input).support →
      ∀ result, result ∈ (R.firstArrival.procedure.execution.costed (adapt input output)).support → result.2 = lastTime)
    (result : Configuration × Nat)
    (hResult : result ∈ ((L.appendEquivalent R adapt equivalent cap capBound).component.firstArrival.procedure.execution.costed input).support) :
    result.2 = firstTime + lastTime + 1 := by
  let linked := L.appendEquivalent R adapt equivalent cap capBound
  have hFirst : ∀ result, result ∈ (linked.first.costed input).support → result.2 = firstTime := by
    apply linked.first_fixed_time_of_arrival input firstTime
    exact fixedFirst
  have hLast : ∀ middle, middle ∈ (linked.first.costed input).support →
      ∀ result, result ∈ (linked.second.costed middle.1).support → result.2 = lastTime := by
    intro middle hMiddle
    have hLogical := linked.first.result_support input middle hMiddle
    rw [linked.first_semantics, PMF.mem_support_map_iff] at hLogical
    obtain ⟨output, hOutput, hPair⟩ := hLogical
    have hInput : middle.1.1 = input := (congrArg Prod.fst hPair).symm
    have hValue : middle.1.2 = output := (congrArg Prod.snd hPair).symm
    apply linked.second_fixed_time_of_arrival middle.1 lastTime
    change ∀ result, result ∈ (R.equivalentEntries.firstArrival.procedure.execution.costed
      (L.equivalentInput R adapt equivalent middle.1.1 middle.1.2)).support → result.2 = lastTime
    apply R.equivalentEntries_firstArrival_fixed_time
    rw [L.equivalentInput_logical, hInput, hValue]
    exact fixedLast output hOutput
  have h := linked.firstArrival_joint_of_fixed_calls input firstTime lastTime hFirst hLast
  change result ∈ (linked.component.firstArrival.procedure.execution.costed input).support at hResult
  rw [h, PMF.mem_support_map_iff] at hResult
  obtain ⟨state, _, rfl⟩ := hResult
  rfl

/-- Compatibility with the earlier API. Its budget premise is no longer
needed by the stronger source-first-arrival rule above. -/
theorem appendEquivalent_firstArrival_fixed_time (input : Input) (firstTime lastTime : Nat)
    (_bounded : L.native.execution.budget input + cap input ≤ firstTime + lastTime)
    (fixedFirst : ∀ result, result ∈ (L.component.firstArrival.procedure.execution.costed input).support → result.2 = firstTime)
    (fixedLast : ∀ output, output ∈ (L.native.execution.semantics input).support →
      ∀ result, result ∈ (R.firstArrival.procedure.execution.costed (adapt input output)).support → result.2 = lastTime)
    (result : Configuration × Nat)
    (hResult : result ∈ ((L.appendEquivalent R adapt equivalent cap capBound).component.firstArrival.procedure.execution.costed input).support) :
    result.2 = firstTime + lastTime + 1 :=
  L.appendEquivalent_firstArrival_fixed_time_of_sources R adapt equivalent cap capBound input firstTime lastTime
    fixedFirst fixedLast result hResult

end Machine.TypedNativeComposition.Link
