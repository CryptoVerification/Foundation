import Foundation.Crypto.Semantics.Machine.NativeInvocationTime

/-! Add actual first-return times in the existing native linker. The final
caller halt costs one real step. Equal upper bounds alone do not establish
these fixed-time hypotheses. This theorem adds no padding instructions. -/
namespace Machine.TypedNativeComposition.Link
open Foundation.Probability TimedExecution
universe u v w x
variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}
    {P : Machine.Procedure Input Output} {Q : Machine.Procedure NextInput NextOutput} (L : Link P Q)

theorem fixed_time (input : Input) (firstTime secondTime : Nat)
    (fixedFirst : ∀ result, result ∈ (L.first.costed input).support → result.2 = firstTime)
    (fixedSecond : ∀ middle, middle ∈ (L.first.costed input).support →
      ∀ result, result ∈ (L.second.costed middle.1).support → result.2 = secondTime)
    (result : Configuration × Nat) (hResult : result ∈ (L.native.execution.costed input).support) :
    result.2 = firstTime + secondTime + 1 := by
  rw [L.costed, PMF.mem_support_bind_iff] at hResult
  obtain ⟨first, hFirst, hRest⟩ := hResult
  rw [PMF.mem_support_map_iff] at hRest
  obtain ⟨second, hSecond, rfl⟩ := hRest
  rw [fixedFirst first hFirst, fixedSecond first hFirst second hSecond]

theorem joint_of_fixed_time (input : Input) (firstTime secondTime : Nat)
    (fixedFirst : ∀ result, result ∈ (L.first.costed input).support → result.2 = firstTime)
    (fixedSecond : ∀ middle, middle ∈ (L.first.costed input).support →
      ∀ result, result ∈ (L.second.costed middle.1).support → result.2 = secondTime) :
    L.native.execution.costed input = (L.native.execution.semantics input).map
      (fun state => (state, firstTime + secondTime + 1)) := by
  have h := L.native.execution.costed_view_of_fixed_time (fun _ state => state) input
    (firstTime + secondTime + 1) (L.fixed_time input firstTime secondTime fixedFirst fixedSecond)
  change (L.native.execution.costed input).map id = ((L.native.execution.semantics input).map id).map _ at h
  simpa only [PMF.map_id] using h

end Machine.TypedNativeComposition.Link
