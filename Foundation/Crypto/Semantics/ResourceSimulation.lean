import Foundation.Crypto.Semantics.ResourceEnvelope
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! Transfer whole-prefix retained-data bounds along exact distributional
simulations. Data encoding overhead is an explicit monotone bound, never an
inferred property of observational equivalence. Only reachable target states
are covered; arbitrary states outside the embedding are not claimed safe. -/
namespace Foundation.Probability.TimedExecution.ResourceGrowth.Envelope
universe u v w x
variable {Source : Type u} {Target : Type v}
    {sourceStep : Source → PMF Source} (E : ResourceGrowth.Envelope sourceStep)
    (targetStep : Target → PMF Target) (embed : Source → Target)
    (targetSize : Target → Nat) (units : Nat → Nat) (hUnits : Monotone units)
    (hData : ∀ source, targetSize (embed source) ≤ units (E.retained source))

include hUnits hData

/-- Every supported target prefix has a source witness on the same elapsed
transition count. Neither injectivity nor a bound on unreachable states is
needed, but the target's retained-data overhead must be supplied explicitly. -/
theorem transport_peak
    (hStep : ∀ state, targetStep (embed state) = (sourceStep state).map embed)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (start : Source) (target : Target)
    (h : target ∈ (eval targetStep elapsed (embed start)).support) :
    targetSize target ≤ units (E.bound (E.extent start + horizon * E.increment)) := by
  rw [← eval_map sourceStep targetStep embed (fun state => (hStep state).symm),
    PMF.mem_support_map_iff] at h
  obtain ⟨source, hs, he⟩ := h
  subst target
  exact (hData source).trans (hUnits (E.peak horizon elapsed hElapsed start source hs))

/-- Component simulations need to hold only before their return boundary.
The memory bound is charged at the actual time in the boundary result. -/
theorem transport_boundary
    (sourceBoundary : Source → Bool) (targetBoundary : Target → Bool)
    (hBoundary : ∀ state, targetBoundary (embed state) = sourceBoundary state)
    (hStep : ∀ state, sourceBoundary state = false →
      targetStep (embed state) = (sourceStep state).map embed)
    (fuel : Nat) (start : Source) (result : Target × Nat)
    (h : result ∈ (runToBoundary targetStep targetBoundary fuel (embed start)).support) :
    targetSize result.1 ≤ units (E.bound (E.extent start + result.2 * E.increment)) := by
  rw [runToBoundary_map sourceStep targetStep sourceBoundary targetBoundary embed hBoundary hStep,
    PMF.mem_support_map_iff] at h
  obtain ⟨source, hs, he⟩ := h
  subst result
  exact (hData source.1).trans (hUnits (E.at_boundary sourceBoundary fuel start source hs))

end Foundation.Probability.TimedExecution.ResourceGrowth.Envelope

namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x
variable {Source : Type u} {Target : Type v} {Input : Type w} {Output : Type x}
    {sourceStep : Source → PMF Source}

/-- The transported procedure's time contract and its whole-prefix storage
bound refer to the same actual target machine and embedded physical entry. -/
theorem transport_resource (P : Procedure sourceStep Input Output)
    (E : ResourceGrowth.Envelope sourceStep)
    (targetStep : Target → PMF Target) (embed : Source → Target)
    (hStep : ∀ state, targetStep (embed state) = (sourceStep state).map embed)
    (targetSize : Target → Nat) (units : Nat → Nat) (hUnits : Monotone units)
    (hData : ∀ source, targetSize (embed source) ≤ units (E.retained source))
    (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ (P.transport targetStep embed hStep).budget input)
    (target : Target)
    (h : target ∈ (eval targetStep elapsed ((P.transport targetStep embed hStep).entry input)).support) :
    targetSize target ≤ units (E.bound (E.extent (P.entry input) + P.budget input * E.increment)) :=
  E.transport_peak targetStep embed targetSize units hUnits hData hStep
    (P.budget input) elapsed hElapsed (P.entry input) target h

end Foundation.Probability.TimedExecution.Procedure
