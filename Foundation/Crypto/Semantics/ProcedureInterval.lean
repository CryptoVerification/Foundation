import Foundation.Crypto.Semantics.ProcedureStoppedIteration
import Foundation.Crypto.Semantics.Simulation

/-! Transfer a finite interval of an existing transition system into a
continuing machine. Simulation is required only before the boundary. Neither
absorption of source boundary states nor arrival by the supplied fuel is
assumed: a separate completion certificate is needed to claim arrival. -/
namespace Foundation.Probability.TimedExecution.Procedure
universe u v
variable {Source : Type u} {Target : Type v}

noncomputable def interval (sourceStep : Source → PMF Source) (targetStep : Target → PMF Target)
    (sourceBoundary : Source → Bool) (targetBoundary : Target → Bool) (embed : Source → Target)
    (hBoundary : ∀ source, targetBoundary (embed source) = sourceBoundary source)
    (hStep : ∀ source, sourceBoundary source = false →
      targetStep (embed source) = (sourceStep source).map embed)
    (fuel : Nat) : Procedure targetStep Source Source where
  entry := embed
  exit := fun _ => embed
  semantics := fun source => (runToBoundary sourceStep sourceBoundary fuel source).map Prod.fst
  costed := runToBoundary sourceStep sourceBoundary fuel
  budget := fun _ => fuel
  bounded := fun source => runToBoundary_bounded sourceStep sourceBoundary fuel source
  correct := fun _ => rfl
  law := by
    intro source horizon hBudget
    have h := runToBoundary_law targetStep targetBoundary fuel horizon (embed source) hBudget
    rw [runToBoundary_map sourceStep targetStep sourceBoundary targetBoundary embed hBoundary hStep] at h
    simpa only [PMF.bind_map, Function.comp_def] using h

/-- Supported outputs reach the source boundary only when a separate
finite-execution certificate establishes that all branches arrive. -/
theorem interval_complete (sourceStep : Source → PMF Source) (targetStep : Target → PMF Target)
    (sourceBoundary : Source → Bool) (targetBoundary : Target → Bool) (embed : Source → Target)
    (hBoundary : ∀ source, targetBoundary (embed source) = sourceBoundary source)
    (hStep : ∀ source, sourceBoundary source = false →
      targetStep (embed source) = (sourceStep source).map embed)
    (fuel : Nat) (source : Source)
    (hComplete : ∀ final ∈ (eval sourceStep fuel source).support, sourceBoundary final = true)
    (final : Source)
    (hFinal : final ∈ ((interval sourceStep targetStep sourceBoundary targetBoundary embed
      hBoundary hStep fuel).semantics source).support) : sourceBoundary final = true := by
  change final ∈ ((runToBoundary sourceStep sourceBoundary fuel source).map Prod.fst).support at hFinal
  rw [PMF.mem_support_map_iff] at hFinal
  obtain ⟨result, hResult, he⟩ := hFinal
  subst final
  exact runToBoundary_completes sourceStep sourceBoundary fuel source hComplete result hResult

end Foundation.Probability.TimedExecution.Procedure
