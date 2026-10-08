import Foundation.Crypto.Semantics.Machine.NativeEquivalentEntry
import Foundation.Crypto.Semantics.Machine.NativeBoundaryObservation
import Foundation.Crypto.Semantics.ProcedureBoundaryReachability
import Foundation.Crypto.Semantics.ProcedurePhysical
import Foundation.Crypto.Semantics.BoundaryStability

/-! Reuse any proved native component with its actual first-halt cost and
full physical result. No code, loader, normalization or padding is added.
The existing termination contract proves that the boundary is reached. -/
namespace Machine.NativeComponent
open Foundation.Probability TimedExecution
universe u v w
variable {Input : Type u} {Output : Type v} (P : NativeComponent Input Output)

private theorem physical_halted (input : Input) (state : Configuration)
    (hState : state ∈ (P.procedure.execution.physical.semantics input).support) : state.halted = true := by
  change state ∈ ((P.procedure.execution.semantics input).map (P.procedure.execution.exit input)).support at hState
  rw [PMF.mem_support_map_iff] at hState
  obtain ⟨output, hOutput, rfl⟩ := hState
  exact P.halted input output hOutput

private theorem halt_absorbing (state : Configuration) (halted : state.halted = true) :
    stepPMF P.procedure.code state = PMF.pure state := by
  simp [stepPMF, next, halted]

noncomputable def firstArrival : NativeComponent Input Configuration where
  procedure := {
    code := P.procedure.code
    execution := P.procedure.execution.physical.liftBoundary Configuration.halted
      (P.physical_halted) (P.halt_absorbing) (fun _ state => state) (fun _ _ => rfl)
      (stepPMF P.procedure.code) Configuration.halted id (fun _ => rfl)
      (fun _ _ => (PMF.map_id _).symm)
  }
  closed := P.closed
  entry := P.entry
  active := P.active
  halted := P.physical_halted

theorem firstArrival_code : P.firstArrival.procedure.code = P.procedure.code := rfl

theorem firstArrival_entry (input : Input) :
    P.firstArrival.procedure.execution.entry input = P.procedure.execution.entry input := rfl

theorem firstArrival_budget (input : Input) :
    P.firstArrival.procedure.execution.budget input = P.procedure.execution.budget input := rfl

theorem firstArrival_exit (input : Input) (state : Configuration) :
    P.firstArrival.procedure.execution.exit input state = state := rfl

theorem firstArrival_semantics (input : Input) :
    P.firstArrival.procedure.execution.semantics input =
      (P.procedure.execution.semantics input).map (P.procedure.execution.exit input) := rfl

theorem firstArrival_costed (input : Input) :
    P.firstArrival.procedure.execution.costed input =
      runToBoundary (stepPMF P.procedure.code) Configuration.halted (P.procedure.execution.budget input)
        (P.procedure.execution.entry input) := by
  change (runToBoundary _ _ _ _).map (fun result => (result.1, result.2)) = _
  exact PMF.map_id _

theorem firstArrival_operational : Procedure.Operational P.firstArrival.procedure.execution := by
  intro input result hResult
  rw [P.firstArrival_costed] at hResult
  exact runToBoundary_reachable (stepPMF P.procedure.code) Configuration.halted _ _ result hResult

theorem firstArrival_halted (input : Input) (result : Configuration × Nat)
    (hResult : result ∈ (P.firstArrival.procedure.execution.costed input).support) : result.1.halted = true :=
  P.firstArrival.halted input result.1 (P.firstArrival.procedure.execution.result_support input result hResult)

theorem firstArrival_idempotent_costed (input : Input) :
    P.firstArrival.firstArrival.procedure.execution.costed input =
      P.firstArrival.procedure.execution.costed input := by
  rw [P.firstArrival.firstArrival_costed, P.firstArrival_costed]
  rfl

theorem equivalentEntries_firstArrival_observe {Value : Type*} (input : EquivalentInput P)
    (observe : Configuration → Value)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second) :
    (P.equivalentEntries.firstArrival.procedure.execution.costed input).map (fun result => (observe result.1, result.2)) =
      (P.firstArrival.procedure.execution.costed input.logical).map (fun result => (observe result.1, result.2)) := by
  rw [P.equivalentEntries.firstArrival_costed, P.firstArrival_costed]
  exact runToHalt_observe_time_eq_of_equivalent P.procedure.code _ _ _ input.equivalent observe invariant

theorem firstArrival_costed_horizon (input : Input) (horizon : Nat)
    (hTime : P.procedure.execution.budget input ≤ horizon) :
    runToBoundary (stepPMF P.procedure.code) Configuration.halted horizon
      (P.procedure.execution.entry input) = P.firstArrival.procedure.execution.costed input := by
  rw [P.firstArrival_costed]
  apply runToBoundary_fuel_stable _ _ _ _ _ hTime
  intro result hResult
  apply P.firstArrival_halted input result
  rwa [P.firstArrival_costed]

theorem firstArrival_run (input : Input) (horizon : Nat)
    (hTime : P.procedure.execution.budget input ≤ horizon) :
    evalConfigWithin P.procedure.code (P.procedure.execution.entry input) horizon =
      P.firstArrival.procedure.execution.semantics input :=
  P.procedure.final_run input (P.halted input) horizon hTime

theorem firstArrival_storage_costed (input : Input) (result : Configuration × Nat)
    (hResult : result ∈ (P.firstArrival.procedure.execution.costed input).support) :
    (NativeEncodedResources.completeEncoding.encode (P.procedure.code, result.1)).length ≤
      NativeEncodedResources.bound P.procedure.code (P.procedure.execution.entry input).pc
        (P.procedure.execution.entry input).tapeCells result.2 := by
  rw [P.firstArrival_costed] at hResult
  exact NativeEncodedResources.boundary P.procedure.code Configuration.halted _ _ result hResult

theorem equivalentEntries_firstArrival_observation {Value : Type*} (input : EquivalentInput P)
    (observe : Configuration × Nat → Value)
    (invariant : ∀ first second time, first.Equivalent second →
      observe (first, time) = observe (second, time)) :
    (P.equivalentEntries.firstArrival.procedure.execution.costed input).map observe =
      (P.firstArrival.procedure.execution.costed input.logical).map observe := by
  rw [P.equivalentEntries.firstArrival_costed, P.firstArrival_costed]
  exact runToBoundary_map_eq_of_equivalent P.procedure.code Configuration.halted (fun _ _ h => h.2.1)
    _ _ _ input.equivalent observe invariant

/-- Actual first-arrival laws depend on code and entry, rather than which
valid termination contract or upper bound was used to certify them. -/
theorem firstArrival_costed_eq_of_code_entry {OtherOutput : Type w}
    (Q : NativeComponent Input OtherOutput) (input : Input)
    (sameCode : P.procedure.code = Q.procedure.code)
    (sameEntry : P.procedure.execution.entry input = Q.procedure.execution.entry input) :
    P.firstArrival.procedure.execution.costed input = Q.firstArrival.procedure.execution.costed input := by
  have hRun (fuel : Nat) :
      runToBoundary (stepPMF P.procedure.code) Configuration.halted fuel (P.procedure.execution.entry input) =
      runToBoundary (stepPMF Q.procedure.code) Configuration.halted fuel (Q.procedure.execution.entry input) :=
    congrArg₂ (fun code start => runToBoundary (stepPMF code) Configuration.halted fuel start) sameCode sameEntry
  rcases Nat.le_total (P.procedure.execution.budget input) (Q.procedure.execution.budget input) with hBudget | hBudget
  · have h := P.firstArrival_costed_horizon input (Q.procedure.execution.budget input) hBudget
    rw [hRun] at h
    rw [Q.firstArrival_costed]
    exact h.symm
  · have h := Q.firstArrival_costed_horizon input (P.procedure.execution.budget input) hBudget
    rw [← hRun] at h
    rw [P.firstArrival_costed]
    exact h

end Machine.NativeComponent
