import Foundation.Crypto.Semantics.Machine.NativeFirstArrival
import Foundation.Crypto.Semantics.Machine.TapeSwapProcedure
import Foundation.Crypto.Semantics.ProcedureCostObservation

/-! Transport actual first-halt times independently of how they were proved:
local clocks, deterministic traces, or adjacent execution horizons. -/
namespace Machine.NativeComponent
open Foundation.Probability TimedExecution
universe u v
variable {Input : Type u} {Output : Type v} (P : NativeComponent Input Output)
set_option backward.isDefEq.respectTransparency false

theorem equivalentEntries_firstArrival_fixed_time (input : EquivalentInput P) (duration : Nat)
    (fixed : ∀ result, result ∈ (P.firstArrival.procedure.execution.costed input.logical).support → result.2 = duration)
    (result : Configuration × Nat)
    (hResult : result ∈ (P.equivalentEntries.firstArrival.procedure.execution.costed input).support) :
    result.2 = duration := by
  have hDistribution := P.equivalentEntries_firstArrival_observation input Prod.snd (fun _ _ _ _ => rfl)
  have hTime : result.2 ∈ ((P.equivalentEntries.firstArrival.procedure.execution.costed input).map Prod.snd).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hResult, rfl⟩
  rw [hDistribution, PMF.mem_support_map_iff] at hTime
  obtain ⟨original, hOriginal, sameTime⟩ := hTime
  exact sameTime.symm.trans (fixed original hOriginal)

theorem swapTapes_firstArrival_costed (input : Input) :
    P.swapTapes.firstArrival.procedure.execution.costed input =
      (P.firstArrival.procedure.execution.costed input).map (fun result => (result.1.swapTapes, result.2)) := by
  rw [P.swapTapes.firstArrival_costed, P.firstArrival_costed]
  exact runToBoundary_map (stepPMF P.procedure.code) (stepPMF P.procedure.code.swapTapes)
    Configuration.halted Configuration.halted Configuration.swapTapes (fun _ => rfl)
    (fun state _ => stepPMF_swapTapes P.procedure.code state) _ _

theorem swapTapes_firstArrival_fixed_time (input : Input) (duration : Nat)
    (fixed : ∀ result, result ∈ (P.firstArrival.procedure.execution.costed input).support → result.2 = duration)
    (result : Configuration × Nat)
    (hResult : result ∈ (P.swapTapes.firstArrival.procedure.execution.costed input).support) :
    result.2 = duration := by
  rw [P.swapTapes_firstArrival_costed, PMF.mem_support_map_iff] at hResult
  obtain ⟨original, hOriginal, rfl⟩ := hResult
  exact fixed original hOriginal

theorem firstArrival_joint_of_fixed_time (input : Input) (duration : Nat)
    (fixed : ∀ result, result ∈ (P.firstArrival.procedure.execution.costed input).support → result.2 = duration) :
    P.firstArrival.procedure.execution.costed input =
      ((P.procedure.execution.semantics input).map (P.procedure.execution.exit input)).map
        (fun state => (state, duration)) := by
  have h := P.firstArrival.procedure.execution.costed_view_of_fixed_time
    (fun _ state => state) input duration fixed
  change (P.firstArrival.procedure.execution.costed input).map id =
    ((P.firstArrival.procedure.execution.semantics input).map id).map _ at h
  simpa only [PMF.map_id, P.firstArrival_semantics] using h

end Machine.NativeComponent
