import Foundation.Crypto.Semantics.Machine.NativeFirstArrival
import Foundation.Crypto.Semantics.Machine.NativeTimedObservationSecurity
import Foundation.Crypto.Semantics.ExactBoundaryClock

/-! Connect local exact clocks to native first-arrival contracts and time-
aware security. A clock is an analysis certificate, never a runtime timer.
Both physical output distributions and actual times remain accounted for. -/
namespace Machine.NativeComponent
open Foundation.Probability TimedExecution
universe u v w x
variable {Input : Type u} {Output : Type v} (P : NativeComponent Input Output)

theorem firstArrival_fixed_time_of_clock
    (clock : ExactBoundaryClock (stepPMF P.procedure.code) Configuration.halted)
    (input : Input) (valid : clock.valid (P.procedure.execution.entry input))
    (bounded : clock.remaining (P.procedure.execution.entry input) ≤ P.procedure.execution.budget input)
    (result : Configuration × Nat)
    (hResult : result ∈ (P.firstArrival.procedure.execution.costed input).support) :
    result.2 = clock.remaining (P.procedure.execution.entry input) := by
  rw [P.firstArrival_costed] at hResult
  exact clock.fixed_time _ _ valid bounded result hResult

theorem firstArrival_joint_of_clock
    (clock : ExactBoundaryClock (stepPMF P.procedure.code) Configuration.halted)
    (input : Input) (valid : clock.valid (P.procedure.execution.entry input))
    (bounded : clock.remaining (P.procedure.execution.entry input) ≤ P.procedure.execution.budget input) :
    P.firstArrival.procedure.execution.costed input =
      ((P.procedure.execution.semantics input).map (P.procedure.execution.exit input)).map
        (fun state => (state, clock.remaining (P.procedure.execution.entry input))) := by
  have h := clock.joint (P.procedure.execution.budget input) (P.procedure.execution.entry input) valid bounded
  rw [← P.firstArrival_costed, P.firstArrival.procedure.execution.correct] at h
  exact h

theorem firstArrival_time_eq_of_clock {Value : Type w} {Observed : Type x}
    (clock : ExactBoundaryClock (stepPMF P.procedure.code) Configuration.halted)
    (view : Input → Configuration → Value) (entry : Value → Configuration)
    (equivalent : ∀ input state, state ∈ (P.firstArrival.procedure.execution.semantics input).support →
      (state.resumeAt 0).Equivalent (entry (view input state)))
    (left right : Input)
    (validLeft : clock.valid (P.procedure.execution.entry left))
    (validRight : clock.valid (P.procedure.execution.entry right))
    (boundedLeft : clock.remaining (P.procedure.execution.entry left) ≤ P.procedure.execution.budget left)
    (boundedRight : clock.remaining (P.procedure.execution.entry right) ≤ P.procedure.execution.budget right)
    (sameTime : clock.remaining (P.procedure.execution.entry left) = clock.remaining (P.procedure.execution.entry right))
    (sameView : (P.firstArrival.procedure.execution.semantics left).map (view left) =
      (P.firstArrival.procedure.execution.semantics right).map (view right))
    (context : Nat → Program) (horizon : Nat → Nat) (observe : Nat → Configuration → Observed)
    (invariant : ∀ time first second, first.Equivalent second → observe time first = observe time second) :
    (P.firstArrival.procedure.execution.costed left).bind (fun result =>
      (evalConfigWithin (context result.2) (result.1.resumeAt 0) (horizon result.2)).map (observe result.2)) =
    (P.firstArrival.procedure.execution.costed right).bind (fun result =>
      (evalConfigWithin (context result.2) (result.1.resumeAt 0) (horizon result.2)).map (observe result.2)) := by
  apply P.firstArrival.continuation_time_eq_of_fixed_time view entry equivalent left right
    (clock.remaining (P.procedure.execution.entry left))
  · exact P.firstArrival_fixed_time_of_clock clock left validLeft boundedLeft
  · intro result hResult
    rw [P.firstArrival_fixed_time_of_clock clock right validRight boundedRight result hResult, sameTime]
  · exact sameView
  · exact invariant

theorem equivalentEntries_firstArrival_fixed_time_of_clock
    (clock : ExactBoundaryClock (stepPMF P.procedure.code) Configuration.halted)
    (input : EquivalentInput P) (valid : clock.valid (P.procedure.execution.entry input.logical))
    (bounded : clock.remaining (P.procedure.execution.entry input.logical) ≤ P.procedure.execution.budget input.logical)
    (result : Configuration × Nat)
    (hResult : result ∈ (P.equivalentEntries.firstArrival.procedure.execution.costed input).support) :
    result.2 = clock.remaining (P.procedure.execution.entry input.logical) := by
  have hDistribution := P.equivalentEntries_firstArrival_observation input Prod.snd (fun _ _ _ _ => rfl)
  have hTime : result.2 ∈ ((P.equivalentEntries.firstArrival.procedure.execution.costed input).map Prod.snd).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hResult, rfl⟩
  rw [hDistribution, PMF.mem_support_map_iff] at hTime
  obtain ⟨original, hOriginal, sameTime⟩ := hTime
  exact sameTime.symm.trans (P.firstArrival_fixed_time_of_clock clock input.logical valid bounded original hOriginal)

end Machine.NativeComponent
