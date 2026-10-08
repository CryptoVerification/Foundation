import Foundation.Crypto.Semantics.Machine.TapeEquivalence
import Foundation.Crypto.Semantics.TimedExecution

/-! Cell equivalence preserves actual boundary-arrival time, jointly with
any invariant observation of the full exit state. This concerns the native
transition system, not a cost chosen by a logical contract. At exhausted
fuel the result records a timeout state and the used fuel; completion is
not inferred without a separate boundary-completion proof. -/
namespace Machine
open Foundation.Probability

theorem runToBoundary_map_eq_of_equivalent {Observed : Type*} (code : Program)
    (boundary : Configuration → Bool)
    (boundaryInvariant : ∀ first second, first.Equivalent second → boundary first = boundary second)
    (fuel : Nat) (first second : Configuration) (equivalent : first.Equivalent second)
    (observe : Configuration × Nat → Observed)
    (invariant : ∀ first second time, first.Equivalent second →
      observe (first, time) = observe (second, time)) :
    (TimedExecution.runToBoundary (stepPMF code) boundary fuel first).map observe =
      (TimedExecution.runToBoundary (stepPMF code) boundary fuel second).map observe := by
  induction fuel generalizing first second observe with
  | zero => simp only [TimedExecution.runToBoundary, PMF.pure_map, invariant first second 0 equivalent]
  | succ fuel ih =>
      simp only [TimedExecution.runToBoundary, boundaryInvariant first second equivalent]
      split
      · simp only [PMF.pure_map, invariant first second 0 equivalent]
      · rw [PMF.map_bind, PMF.map_bind]
        apply stepPMF_bind_eq_of_equivalent code first second equivalent
        intro next other hNext
        simp only [PMF.map_comp, Function.comp_def]
        exact ih next other hNext (fun result => observe (result.1, result.2 + 1))
          (fun first second time h => invariant first second (time + 1) h)

theorem runToHalt_observe_time_eq_of_equivalent {Observed : Type*} (code : Program)
    (fuel : Nat) (first second : Configuration) (equivalent : first.Equivalent second)
    (observe : Configuration → Observed)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second) :
    (TimedExecution.runToBoundary (stepPMF code) Configuration.halted fuel first).map
      (fun result => (observe result.1, result.2)) =
    (TimedExecution.runToBoundary (stepPMF code) Configuration.halted fuel second).map
      (fun result => (observe result.1, result.2)) := by
  exact runToBoundary_map_eq_of_equivalent code Configuration.halted (fun _ _ h => h.2.1)
    fuel first second equivalent _ (fun first second time h => congrArg (fun value => (value, time)) (invariant first second h))

end Machine
