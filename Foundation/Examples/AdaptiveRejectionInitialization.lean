import Foundation.Examples.AdaptiveRejectionLoop
import Foundation.Examples.OneUseInitialization
import Foundation.Crypto.Semantics.Oracle.InitializationContinuation

/-! Actual native key generation followed by an arbitrary finite rejection
prefix. The exact private tape and public caller are passed through unchanged.
Initialization timing is retained, never replaced by a uniform-key prior. -/
namespace Foundation.AdaptiveRejectionInitializationExamples
open Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open AdaptiveRejectionLoopExamples
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {State : Type u} {width : Nat} (native : Machine.Program) (oracle : BitOracle State)
    (hMismatch : width ≠ 1) (stop : Public State → Bool) (rounds : Nat) (start : Public State)

noncomputable def suffix : Procedure (OneUseSource.step native code oracle) (Bits width) (Public State) :=
  Procedure.dispatch (fun key : Bits width =>
    show Procedure (OneUseSource.step native code oracle) Unit (Public State) from
      (execution native oracle key hMismatch stop rounds).reindex (fun _ : Unit => start))

theorem suffix_budget (key : Bits width) : (suffix native oracle hMismatch stop rounds start).budget key =
    rounds * (12 * min width 1 + 34) :=
  AdaptiveRejectionLoopExamples.budget native oracle key hMismatch stop rounds start

theorem suffix_entry (key : Bits width) : (suffix native oracle hMismatch stop rounds start).entry key =
    .source false (Machine.PairPreparation.operand [] key.toList []) (frame start) := by
  change (execution native oracle key hMismatch stop rounds).entry start = _
  exact AdaptiveRejectionLoopExamples.entry native oracle key hMismatch stop rounds start

theorem suffix_exit (key : Bits width) (finish : Public State) :
    (suffix native oracle hMismatch stop rounds start).exit key finish =
      .source false (Machine.PairPreparation.operand [] key.toList []) (frame finish) :=
  AdaptiveRejectionLoopExamples.exit native oracle key hMismatch stop rounds start finish

noncomputable def publicKernel := CostedIteration.eval (CostedIteration.guarded
  (SelectedRejection.roundKernel [] AdaptiveRejectionLoopExamples.next (publicSelection hMismatch)) stop) rounds start

theorem suffix_costed (key : Bits width) : (suffix native oracle hMismatch stop rounds start).costed key =
    publicKernel hMismatch stop rounds start :=
  public_cost native oracle key hMismatch stop rounds start

theorem suffix_semantics (key : Bits width) : (suffix native oracle hMismatch stop rounds start).semantics key =
    (publicKernel hMismatch stop rounds start).map Prod.fst := by
  rw [← Procedure.correct, suffix_costed]

noncomputable def whole :=
  OneUseInitialization.follow Machine.OneTimePad.keygen native code oracle (frame start)
    (OneUseInitializationExamples.initialization native code oracle (frame start) width)
    (fun key : Bits width => Machine.PairPreparation.operand [] key.toList []) (fun _ _ _ => rfl)
    (suffix native oracle hMismatch stop rounds start)
    (suffix_entry native oracle hMismatch stop rounds start)
    (fun _ => rounds * (12 * min width 1 + 34))
    (fun _ result _ => le_of_eq (suffix_budget native oracle hMismatch stop rounds start result.1))

theorem budget : (whole native oracle hMismatch stop rounds start).budget () =
    6 * width + 5 + rounds * (12 * min width 1 + 34) := by
  unfold whole
  rw [OneUseInitialization.follow_budget, OneUseInitializationExamples.budget]

/-- The public result and total actual cost include the real initializer's
time marginal, including any correlation its private computation may have. -/
theorem public_cost : ((whole native oracle hMismatch stop rounds start).costed ()).map
    (fun result => (result.1.2, result.2)) =
      (((OneUseInitializationExamples.initialization native code oracle (frame start) width).costed ()).map Prod.snd).bind
        (fun time => (publicKernel hMismatch stop rounds start).map
          (fun result => (result.1, time + result.2))) := by
  unfold whole
  apply OneUseInitialization.follow_public_cost_independent (view := fun _ output => output)
  intro key
  rw [suffix_costed]
  exact PMF.map_id _

/-- Generated keys and the complete public prefix result are independent.
This statement discards costs and does not assert timing independence. -/
theorem key_public_independence : ((whole native oracle hMismatch stop rounds start).semantics ()).map
    (fun result => (result.1.1, result.2)) =
      (uniform (Bits width)).bind (fun key => ((publicKernel hMismatch stop rounds start).map Prod.fst).map
        (fun publicState => (key, publicState))) := by
  unfold whole
  apply OneUseInitialization.follow_key_public_result (view := fun _ output => output)
  · exact OneUseInitializationExamples.key_distribution native code oracle (frame start) width
  · intro key
    rw [suffix_semantics]
    exact PMF.map_id _

/-- The logical prefix returns to the real caller, which keeps executing
for the time remaining in the outer initialization/runtime system. -/
theorem resume_law (horizon : Nat)
    (hHorizon : 6 * width + 5 + rounds * (12 * min width 1 + 34) ≤ horizon) :
    TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen native code oracle (frame start))
      horizon (.initializing (.generating (Machine.Configuration.initial (List.replicate width true)))) =
      ((whole native oracle hMismatch stop rounds start).costed ()).bind (fun result =>
        TimedExecution.eval (OneUseInitialization.step Machine.OneTimePad.keygen native code oracle (frame start))
          (horizon - result.2) (.active (.source false
            (Machine.PairPreparation.operand [] result.1.1.1.toList []) (frame result.1.2)))) := by
  have h := (whole native oracle hMismatch stop rounds start).law () horizon (by rw [budget]; exact hHorizon)
  change TimedExecution.eval _ _ ((whole native oracle hMismatch stop rounds start).entry ()) = _
  rw [h]
  congr 1
  funext result
  change TimedExecution.eval _ _ (OneUseInitialization.Control.active
    ((suffix native oracle hMismatch stop rounds start).exit result.1.1.1 result.1.2)) = _
  rw [suffix_exit]

end Foundation.AdaptiveRejectionInitializationExamples
