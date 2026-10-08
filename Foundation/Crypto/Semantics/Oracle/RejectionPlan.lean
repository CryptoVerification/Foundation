import Foundation.Crypto.Semantics.Oracle.SelectedRejection

/-! Package the physical and resource obligations of a reusable adaptive
rejection program. Families may have different keys and native programs;
their public request selection must have a common joint cost distribution. -/
namespace CryptoOracle.Interactive.SelectedRejection
open Foundation.Probability TimedExecution
universe u v w
variable {State : Type u} {Value : Type v} {width : Nat} {code : Code}

structure Plan (State : Type u) (Value : Type v) (width : Nat) (code : Code)
    (oracle : BitOracle State) (keyTail : List (Option Bool)) (frame : Value → Configuration State) where
  native : Machine.Program
  key : List Bool
  key_width : key.length = width
  selection : Procedure (OneUseSource.step native code oracle) Value (Call State code width)
  handoff : ∀ start call, call ∈ (selection.semantics start).support →
    (reject native oracle key keyTail key_width call).entry () = selection.exit start call
  cap : Value → Nat
  bound : ∀ start call, call ∈ (selection.semantics start).support →
    (reject native oracle key keyTail key_width call).budget () ≤ cap start
  entry : ∀ start, selection.entry start =
    .source false (Machine.PairPreparation.operand [] key keyTail) (frame start)

variable {oracle : BitOracle State} {keyTail : List (Option Bool)} {frame : Value → Configuration State}
    (plan : Plan State Value width code oracle keyTail frame)
    (next : Call State code width → Value) (hNext : ∀ call, frame (next call) = returned call)
    (bound : Nat) (hBound : ∀ start, plan.selection.budget start + plan.cap start ≤ bound)

noncomputable def Plan.execute (stop : Value → Bool) (rounds : Nat) :=
  (round plan.native oracle plan.key keyTail plan.key_width plan.selection plan.handoff plan.cap plan.bound
    frame next hNext).iterateUntil stop bound hBound
      (fun start output _ => round_return plan.native oracle plan.key keyTail plan.key_width plan.selection
        plan.handoff plan.cap plan.bound frame next hNext plan.entry start output) rounds

theorem Plan.execute_budget (stop : Value → Bool) (rounds : Nat) (start : Value) :
    (plan.execute next hNext bound hBound stop rounds).budget start = rounds * bound := by
  unfold Plan.execute
  apply Procedure.until_budget

theorem Plan.execute_entry (stop : Value → Bool) (rounds : Nat) (start : Value) :
    (plan.execute next hNext bound hBound stop rounds).entry start =
      .source false (Machine.PairPreparation.operand [] plan.key keyTail) (frame start) := by
  unfold Plan.execute Procedure.iterateUntil
  rw [Procedure.iterate_entry]
  exact plan.entry start

theorem Plan.execute_exit (stop : Value → Bool) (rounds : Nat) (start output : Value) :
    (plan.execute next hNext bound hBound stop rounds).exit start output =
      .source false (Machine.PairPreparation.operand [] plan.key keyTail) (frame output) := by
  unfold Plan.execute Procedure.iterateUntil
  rw [Procedure.iterate_exit]
  exact plan.entry output

/-- The budget is an upper bound, not padding. Unused time resumes the
original runtime at the physical rejection-return state. -/
theorem Plan.resume_law (stop : Value → Bool) (rounds : Nat) (start : Value)
    (horizon : Nat) (hHorizon : rounds * bound ≤ horizon) :
    TimedExecution.eval (OneUseSource.step plan.native code oracle) horizon
      (.source false (Machine.PairPreparation.operand [] plan.key keyTail) (frame start)) =
      ((plan.execute next hNext bound hBound stop rounds).costed start).bind (fun result =>
        TimedExecution.eval (OneUseSource.step plan.native code oracle) (horizon - result.2)
          (.source false (Machine.PairPreparation.operand [] plan.key keyTail) (frame result.1))) := by
  have h := (plan.execute next hNext bound hBound stop rounds).law start horizon
    (by rw [plan.execute_budget]; exact hHorizon)
  rw [plan.execute_entry] at h
  simp only [plan.execute_exit] at h
  exact h

theorem Plan.public_cost (publicSelection : Value → PMF (Call State code width × Nat))
    (hSelection : ∀ start, plan.selection.costed start = publicSelection start)
    (stop : Value → Bool) (rounds : Nat) (start : Value) :
    (plan.execute next hNext bound hBound stop rounds).costed start =
      CostedIteration.eval (CostedIteration.guarded (roundKernel keyTail next publicSelection) stop) rounds start :=
  iterateUntil_public_cost plan.native oracle plan.key keyTail plan.key_width plan.selection plan.handoff
    plan.cap plan.bound frame next hNext plan.entry publicSelection hSelection bound hBound stop rounds start

/-- Sample a key label once and run its actual program. Public states and
accumulated actual costs remain independent of that label after any finite
number of adaptive rejected calls and any public stopping condition. -/
theorem Plan.family_independent {Key : Type w} (prior : PMF Key)
    (plans : Key → Plan State Value width code oracle keyTail frame)
    (next : Call State code width → Value) (hNext : ∀ call, frame (next call) = returned call)
    (publicSelection : Value → PMF (Call State code width × Nat))
    (hSelection : ∀ key start, (plans key).selection.costed start = publicSelection start)
    (bound : Nat) (hBound : ∀ key start, (plans key).selection.budget start + (plans key).cap start ≤ bound)
    (stop : Value → Bool) (rounds : Nat) (start : Value) :
    KeyedIteration.joint prior (fun key =>
      ((plans key).execute next hNext bound (hBound key) stop rounds).costed start) =
      prior.bind (fun key =>
        (CostedIteration.eval (CostedIteration.guarded (roundKernel keyTail next publicSelection) stop) rounds start).map
          (fun result => (key, result))) := by
  apply KeyedIteration.joint_independent
  intro key
  exact (plans key).public_cost next hNext bound (hBound key) publicSelection (hSelection key) stop rounds start

end CryptoOracle.Interactive.SelectedRejection
