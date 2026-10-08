import Foundation.Crypto.Semantics.Oracle.RejectionPlan
import Foundation.Crypto.Semantics.KeyedContinuation

/-! Rejected adaptive calls can precede a key-dependent normal operation.
The successor starts at the actual retained-key return configuration.
Security is required only after averaging the successor over the key prior;
it is not incorrectly demanded separately for each key. -/
namespace CryptoOracle.Interactive.SelectedRejection
open Foundation.Probability TimedExecution
universe u v w x y
variable {State : Type u} {Value : Type v} {Output : Type w} {width : Nat} {code : Code}
    {oracle : BitOracle State} {keyTail : List (Option Bool)} {frame : Value → Configuration State}

variable (plan : Plan State Value width code oracle keyTail frame)
    (next : Call State code width → Value) (hNext : ∀ call, frame (next call) = returned call)
    (bound : Nat) (hBound : ∀ start, plan.selection.budget start + plan.cap start ≤ bound)
    (stop : Value → Bool) (rounds : Nat)
    (continuation : Procedure (OneUseSource.step plan.native code oracle) Value Output)
    (hEntry : ∀ value, continuation.entry value =
      .source false (Machine.PairPreparation.operand [] plan.key keyTail) (frame value))
    (cap : Value → Nat)
    (hCap : ∀ start value,
      value ∈ ((plan.execute next hNext bound hBound stop rounds).semantics start).support →
      continuation.budget value ≤ cap start)

noncomputable def Plan.follow :=
  (plan.execute next hNext bound hBound stop rounds).seq continuation
    (fun _ value _ => (hEntry value).trans (plan.execute_exit next hNext bound hBound stop rounds _ value).symm)
    cap hCap

theorem Plan.follow_budget (start : Value) :
    (plan.follow next hNext bound hBound stop rounds continuation hEntry cap hCap).budget start =
      rounds * bound + cap start := by
  change (plan.execute next hNext bound hBound stop rounds).budget start + cap start = _
  rw [plan.execute_budget]

theorem Plan.follow_public_cost {Key : Type x} {Observed : Type y} (keys : PMF Key)
    (plans : Key → Plan State Value width code oracle keyTail frame)
    (next : Call State code width → Value) (hNext : ∀ call, frame (next call) = returned call)
    (bound : Nat) (hBound : ∀ key start, (plans key).selection.budget start + (plans key).cap start ≤ bound)
    (stop : Value → Bool) (rounds : Nat)
    (continuation : ∀ key, Procedure (OneUseSource.step (plans key).native code oracle) Value Output)
    (hEntry : ∀ key value, (continuation key).entry value =
      .source false (Machine.PairPreparation.operand [] (plans key).key keyTail) (frame value))
    (cap : Value → Nat)
    (hCap : ∀ key start value,
      value ∈ (((plans key).execute next hNext bound (hBound key) stop rounds).semantics start).support →
      (continuation key).budget value ≤ cap start)
    (view : Key → Value → Output → Observed)
    (publicSelection : Value → PMF (Call State code width × Nat))
    (hSelection : ∀ key start, (plans key).selection.costed start = publicSelection start)
    (publicContinuation : Value → PMF (Observed × Nat))
    (hContinuation : ∀ value, keys.bind (fun key => ((continuation key).costed value).map
      (fun result => (view key value result.1, result.2))) = publicContinuation value)
    (start : Value) :
    keys.bind (fun key =>
      (((plans key).follow next hNext bound (hBound key) stop rounds (continuation key) (hEntry key) cap (hCap key)).costed start).map
        (fun result => ((result.1.1, view key result.1.1 result.1.2), result.2))) =
      (CostedIteration.eval (CostedIteration.guarded (roundKernel keyTail next publicSelection) stop) rounds start).bind
        (fun first => (publicContinuation first.1).map
          (fun second => ((first.1, second.1), first.2 + second.2))) := by
  apply Procedure.keyed_seq_public_cost keys
    (fun key => (plans key).execute next hNext bound (hBound key) stop rounds)
    continuation
    (fun key initial value _ => (hEntry key value).trans
      ((plans key).execute_exit next hNext bound (hBound key) stop rounds initial value).symm)
    (fun _ => cap) hCap view start
  · intro key
    exact (plans key).public_cost next hNext bound (hBound key) publicSelection (hSelection key) stop rounds start
  · exact hContinuation

end CryptoOracle.Interactive.SelectedRejection
