import Foundation.Crypto.Semantics.Oracle.StatefulDiagramExchange

/-! A chronological operation log is part of the observation here. The log
records operation labels only; it is not a complete request/response trace.
A difference visible in this marginal also obstructs equality of richer logs. -/
namespace CryptoOracle.StatefulDiagram.HistoryBoundary
open Foundation.Probability
variable {Slot Op Value : Type} [DecidableEq Slot]

noncomputable def recorded (signature : Op → Interface Slot) (world : Kernels signature Value)
    (word : List Op) (store : Store Slot Value) : PMF (Store Slot Value × List Op) :=
  (execute signature world word store).map (fun final => (final, word))

theorem store_marginal (signature : Op → Interface Slot) (world : Kernels signature Value)
    (word : List Op) (store : Store Slot Value) :
    (recorded signature world word store).map Prod.fst = execute signature world word store := by
  simp only [recorded, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

theorem history_marginal (signature : Op → Interface Slot) (world : Kernels signature Value)
    (word : List Op) (store : Store Slot Value) :
    (recorded signature world word store).map Prod.snd = PMF.pure word := by
  simp only [recorded, PMF.map_comp, Function.comp_def]
  exact PMF.map_const _ _

theorem history_eq_of_recorded_eq (signature : Op → Interface Slot) (world : Kernels signature Value)
    (left right : List Op) (store : Store Slot Value)
    (same : recorded signature world left store = recorded signature world right store) : left = right := by
  classical
  have observed := congrArg (fun law => law.map Prod.snd) same
  rw [history_marginal, history_marginal] at observed
  have value := congrArg (fun law : PMF (List Op) => law left) observed
  by_contra different
  simp [PMF.pure_apply, different] at value

theorem exchange_not_history_equal (signature : Op → Interface Slot) (world : Kernels signature Value)
    (past future : List Op) (first second : Op) (store : Store Slot Value)
    (different : first ≠ second) :
    recorded signature world (past ++ [first, second] ++ future) store ≠
      recorded signature world (past ++ [second, first] ++ future) store := by
  intro same
  have words := history_eq_of_recorded_eq signature world _ _ store same
  have tails := List.append_cancel_left (by simpa only [List.append_assoc] using words)
  have heads := List.cons.inj tails
  exact different heads.1

/-- State exchange remains valid, while the chronological log distinguishes
its two boundaries. This is a boundary on observations, not a new separation rule. -/
theorem independent_exchange_boundary (signature : Op → Interface Slot) (world : Kernels signature Value)
    (past future : List Op) (first second : Op) (store : Store Slot Value)
    (accepted : checkExchange signature first second = true) (different : first ≠ second) :
    execute signature world (past ++ [first, second] ++ future) store =
      execute signature world (past ++ [second, first] ++ future) store ∧
    recorded signature world (past ++ [first, second] ++ future) store ≠
      recorded signature world (past ++ [second, first] ++ future) store :=
  ⟨exchange_in_context signature world past future first second store accepted,
    exchange_not_history_equal signature world past future first second store different⟩

/-- Swap two neighboring recorded labels, preserving every label. -/
def swapAt : Nat → List Op → List Op
  | 0, first :: second :: rest => second :: first :: rest
  | 0, rest => rest
  | _ + 1, [] => []
  | position + 1, head :: rest => head :: swapAt position rest

theorem swapAt_involutive (position : Nat) (word : List Op) :
    swapAt position (swapAt position word) = word := by
  induction position generalizing word with
  | zero => cases word with
    | nil => rfl
    | cons first rest => cases rest <;> rfl
  | succ position ih => cases word with
    | nil => rfl
    | cons first rest => simp only [swapAt, ih]

theorem swapAt_context (past future : List Op) (first second : Op) :
    swapAt past.length (past ++ [first, second] ++ future) = past ++ [second, first] ++ future := by
  induction past with
  | nil => rfl
  | cons head rest ih => simpa only [List.length_cons, List.cons_append, swapAt] using congrArg (List.cons head) ih

/-- This observation correspondence is bijective: it does not erase history.
It is not equality of the two chronological observations. -/
def historyEquiv (position : Nat) : (Store Slot Value × List Op) ≃ (Store Slot Value × List Op) where
  toFun result := (result.1, swapAt position result.2)
  invFun result := (result.1, swapAt position result.2)
  left_inv result := by simp only [swapAt_involutive]
  right_inv result := by simp only [swapAt_involutive]

theorem recorded_exchange_transport (signature : Op → Interface Slot) (world : Kernels signature Value)
    (past future : List Op) (first second : Op) (store : Store Slot Value)
    (accepted : checkExchange signature first second = true) :
    (recorded signature world (past ++ [first, second] ++ future) store).map
        (historyEquiv past.length) =
      recorded signature world (past ++ [second, first] ++ future) store := by
  simp only [recorded, PMF.map_comp, Function.comp_def, historyEquiv, Equiv.coe_fn_mk, swapAt_context]
  rw [exchange_in_context signature world past future first second store accepted]

/-- Every target test has an exactly matching source test after transport.
This changes the test along with the observation; it does not prove equality
for a fixed observer that can inspect chronological order. -/
theorem transported_observation {Observation : Type} (signature : Op → Interface Slot)
    (world : Kernels signature Value) (past future : List Op) (first second : Op)
    (store : Store Slot Value) (accepted : checkExchange signature first second = true)
    (observe : Store Slot Value × List Op → Observation) :
    (recorded signature world (past ++ [first, second] ++ future) store).map
        (fun result => observe (historyEquiv past.length result)) =
      (recorded signature world (past ++ [second, first] ++ future) store).map observe := by
  rw [← recorded_exchange_transport signature world past future first second store accepted]
  exact (PMF.map_comp _ _ _).symm

/-- An unchanged observer is preserved only under an explicit invariance
condition. The complete chronological-history observer does not satisfy it. -/
theorem invariant_observation {Observation : Type} (signature : Op → Interface Slot)
    (world : Kernels signature Value) (past future : List Op) (first second : Op)
    (store : Store Slot Value) (accepted : checkExchange signature first second = true)
    (observe : Store Slot Value × List Op → Observation)
    (invariant : ∀ result, observe (historyEquiv past.length result) = observe result) :
    (recorded signature world (past ++ [first, second] ++ future) store).map observe =
      (recorded signature world (past ++ [second, first] ++ future) store).map observe := by
  simpa only [invariant] using transported_observation signature world past future first second store accepted observe

/-- Every chronological label remains recoverable in the original order. -/
theorem recover_original (signature : Op → Interface Slot) (world : Kernels signature Value)
    (past future : List Op) (first second : Op) (store : Store Slot Value)
    (accepted : checkExchange signature first second = true) :
    (recorded signature world (past ++ [second, first] ++ future) store).map
        (historyEquiv (Slot := Slot) (Value := Value) past.length).symm =
      recorded signature world (past ++ [first, second] ++ future) store := by
  rw [← recorded_exchange_transport signature world past future first second store accepted]
  simp only [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id]

/-- A preexisting, arbitrarily correlated context remains paired with the
same state execution. No independent resampling of the state is introduced. -/
noncomputable def joint {Context : Type} (signature : Op → Interface Slot)
    (world : Kernels signature Value) (word : List Op) (input : PMF (Context × Store Slot Value)) :
    PMF (Context × (Store Slot Value × List Op)) :=
  input.bind fun initial => (recorded signature world word initial.2).map (fun final => (initial.1, final))

theorem joint_exchange_transport {Context : Type} (signature : Op → Interface Slot)
    (world : Kernels signature Value) (past future : List Op) (first second : Op)
    (input : PMF (Context × Store Slot Value)) (accepted : checkExchange signature first second = true) :
    (joint signature world (past ++ [first, second] ++ future) input).map
      (fun result => (result.1, historyEquiv past.length result.2)) =
    joint signature world (past ++ [second, first] ++ future) input := by
  simp only [joint, PMF.map_bind]
  congr 1
  funext initial
  rw [← recorded_exchange_transport signature world past future first second initial.2 accepted]
  simp only [PMF.map_comp, Function.comp_def]

/-- An observer of the original chronological labels distinguishes every
changed fixed word perfectly, even when final stores agree. -/
theorem distinguishing_history [DecidableEq Op] (signature : Op → Interface Slot) (world : Kernels signature Value)
    (left right : List Op) (store : Store Slot Value) (different : left ≠ right) :
    let observes : Store Slot Value × List Op → Bool := fun result => decide (result.2 = left)
    (recorded signature world left store).map observes = PMF.pure true ∧
    (recorded signature world right store).map observes = PMF.pure false := by
  classical
  dsimp only
  have result (word : List Op) :
      (recorded signature world word store).map (fun result => decide (result.2 = left)) =
      PMF.pure (decide (word = left)) := by
    have marginal := congrArg (PMF.map (fun word => decide (word = left)))
      (history_marginal signature world word store)
    simpa only [PMF.map_comp, Function.comp_def, PMF.pure_map] using marginal
  constructor
  · simpa using result left
  · simpa [Ne.symm different] using result right

namespace Example

def signature (op : Bool) : Interface Bool := ⟨∅, {op}⟩

theorem independent : checkExchange signature false true = true := by decide

theorem full_observation_boundary {Value : Type} (world : Kernels signature Value) (store : Store Bool Value) :
    execute signature world [false, true] store = execute signature world [true, false] store ∧
    recorded signature world [false, true] store ≠ recorded signature world [true, false] store :=
  independent_exchange_boundary signature world [] [] false true store independent (by decide)

end Example

end CryptoOracle.StatefulDiagram.HistoryBoundary
