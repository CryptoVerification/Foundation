import Foundation.Crypto.Semantics.Oracle.StatefulDiagramHigherBoundary

/-! Extend the old three-form higher language with the missing single
self-exchange contraction. This fixes the verified parity obstruction; it is
NOT a proof of global higher coherence or finite derivation type. -/
namespace CryptoOracle.StatefulDiagram
open Foundation.Probability
variable {Slot Op Value : Type} [DecidableEq Slot]

theorem self_exchange_no_writes (signature : Op → Interface Slot) (op : Op)
    (accepted : checkExchange signature op op = true) : (signature op).writes = ∅ := by
  have safe : Independent signature op op := of_decide_eq_true accepted
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro slot member
  exact Finset.disjoint_left.mp safe.2.2 member member

/-- A total probabilistic box with no declared writes has no store effect.
This says nothing about the CPU time or erased private random draws. -/
theorem step_no_writes (signature : Op → Interface Slot) (world : Kernels signature Value)
    (op : Op) (empty : (signature op).writes = ∅) (store : Store Slot Value) :
    step signature world op store = PMF.pure store := by
  have unchanged : write (signature op).writes store = Function.const ((signature op).writes → Value) store := by
    funext values slot
    have outside : slot ∉ (signature op).writes := by rw [empty]; exact Finset.notMem_empty slot
    simp only [write, dif_neg outside, Function.const_apply]
  simp only [step, unchanged, PMF.map_const]

theorem self_exchange_no_effect (signature : Op → Interface Slot) (world : Kernels signature Value)
    (op : Op) (accepted : checkExchange signature op op = true) (store : Store Slot Value) :
    execute signature world [op, op] store = PMF.pure store := by
  have noWrite := self_exchange_no_writes signature op accepted
  simp only [execute, step_no_writes signature world op noWrite, PMF.pure_bind]

/-- New bounded root form plus the old diagrams and pasting/context closure.
No arbitrary pair of parallel paths is accepted as a generator. -/
inductive ExchangeHigherWithSelf (signature : Op → Interface Slot) : {one two : List Op} →
    Exchange signature one two → Exchange signature one two → Type where
  | original {one two} {first second : Exchange signature one two} :
      ExchangeHigher signature first second → ExchangeHigherWithSelf signature first second
  | self (op : Op) (accepted : checkExchange signature op op = true) :
      ExchangeHigherWithSelf signature (Exchange.swap [] [] op op accepted) (.refl [op, op])
  | symm {one two} {first second : Exchange signature one two} :
      ExchangeHigherWithSelf signature first second → ExchangeHigherWithSelf signature second first
  | trans {one two} {first second third : Exchange signature one two} :
      ExchangeHigherWithSelf signature first second → ExchangeHigherWithSelf signature second third →
        ExchangeHigherWithSelf signature first third
  | comp {one two three} {first first' : Exchange signature one two} {second second' : Exchange signature two three} :
      ExchangeHigherWithSelf signature first first' → ExchangeHigherWithSelf signature second second' →
        ExchangeHigherWithSelf signature (.trans first second) (.trans first' second')
  | whisker {one two} {first second : Exchange signature one two} (past future : List Op) :
      ExchangeHigherWithSelf signature first second → ExchangeHigherWithSelf signature
        (first.whisker signature past future) (second.whisker signature past future)

namespace HigherBoundary

def selfContraction : ExchangeHigherWithSelf readOnly selfSwap identityPath := .self () (by decide)

theorem extension_closes_counterexample : Nonempty (ExchangeHigherWithSelf readOnly selfSwap identityPath) :=
  ⟨selfContraction⟩

/-- The added root is not a derived instance of the old three higher forms. -/
theorem added_root_not_old_derived :
    Nonempty (ExchangeHigherWithSelf readOnly selfSwap identityPath) ∧
      ¬ Nonempty (ExchangeHigher readOnly selfSwap identityPath) :=
  ⟨extension_closes_counterexample, no_self_contraction⟩

end HigherBoundary
end CryptoOracle.StatefulDiagram
