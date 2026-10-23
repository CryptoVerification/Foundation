import Foundation.Crypto.Semantics.Oracle.StatefulDiagramExchangeDecision

/-! A concrete obstruction to normalizing partial independence by descending
adjacent swaps. All statements concern the actual read/write exchange rule;
this is not an impossibility result for other normalization strategies. -/
namespace CryptoOracle.StatefulDiagram
variable {Slot Op : Type} [DecidableEq Slot]

/-- All one-step adjacent, independent, strictly descending swaps.
This enumerates positions in one word, not exchange paths. -/
def descendingSwaps (signature : Op → Interface Slot) (rank : Op → Nat) : List Op → List (List Op)
  | [] => []
  | first :: rest =>
    (match rest with
    | [] => []
    | second :: future =>
      if rank second < rank first ∧ checkExchange signature first second = true then
        [second :: first :: future]
      else []) ++ (descendingSwaps signature rank rest).map (List.cons first)

/-- Finite iteration of the explicitly oriented steps. -/
inductive DescendingPath (signature : Op → Interface Slot) (rank : Op → Nat) : List Op → List Op → Prop where
  | refl (word) : DescendingPath signature rank word word
  | step {one two three} : two ∈ descendingSwaps signature rank one →
      DescendingPath signature rank two three → DescendingPath signature rank one three

theorem descendingSwaps_checked (signature : Op → Interface Slot) (rank : Op → Nat)
    {one two : List Op} (member : two ∈ descendingSwaps signature rank one) :
    Nonempty (Exchange signature one two) := by
  induction one generalizing two with
  | nil => simp [descendingSwaps] at member
  | cons first rest ih =>
    simp only [descendingSwaps, List.mem_append] at member
    rcases member with direct | later
    · cases rest with
      | nil => simp at direct
      | cons second future =>
        change two ∈ (if rank second < rank first ∧ checkExchange signature first second = true
          then [second :: first :: future] else []) at direct
        by_cases condition : rank second < rank first ∧ checkExchange signature first second = true
        · simp only [if_pos condition, List.mem_singleton] at direct
          subst two
          exact ⟨.swap [] future first second condition.2⟩
        · simp [condition] at direct
    · obtain ⟨tail, inTail, equal⟩ := List.mem_map.mp later
      subst two
      obtain ⟨path⟩ := ih inTail
      exact ⟨by simpa only [List.singleton_append, List.append_nil] using
        path.whisker signature [first] []⟩

theorem DescendingPath.checked (signature : Op → Interface Slot) (rank : Op → Nat)
    {one two : List Op} (path : DescendingPath signature rank one two) :
    Nonempty (Exchange signature one two) := by
  induction path with
  | refl word => exact ⟨.refl word⟩
  | step member _ ih =>
    obtain ⟨first⟩ := descendingSwaps_checked signature rank member
    obtain ⟨rest⟩ := ih
    exact ⟨first.trans rest⟩

theorem DescendingPath.from_terminal (signature : Op → Interface Slot) (rank : Op → Nat)
    {one two : List Op} (terminal : descendingSwaps signature rank one = [])
    (path : DescendingPath signature rank one two) : two = one := by
  cases path with
  | refl => rfl
  | step member => simp [terminal] at member

end CryptoOracle.StatefulDiagram

namespace Foundation.Examples.StatefulDiagramNormalizationBoundary
open CryptoOracle.StatefulDiagram

/-- 0 reads 2; 1 is independent of both; 2 must stay before 0. -/
def signature (op : Fin 3) : Interface (Fin 3) :=
  ⟨if op = 0 then {2} else ∅, {op}⟩

def rank (op : Fin 3) : Nat := op.val

theorem peak_successors : descendingSwaps signature rank [2, 1, 0] = [[1, 2, 0], [2, 0, 1]] := by
  decide_cbv

theorem left_terminal : descendingSwaps signature rank [1, 2, 0] = [] := by decide_cbv

theorem right_terminal : descendingSwaps signature rank [2, 0, 1] = [] := by decide_cbv

theorem different_terminals : ([1, 2, 0] : List (Fin 3)) ≠ [2, 0, 1] := by decide

/-- The peak has no common descendant under descending adjacent swaps. -/
theorem peak_not_joinable : ¬ ∃ common,
    DescendingPath signature rank [1, 2, 0] common ∧
    DescendingPath signature rank [2, 0, 1] common := by
  rintro ⟨common, left, right⟩
  have first := left.from_terminal signature rank left_terminal
  have second := right.from_terminal signature rank right_terminal
  exact different_terminals (first.symm.trans second)

theorem descending_not_locally_confluent : ¬ ∀ (word left right : List (Fin 3)),
    left ∈ descendingSwaps signature rank word → right ∈ descendingSwaps signature rank word →
      ∃ common, DescendingPath signature rank left common ∧ DescendingPath signature rank right common := by
  intro confluent
  apply peak_not_joinable
  exact confluent [2, 1, 0] [1, 2, 0] [2, 0, 1]
    (by simp [peak_successors]) (by simp [peak_successors])

def peakLeft : Exchange signature [2, 1, 0] [1, 2, 0] :=
  .swap [] [0] 2 1 (by decide_cbv)

def peakRight : Exchange signature [2, 1, 0] [2, 0, 1] :=
  .swap [2] [] 1 0 (by decide_cbv)

/-- Distinct terminal words still denote the same full store distribution. -/
theorem terminal_execution_equal {Value : Type} (world : Kernels signature Value)
    (store : Store (Fin 3) Value) :
    execute signature world [1, 2, 0] store = execute signature world [2, 0, 1] store :=
  (peakLeft.symm.trans peakRight).sound signature world store

/-- Head extraction can cross an ascending pair, avoiding the stuck branch. -/
theorem extraction_succeeds : (exposeHead signature 1 [2, 0, 1]).isSome = true := by decide_cbv

theorem blocked_extraction : (exposeHead signature 0 [2, 1, 0]).isSome = false := by decide_cbv

/-- The complete generator connects the two distinct descending terminals. -/
def terminalAlignment : Exchange signature [1, 2, 0] [2, 0, 1] :=
  (alignExchange signature [1, 2, 0] [2, 0, 1]).get (by decide_cbv)

theorem terminalAlignment_count : terminalAlignment.swapCount signature = 2 := by decide_cbv

theorem impossible_order_rejected : (alignExchange signature [2, 1, 0] [0, 1, 2]).isSome = false := by
  decide_cbv

/-- info: (true, false, 2) -/
#guard_msgs in
#eval ((alignExchange signature [1, 2, 0] [2, 0, 1]).isSome,
  (alignExchange signature [2, 1, 0] [0, 1, 2]).isSome, terminalAlignment.swapCount signature)

/-- info: ([[1, 2, 0], [2, 0, 1]], [], [], true, false) -/
#guard_msgs in
#eval (descendingSwaps signature rank [2, 1, 0],
  descendingSwaps signature rank [1, 2, 0], descendingSwaps signature rank [2, 0, 1],
  (exposeHead signature 1 [2, 0, 1]).isSome, (exposeHead signature 0 [2, 1, 0]).isSome)

end Foundation.Examples.StatefulDiagramNormalizationBoundary
