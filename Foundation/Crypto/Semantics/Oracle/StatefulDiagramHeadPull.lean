import Foundation.Crypto.Semantics.Oracle.StatefulDiagramHorizontal

/-! Explicit residual paths after deleting one occurrence, and checked paths
pulling an accessible label to the front. These data are used to construct
higher comparisons; no new higher root is introduced. -/
namespace CryptoOracle.StatefulDiagram
variable {Slot Op Value : Type} [DecidableEq Slot] [DecidableEq Op]

/-- Delete the first wanted occurrence on both sides of one primitive swap. -/
def eraseSwap (signature : Op → Interface Slot) (wanted : Op) :
    (past future : List Op) → (a b : Op) → (ab : checkExchange signature a b = true) →
    Exchange signature ((past ++ [a, b] ++ future).erase wanted) ((past ++ [b, a] ++ future).erase wanted)
  | [], future, a, b, ab => by
    by_cases first : a = wanted
    · subst a
      by_cases second : b = wanted
      · subst b
        exact .refl _
      · simpa only [List.nil_append, List.cons_append, List.erase_cons_head, List.erase_cons,
          beq_iff_eq, second, if_false] using Exchange.refl (b :: future)
    · by_cases second : b = wanted
      · subst b
        simpa only [List.nil_append, List.cons_append, List.erase_cons_head, List.erase_cons,
          beq_iff_eq, first, if_false] using Exchange.refl (a :: future)
      · simpa only [List.nil_append, List.cons_append, List.erase_cons, beq_iff_eq, first, second, if_false] using
          Exchange.swap [] (future.erase wanted) a b ab
  | head :: past, future, a, b, ab => by
    by_cases equal : head = wanted
    · subst head
      simpa only [List.cons_append, List.erase_cons_head] using Exchange.swap past future a b ab
    · simpa only [List.cons_append, List.erase_cons, beq_iff_eq, equal, if_false] using
        (eraseSwap signature wanted past future a b ab).prepend signature head

/-- A computable path-level counterpart of Exchange.erase. -/
def Exchange.eraseData (signature : Op → Interface Slot) (wanted : Op) : {one two : List Op} →
    Exchange signature one two → Exchange signature (one.erase wanted) (two.erase wanted)
  | _, _, .refl word => .refl (word.erase wanted)
  | _, _, .swap past future a b ab => eraseSwap signature wanted past future a b ab
  | _, _, .symm path => (path.eraseData signature wanted).symm
  | _, _, .trans first second => (first.eraseData signature wanted).trans (second.eraseData signature wanted)

/-- Pull the first accessible occurrence to the head, retaining exactly the
original order of all other occurrences. -/
def pullHead (signature : Op → Interface Slot) (wanted : Op) : (word : List Op) →
    AccessibleHead signature wanted word → Exchange signature word (wanted :: word.erase wanted)
  | [], safe => False.elim safe
  | head :: tail, safe => by
    by_cases equal : head = wanted
    · subst head
      simpa only [List.erase_cons_head] using Exchange.refl (wanted :: tail)
    · have rest := safe.resolve_left equal
      let lifted := (pullHead signature wanted tail rest.2).prepend signature head
      simpa only [List.erase_cons, beq_iff_eq, equal, if_false, List.nil_append, List.cons_append] using
        lifted.trans (Exchange.swap [] (tail.erase wanted) head wanted rest.1)

theorem pullHead_front (signature : Op → Interface Slot) (wanted : Op) (tail : List Op)
    (safe : AccessibleHead signature wanted (wanted :: tail)) :
    HEq (pullHead signature wanted (wanted :: tail) safe) (Exchange.refl (signature := signature) (wanted :: tail)) := by
  simp only [pullHead]
  exact cast_heq _ _

/-- Deletion respects formal inverse and composition by construction. -/
theorem Exchange.eraseData_trans (signature : Op → Interface Slot) (wanted : Op) {a b c : List Op}
    (p : Exchange signature a b) (q : Exchange signature b c) :
    (p.trans q).eraseData signature wanted = (p.eraseData signature wanted).trans (q.eraseData signature wanted) := rfl

theorem Exchange.eraseData_symm (signature : Op → Interface Slot) (wanted : Op) {a b : List Op}
    (p : Exchange signature a b) :
    (p.symm).eraseData signature wanted = (p.eraseData signature wanted).symm := rfl

theorem pullHead_sound (signature : Op → Interface Slot) (wanted : Op) (word : List Op)
    (safe : AccessibleHead signature wanted word) (world : Kernels signature Value) (store : Store Slot Value) :
    execute signature world word store = execute signature world (wanted :: word.erase wanted) store :=
  (pullHead signature wanted word safe).sound signature world store

end CryptoOracle.StatefulDiagram
