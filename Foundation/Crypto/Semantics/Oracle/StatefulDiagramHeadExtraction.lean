import Foundation.Crypto.Semantics.Oracle.StatefulDiagramHigher

/-! A checked head-extraction primitive for future trace normalization.
It scans a word, never enumerates exchange paths, and returns explicit path
 data. Canonical normalization and higher coherence are separate obligations. -/
namespace CryptoOracle.StatefulDiagram
variable {Slot Op Value : Type} [DecidableEq Slot]

/-- A word and a concrete checked exchange path exposing the selected label. -/
structure HeadExtraction (signature : Op → Interface Slot) (wanted : Op) (word : List Op) where
  rest : List Op
  path : Exchange signature word (wanted :: rest)

/-- Stop at the first equal label; cross preceding boxes only after checking
read/write independence. No equality test on probabilistic kernels is used. -/
def exposeHead [DecidableEq Op] (signature : Op → Interface Slot) (wanted : Op) :
    (word : List Op) → Option (HeadExtraction signature wanted word)
  | [] => none
  | head :: tail =>
    if equal : head = wanted then by
      subst head
      exact some ⟨tail, .refl _⟩
    else if accepted : checkExchange signature head wanted = true then
      match exposeHead signature wanted tail with
      | none => none
      | some result =>
        let lifted : Exchange signature (head :: tail) (head :: wanted :: result.rest) := by
          simpa only [List.singleton_append, List.append_nil] using
            result.path.whisker signature [head] []
        let crossed : Exchange signature (head :: wanted :: result.rest) (wanted :: head :: result.rest) :=
          Exchange.swap [] result.rest head wanted accepted
        some ⟨head :: result.rest, lifted.trans crossed⟩
    else none

/-- Declarative success criterion, independent of generated proof data. -/
def AccessibleHead [DecidableEq Op] (signature : Op → Interface Slot) (wanted : Op) : List Op → Prop
  | [] => False
  | head :: tail => head = wanted ∨
      (checkExchange signature head wanted = true ∧ AccessibleHead signature wanted tail)

theorem exposeHead_success_iff [DecidableEq Op] (signature : Op → Interface Slot) (wanted : Op)
    (word : List Op) : (exposeHead signature wanted word).isSome = true ↔
      AccessibleHead signature wanted word := by
  induction word with
  | nil => simp [exposeHead, AccessibleHead]
  | cons head tail ih =>
    by_cases equal : head = wanted
    · subst head
      simp [exposeHead, AccessibleHead]
    · by_cases accepted : checkExchange signature head wanted = true
      · simp only [AccessibleHead, equal, false_or, accepted, true_and]
        rw [← ih]
        cases result : exposeHead signature wanted tail <;> simp [exposeHead, equal, accepted, result]
      · simp [exposeHead, AccessibleHead, equal, accepted]

theorem checkExchange_reverse (signature : Op → Interface Slot) (a b : Op)
    (accepted : checkExchange signature a b = true) : checkExchange signature b a = true := by
  simp only [checkExchange, decide_eq_true_eq] at accepted ⊢
  exact ⟨accepted.2.1, accepted.1, accepted.2.2.symm⟩

private theorem accessible_swap [DecidableEq Op] (signature : Op → Interface Slot) (wanted a b : Op)
    (rest : List Op) (accepted : checkExchange signature a b = true) :
    AccessibleHead signature wanted (a :: b :: rest) ↔
      AccessibleHead signature wanted (b :: a :: rest) := by
  have reversed := checkExchange_reverse signature a b accepted
  by_cases first : a = wanted
  · subst a
    simp [AccessibleHead, reversed]
  · by_cases second : b = wanted
    · subst b
      simp [AccessibleHead, accepted]
    · simp only [AccessibleHead, first, second, false_or]
      tauto

private theorem accessible_prefix [DecidableEq Op] (signature : Op → Interface Slot) (wanted : Op)
    (past one two : List Op) (same : AccessibleHead signature wanted one ↔ AccessibleHead signature wanted two) :
    AccessibleHead signature wanted (past ++ one) ↔ AccessibleHead signature wanted (past ++ two) := by
  induction past with
  | nil => exact same
  | cons head tail ih => simp only [List.cons_append, AccessibleHead, ih]

/-- Accessibility is invariant under arbitrary checked exchange paths,
including inverse paths and repeated operation labels. -/
theorem Exchange.accessibleHead_iff [DecidableEq Op] (signature : Op → Interface Slot) (wanted : Op)
    {one two : List Op} (path : Exchange signature one two) :
    AccessibleHead signature wanted one ↔ AccessibleHead signature wanted two := by
  induction path with
  | refl => rfl
  | swap past future a b accepted =>
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      accessible_prefix signature wanted past (a :: b :: future) (b :: a :: future)
        (accessible_swap signature wanted a b future accepted)
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second

/-- The scan succeeds exactly when some checked exchange path can expose the
requested label. This is completeness for the exchange syntax, not for all
semantically equivalent probabilistic programs. -/
theorem exposeHead_complete [DecidableEq Op] (signature : Op → Interface Slot) (wanted : Op)
    (word : List Op) : (exposeHead signature wanted word).isSome = true ↔
      ∃ rest, Nonempty (Exchange signature word (wanted :: rest)) := by
  constructor
  · intro accepted
    cases result : exposeHead signature wanted word with
    | none => simp [result] at accepted
    | some extracted => exact ⟨extracted.rest, ⟨extracted.path⟩⟩
  · rintro ⟨rest, ⟨path⟩⟩
    apply (exposeHead_success_iff signature wanted word).mpr
    apply (path.accessibleHead_iff signature wanted).mpr
    simp [AccessibleHead]

theorem Exchange.length_eq (signature : Op → Interface Slot) {one two : List Op}
    (path : Exchange signature one two) : one.length = two.length := by
  induction path with
  | refl => rfl
  | swap => simp
  | symm _ ih => exact ih.symm
  | trans _ _ ihOne ihTwo => exact ihOne.trans ihTwo

theorem HeadExtraction.length (signature : Op → Interface Slot) (wanted : Op) (word : List Op)
    (result : HeadExtraction signature wanted word) : word.length = result.rest.length + 1 :=
  result.path.length_eq signature

theorem HeadExtraction.sound (signature : Op → Interface Slot) (wanted : Op) (word : List Op)
    (result : HeadExtraction signature wanted word) (world : Kernels signature Value) (store : Store Slot Value) :
    execute signature world word store = execute signature world (wanted :: result.rest) store :=
  result.path.sound signature world store

end CryptoOracle.StatefulDiagram
