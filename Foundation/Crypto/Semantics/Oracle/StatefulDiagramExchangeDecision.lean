import Foundation.Crypto.Semantics.Oracle.StatefulDiagramHeadExtraction

/-! A complete proof-producing decision procedure for the checked exchange
syntax, using recursive head extraction rather than enumeration of paths.
This decides the generated trace equivalence, not arbitrary semantic equality,
and does not yet identify all parallel proof terms by higher cells. -/
namespace CryptoOracle.StatefulDiagram
variable {Slot Op Value : Type} [DecidableEq Slot] [DecidableEq Op]

/-- Removing the first occurrence of a label preserves checked exchange
reachability. In particular this yields cancellation of a common head. -/
theorem Exchange.erase (signature : Op → Interface Slot) (wanted : Op) {one two : List Op}
    (path : Exchange signature one two) :
    Nonempty (Exchange signature (one.erase wanted) (two.erase wanted)) := by
  induction path with
  | refl => exact ⟨.refl _⟩
  | swap past future a b accepted =>
    by_cases member : wanted ∈ past
    · simpa only [List.append_assoc, List.erase_append_left _ member] using
        (show Nonempty (Exchange signature (past.erase wanted ++ [a, b] ++ future)
          (past.erase wanted ++ [b, a] ++ future)) from ⟨.swap _ _ a b accepted⟩)
    · simp only [List.append_assoc, List.erase_append_right _ member, List.cons_append, List.nil_append]
      by_cases first : a = wanted
      · subst a
        by_cases second : b = wanted
        · subst b
          exact ⟨.refl _⟩
        · simp only [List.erase_cons_head, List.erase_cons, beq_iff_eq, second, if_false]
          exact ⟨.refl _⟩
      · by_cases second : b = wanted
        · subst b
          simp only [List.erase_cons_head, List.erase_cons, beq_iff_eq, first, if_false]
          exact ⟨.refl _⟩
        · simp only [List.erase_cons, beq_iff_eq, first, second, if_false]
          exact ⟨by simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            Exchange.swap past (future.erase wanted) a b accepted⟩
  | symm _ ih =>
    obtain ⟨path⟩ := ih
    exact ⟨path.symm⟩
  | trans _ _ first second =>
    obtain ⟨p⟩ := first
    obtain ⟨q⟩ := second
    exact ⟨p.trans q⟩

theorem Exchange.cancel_head (signature : Op → Interface Slot) (head : Op) {one two : List Op}
    (path : Exchange signature (head :: one) (head :: two)) : Nonempty (Exchange signature one two) := by
  simpa only [List.erase_cons_head] using path.erase signature head

/-- Target-directed path construction. Each recursion removes one target
letter; there is no search over intermediate execution paths. -/
def alignExchange (signature : Op → Interface Slot) : (one two : List Op) → Option (Exchange signature one two)
  | [], [] => some (.refl [])
  | _ :: _, [] => none
  | one, wanted :: tail =>
    match exposeHead signature wanted one with
    | none => none
    | some extracted =>
      match alignExchange signature extracted.rest tail with
      | none => none
      | some restPath =>
        let lifted : Exchange signature (wanted :: extracted.rest) (wanted :: tail) := by
          simpa only [List.singleton_append, List.append_nil] using restPath.whisker signature [wanted] []
        some (extracted.path.trans lifted)

/-- Completeness is for all finite raw Exchange paths, including reversal,
composition, repetitions and accepted read-only self-exchange. -/
theorem alignExchange_complete (signature : Op → Interface Slot) (one two : List Op) :
    (alignExchange signature one two).isSome = true ↔ Nonempty (Exchange signature one two) := by
  constructor
  · intro accepted
    cases result : alignExchange signature one two with
    | none => simp [result] at accepted
    | some path => exact ⟨path⟩
  · rintro ⟨path⟩
    induction two generalizing one with
    | nil =>
      have length := path.length_eq signature
      have equal : one = [] := List.length_eq_zero_iff.mp length
      subst one
      rfl
    | cons wanted tail ih =>
      have accessible := (exposeHead_complete signature wanted one).mpr ⟨tail, ⟨path⟩⟩
      cases result : exposeHead signature wanted one with
      | none => simp [result] at accessible
      | some extracted =>
        have restReach := (extracted.path.symm.trans path).cancel_head signature wanted
        obtain ⟨restPath⟩ := restReach
        have restAccepted := ih extracted.rest restPath
        cases restResult : alignExchange signature extracted.rest tail with
        | none => simp [restResult] at restAccepted
        | some residual => simp [alignExchange, result, restResult]

/-- Every generated certificate preserves the full store distribution for
all typed probabilistic kernels and every initial state. -/
theorem alignExchange_sound (signature : Op → Interface Slot) (one two : List Op)
    (world : Kernels signature Value) (store : Store Slot Value)
    (accepted : (alignExchange signature one two).isSome = true) :
    execute signature world one store = execute signature world two store := by
  obtain ⟨path⟩ := (alignExchange_complete signature one two).mp accepted
  exact path.sound signature world store

end CryptoOracle.StatefulDiagram
