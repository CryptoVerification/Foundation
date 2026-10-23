import Foundation.Crypto.Semantics.Oracle.StatefulDiagramExchange

/-! The backward analysis respects the ACTUAL checked stateful exchange rule.
This is equality of computed input/obligation sets, not higher coherence of
parallel Exchange paths and not invariance under arbitrary semantic equality. -/
namespace CryptoOracle.StatefulDiagram
open Foundation.Probability
variable {Slot Op : Type} [DecidableEq Slot]

omit [DecidableEq Slot] in
private theorem independent_symm (signature : Op → Interface Slot) (first second : Op)
    (safe : Independent signature first second) : Independent signature second first :=
  ⟨safe.2.1, safe.1, safe.2.2.symm⟩

/-- An independent neighbour cannot change whether a box is relevant. -/
theorem relevant_after_independent (signature : Op → Interface Slot) (first second : Op)
    (needed : Finset Slot) (safe : Independent signature first second) :
    Disjoint (signature first).writes (neededBefore signature second needed) ↔
      Disjoint (signature first).writes needed := by
  classical
  rcases safe with ⟨reads, _, writes⟩
  by_cases skip : Disjoint (signature second).writes needed
  · simp only [neededBefore, if_pos skip]
  · simp only [neededBefore, if_neg skip, Finset.disjoint_union_right]
    constructor
    · rintro ⟨remaining, _⟩
      apply Finset.disjoint_left.mpr
      intro slot member relevant
      have outside : slot ∉ (signature second).writes := fun other => Finset.disjoint_left.mp writes member other
      exact Finset.disjoint_left.mp remaining member (Finset.mem_sdiff.mpr ⟨relevant, outside⟩)
    · intro disjoint
      exact ⟨disjoint.mono_right Finset.sdiff_subset, reads⟩

/-- Backwards input requirements commute for checked independent boxes. -/
theorem neededBefore_commute (signature : Op → Interface Slot) (first second : Op)
    (needed : Finset Slot) (safe : Independent signature first second) :
    neededBefore signature first (neededBefore signature second needed) =
      neededBefore signature second (neededBefore signature first needed) := by
  classical
  have firstRelevant := relevant_after_independent signature first second needed safe
  have secondRelevant := relevant_after_independent signature second first needed (independent_symm signature first second safe)
  by_cases skipFirst : Disjoint (signature first).writes needed <;>
    by_cases skipSecond : Disjoint (signature second).writes needed
  · simp only [neededBefore, if_pos skipFirst, if_pos skipSecond]
  · have skip := firstRelevant.mpr skipFirst
    rw [show neededBefore signature first (neededBefore signature second needed) = neededBefore signature second needed from if_pos skip]
    rw [show neededBefore signature first needed = needed from if_pos skipFirst]
  · have skip := secondRelevant.mpr skipSecond
    rw [show neededBefore signature second (neededBefore signature first needed) = neededBefore signature first needed from if_pos skip]
    rw [show neededBefore signature second needed = needed from if_pos skipSecond]
  · have useFirst : ¬ Disjoint (signature first).writes (neededBefore signature second needed) :=
      fun skip => skipFirst (firstRelevant.mp skip)
    have useSecond : ¬ Disjoint (signature second).writes (neededBefore signature first needed) :=
      fun skip => skipSecond (secondRelevant.mp skip)
    rw [show neededBefore signature first (neededBefore signature second needed) =
      (neededBefore signature second needed \ (signature first).writes) ∪ (signature first).reads from if_neg useFirst]
    rw [show neededBefore signature second (neededBefore signature first needed) =
      (neededBefore signature first needed \ (signature second).writes) ∪ (signature second).reads from if_neg useSecond]
    rw [show neededBefore signature second needed = (needed \ (signature second).writes) ∪ (signature second).reads from if_neg skipSecond,
      show neededBefore signature first needed = (needed \ (signature first).writes) ∪ (signature first).reads from if_neg skipFirst]
    ext slot
    simp only [Finset.mem_union, Finset.mem_sdiff]
    have leftRead : slot ∈ (signature first).reads → slot ∉ (signature second).writes :=
      fun member other => Finset.disjoint_left.mp safe.2.1 other member
    have rightRead : slot ∈ (signature second).reads → slot ∉ (signature first).writes :=
      fun member other => Finset.disjoint_left.mp safe.1 other member
    tauto

theorem dependencies_append (signature : Op → Interface Slot) (first second : List Op) (needed : Finset Slot) :
    dependencies signature (first ++ second) needed = dependencies signature first (dependencies signature second needed) := by
  induction first with
  | nil => rfl
  | cons op rest ih => simp only [List.cons_append, dependencies, ih]

theorem required_append [DecidableEq Op] (signature : Op → Interface Slot) (first second : List Op) (needed : Finset Slot) :
    required signature (first ++ second) needed =
      required signature first (dependencies signature second needed) ∪ required signature second needed := by
  induction first with
  | nil => simp only [List.nil_append, required, Finset.empty_union]
  | cons op rest ih =>
      simp only [List.cons_append, required, dependencies_append, ih]
      split <;> simp only [Finset.insert_union]

theorem required_exchange [DecidableEq Op] (signature : Op → Interface Slot)
    (first second : Op) (future : List Op) (needed : Finset Slot) (safe : Independent signature first second) :
    required signature (first :: second :: future) needed = required signature (second :: first :: future) needed := by
  have firstRelevant := relevant_after_independent signature first second (dependencies signature future needed) safe
  have secondRelevant := relevant_after_independent signature second first (dependencies signature future needed)
    (independent_symm signature first second safe)
  simp only [required, dependencies]
  simp only [firstRelevant, secondRelevant]
  by_cases skipFirst : Disjoint (signature first).writes (dependencies signature future needed) <;>
    by_cases skipSecond : Disjoint (signature second).writes (dependencies signature future needed) <;>
    simp only [skipFirst, skipSecond, if_true, if_false, Finset.insert_comm]

/-- Every generated exchange path preserves the backwards input interface. -/
theorem Exchange.dependencies_eq (signature : Op → Interface Slot) {one two : List Op}
    (certificate : Exchange signature one two) (needed : Finset Slot) :
    dependencies signature one needed = dependencies signature two needed := by
  induction certificate with
  | refl => rfl
  | swap past future first second accepted =>
      simp only [dependencies_append, dependencies]
      rw [neededBefore_commute signature first second (dependencies signature future needed) (of_decide_eq_true accepted)]
  | symm certificate ih => exact ih.symm
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- The generated local-law IDs are independent of the chosen checked order. -/
theorem Exchange.required_eq [DecidableEq Op] (signature : Op → Interface Slot) {one two : List Op}
    (certificate : Exchange signature one two) (needed : Finset Slot) :
    required signature one needed = required signature two needed := by
  induction certificate with
  | refl => rfl
  | swap past future first second accepted =>
      have safe : Independent signature first second := of_decide_eq_true accepted
      have inputs : dependencies signature [first, second] (dependencies signature future needed) =
          dependencies signature [second, first] (dependencies signature future needed) :=
        neededBefore_commute signature first second (dependencies signature future needed) safe
      have leaves := required_exchange signature first second [] (dependencies signature future needed) safe
      change required signature [first, second] (dependencies signature future needed) =
        required signature [second, first] (dependencies signature future needed) at leaves
      simp only [required_append]
      rw [inputs, leaves]
  | symm certificate ih => exact ih.symm
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem Exchange.obligations_eq [DecidableEq Op] (signature : Op → Interface Slot) {one two : List Op}
    (certificate : Exchange signature one two) (needed : Finset Slot) (changed : Finset Op) :
    obligations signature one needed changed = obligations signature two needed changed := by
  simp only [obligations, certificate.required_eq signature needed]

/-- Carry the old local equality proofs to any checked reordering. -/
theorem Exchange.transportRepair [DecidableEq Op] {Value : Type} (signature : Op → Interface Slot)
    {one two : List Op} (certificate : Exchange signature one two)
    (needed : Finset Slot) (changed : Finset Op) (left right : Kernels signature Value)
    (localLaws : ∀ op ∈ obligations signature one needed changed, left op = right op) :
    ∀ op ∈ obligations signature two needed changed, left op = right op := by
  intro op member
  apply localLaws op
  rw [certificate.obligations_eq signature needed changed]
  exact member

/-- The same fresh laws repair the game after any checked exchange path. -/
theorem Exchange.repair_reordered [DecidableEq Op] {Value : Type} (signature : Op → Interface Slot)
    {one two : List Op} (certificate : Exchange signature one two)
    (needed : Finset Slot) (changed : Finset Op) (left right : Kernels signature Value)
    (unchanged : ∀ op ∉ changed, left op = right op)
    (localLaws : ∀ op ∈ obligations signature one needed changed, left op = right op)
    (store : Store Slot Value) :
    (execute signature left two store).map (view needed) = (execute signature right two store).map (view needed) :=
  repair_sound signature left right two needed changed store unchanged
    (certificate.transportRepair signature needed changed left right localLaws)

/-- The old local laws also connect the opposite corners of the repair /
reorder square; all occurrences use the same actual initial store. -/
theorem Exchange.repair_across [DecidableEq Op] {Value : Type} (signature : Op → Interface Slot)
    {one two : List Op} (certificate : Exchange signature one two)
    (needed : Finset Slot) (changed : Finset Op) (left right : Kernels signature Value)
    (unchanged : ∀ op ∉ changed, left op = right op)
    (localLaws : ∀ op ∈ obligations signature one needed changed, left op = right op)
    (store : Store Slot Value) :
    (execute signature left one store).map (view needed) = (execute signature right two store).map (view needed) := by
  calc
    _ = (execute signature right one store).map (view needed) :=
      repair_sound signature left right one needed changed store unchanged localLaws
    _ = _ := congrArg (PMF.map (view needed)) (certificate.sound signature right store)

end CryptoOracle.StatefulDiagram
