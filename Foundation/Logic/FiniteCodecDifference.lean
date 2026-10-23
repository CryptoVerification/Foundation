import Foundation.Logic.FiniteCodecRepair

/-! Compute the exact changed rows of two finite-output declarations on a
supplied finite scope. This compares ALL public values at each scoped row;
it does not inspect just reachable responses or infer arbitrary relations. -/
namespace Foundation.Logic.FiniteCodecDifference
variable {Index : Type} [DecidableEq Index] {width : Nat}

def changed (used : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1)) : Finset Index :=
  used.filter (fun index => left index ≠ right index)

omit [DecidableEq Index] in
theorem mem_changed (used : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1)) (index : Index) :
    index ∈ changed used left right ↔ index ∈ used ∧ left index ≠ right index := by
  exact Finset.mem_filter

omit [DecidableEq Index] in
theorem changed_subset (used : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1)) :
    changed used left right ⊆ used := Finset.filter_subset _ _

omit [DecidableEq Index] in
theorem unchanged (used : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1)) :
    ∀ index ∈ used, index ∉ changed used left right → left index = right index := by
  intro index included untouched
  by_contra different
  exact untouched ((mem_changed used left right index).mpr ⟨included, different⟩)

omit [DecidableEq Index] in
/-- Every sound declared change set contains the computed exact difference. -/
theorem minimal (used candidate : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1))
    (sound : ∀ index ∈ used, index ∉ candidate → left index = right index) :
    changed used left right ⊆ candidate := by
  intro index included
  obtain ⟨member, different⟩ := (mem_changed used left right index).mp included
  by_contra outside
  exact different (sound index member outside)

def compile (used : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1))
    (accepted : (FiniteCodecRestriction.compile used left).isSome = true) :=
  FiniteCodecRepair.compile used (changed used left right) left right accepted (unchanged used left right)

theorem compile_eq_full (used : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1))
    (accepted : (FiniteCodecRestriction.compile used left).isSome = true) :
    compile used left right accepted = FiniteCodecRestriction.compile used right :=
  FiniteCodecRepair.compile_eq_full used (changed used left right) left right accepted (unchanged used left right)

theorem complete (used : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1))
    (accepted : (FiniteCodecRestriction.compile used left).isSome = true) :
    (compile used left right accepted).isSome = true ↔
      ∀ index ∈ changed used left right, Function.Bijective (right index) := by
  unfold compile
  rw [FiniteCodecRepair.complete, Finset.inter_eq_right.mpr (changed_subset used left right)]

end Foundation.Logic.FiniteCodecDifference
