import Foundation.Logic.FiniteCodecRestriction

/-! An incremental compiler. A previously checked declaration and a proof that
unedited rows agree are reused. Only the edited intersection is validated at
runtime. Proof inputs are erased; initial certification and proving agreement
are separate costs, not included in the incremental check. -/
namespace Foundation.Logic.FiniteCodecRepair
open FiniteCodecGenerator
variable {Index : Type} [DecidableEq Index] {width : Nat}

private theorem checked_all (used changed : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1))
    (accepted : (FiniteCodecRestriction.compile used left).isSome = true)
    (unchanged : ∀ index ∈ used, index ∉ changed → left index = right index)
    (checked : ∀ index ∈ used ∩ changed, validates (right index) = true) :
    ∀ index ∈ used, validates (right index) = true := by
  have newAccepted := (FiniteCodecRestriction.repair_complete used changed left right accepted unchanged).mpr
    (fun index included => (validates_bijective (right index)).mp (checked index included))
  intro index included
  exact (validates_bijective (right index)).mpr
    ((FiniteCodecRestriction.complete used right).mp newAccepted index included)

def compile (used changed : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1))
    (accepted : (FiniteCodecRestriction.compile used left).isSome = true)
    (unchanged : ∀ index ∈ used, index ∉ changed → left index = right index) :
    Option (Index → Fin (width + 1) ≃ Fin (width + 1)) :=
  if checked : ∀ index ∈ used ∩ changed, validates (right index) = true then
    some (fun index => if included : index ∈ used then
      checkedEquiv (right index) (checked_all used changed left right accepted unchanged checked index included)
      else Equiv.refl _) else none

theorem compile_eq_full (used changed : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1))
    (accepted : (FiniteCodecRestriction.compile used left).isSome = true)
    (unchanged : ∀ index ∈ used, index ∉ changed → left index = right index) :
    compile used changed left right accepted unchanged = FiniteCodecRestriction.compile used right := by
  unfold compile FiniteCodecRestriction.compile
  by_cases checked : ∀ index ∈ used ∩ changed, validates (right index) = true
  · rw [dif_pos checked, dif_pos (checked_all used changed left right accepted unchanged checked)]
  · have failed : ¬ ∀ index ∈ used, validates (right index) = true := by
      intro allChecked
      exact checked (fun index included => allChecked index (Finset.mem_inter.mp included).1)
    rw [dif_neg checked, dif_neg failed]

theorem complete (used changed : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1))
    (accepted : (FiniteCodecRestriction.compile used left).isSome = true)
    (unchanged : ∀ index ∈ used, index ∉ changed → left index = right index) :
    (compile used changed left right accepted unchanged).isSome = true ↔
      ∀ index ∈ used ∩ changed, Function.Bijective (right index) := by
  rw [compile_eq_full]
  exact FiniteCodecRestriction.repair_complete used changed left right accepted unchanged

/-- Runtime acceptance depends only on the edited intersection. -/
theorem acceptance (used changed : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1))
    (accepted : (FiniteCodecRestriction.compile used left).isSome = true)
    (unchanged : ∀ index ∈ used, index ∉ changed → left index = right index) :
    (compile used changed left right accepted unchanged).isSome =
      FiniteCodecRestriction.validates (used ∩ changed) right := by
  unfold compile FiniteCodecRestriction.validates
  split <;> simp_all

end Foundation.Logic.FiniteCodecRepair
