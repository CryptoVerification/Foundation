import Foundation.Logic.FiniteCodecGenerator

/-! Validate only a supplied finite scope. Outside that scope the generated
total codec is identity, not the unchecked forward declaration. An operational
use must separately prove that ignored entries cannot be inspected or recoded. -/
namespace Foundation.Logic.FiniteCodecRestriction
open FiniteCodecGenerator
variable {Index : Type} [DecidableEq Index] {width : Nat}

def validates (used : Finset Index) (encoder : Index → Fin (width + 1) → Fin (width + 1)) : Bool :=
  decide (∀ index ∈ used, FiniteCodecGenerator.validates (encoder index) = true)

def compile (used : Finset Index) (encoder : Index → Fin (width + 1) → Fin (width + 1)) :
    Option (Index → Fin (width + 1) ≃ Fin (width + 1)) :=
  if checked : ∀ index ∈ used, FiniteCodecGenerator.validates (encoder index) = true then
    some (fun index => if included : index ∈ used then
      checkedEquiv (encoder index) (checked index included) else Equiv.refl _) else none

theorem complete (used : Finset Index) (encoder : Index → Fin (width + 1) → Fin (width + 1)) :
    (compile used encoder).isSome = true ↔ ∀ index ∈ used, Function.Bijective (encoder index) := by
  have pointwise : (∀ index ∈ used, Function.Bijective (encoder index)) ↔
      ∀ index ∈ used, FiniteCodecGenerator.validates (encoder index) = true := by
    simp only [validates_bijective]
  rw [pointwise]
  by_cases checked : ∀ index ∈ used, FiniteCodecGenerator.validates (encoder index) = true <;>
    simp [compile, checked]

theorem forward_spec (used : Finset Index) (encoder : Index → Fin (width + 1) → Fin (width + 1))
    (family : Index → Fin (width + 1) ≃ Fin (width + 1)) (compiled : compile used encoder = some family)
    (index : Index) (included : index ∈ used) (value : Fin (width + 1)) : family index value = encoder index value := by
  unfold compile at compiled
  split at compiled
  · cases compiled
    simp only [dif_pos included, checkedEquiv]
    rfl
  · contradiction

theorem inverse_spec (used : Finset Index) (encoder : Index → Fin (width + 1) → Fin (width + 1))
    (family : Index → Fin (width + 1) ≃ Fin (width + 1)) (compiled : compile used encoder = some family)
    (index : Index) (included : index ∈ used) (stored : Fin (width + 1)) :
    (family index).symm stored = FiniteCodecGenerator.inverse (encoder index) stored := by
  unfold compile at compiled
  split at compiled
  · cases compiled
    simp only [dif_pos included, checkedEquiv]
    rfl
  · contradiction

theorem outside_spec (used : Finset Index) (encoder : Index → Fin (width + 1) → Fin (width + 1))
    (family : Index → Fin (width + 1) ≃ Fin (width + 1)) (compiled : compile used encoder = some family)
    (index : Index) (outside : index ∉ used) : family index = Equiv.refl _ := by
  unfold compile at compiled
  split at compiled
  · cases compiled
    simp only [dif_neg outside]
  · contradiction

/-- An edit outside the checked scope preserves the entire generated artifact,
including rejection and the identity completion outside the scope. -/
theorem compile_congr (used : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1))
    (agree : ∀ index ∈ used, left index = right index) :
    compile used left = compile used right := by
  have checks : (∀ index ∈ used, FiniteCodecGenerator.validates (left index) = true) ↔
      ∀ index ∈ used, FiniteCodecGenerator.validates (right index) = true := by
    constructor <;> intro checked index included
    · rw [← agree index included]
      exact checked index included
    · rw [agree index included]
      exact checked index included
  unfold compile
  by_cases checked : ∀ index ∈ used, FiniteCodecGenerator.validates (left index) = true
  · rw [dif_pos checked, dif_pos (checks.mp checked)]
    apply congrArg some
    funext index
    by_cases included : index ∈ used
    · apply Equiv.ext
      intro value
      simp only [dif_pos included, checkedEquiv]
      exact congrFun (agree index included) value
    · simp only [dif_neg included]
  · rw [dif_neg checked, dif_neg (fun other => checked (checks.mpr other))]

/-- An accepted old declaration needs new bijectivity proofs only on the
intersection of the checked scope and the declared set of edits. -/
theorem repair_complete (used changed : Finset Index)
    (left right : Index → Fin (width + 1) → Fin (width + 1))
    (accepted : (compile used left).isSome = true)
    (unchanged : ∀ index ∈ used, index ∉ changed → left index = right index) :
    (compile used right).isSome = true ↔
      ∀ index ∈ used ∩ changed, Function.Bijective (right index) := by
  rw [complete]
  constructor
  · intro checked index included
    exact checked index (Finset.mem_inter.mp included).1
  · intro checked index included
    by_cases edited : index ∈ changed
    · exact checked index (Finset.mem_inter.mpr ⟨included, edited⟩)
    · rw [← unchanged index included edited]
      exact (complete used left).mp accepted index included

end Foundation.Logic.FiniteCodecRestriction
