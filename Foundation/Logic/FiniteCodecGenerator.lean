import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange

/-! Construct a finite byte-style codec from a forward declaration alone.
The inverse is an executable first-preimage search. Validation checks its
roundtrip on every public value; no supplied inverse or bijectivity proof is
an input to compile. Complexity is not claimed to be linear. -/
namespace Foundation.Logic.FiniteCodecGenerator
variable {width : Nat}

def inverse (encoder : Fin (width + 1) → Fin (width + 1)) (stored : Fin (width + 1)) : Fin (width + 1) :=
  (((List.finRange (width + 1)).find? fun value => encoder value == stored)).getD 0

def validates (encoder : Fin (width + 1) → Fin (width + 1)) : Bool :=
  (List.finRange (width + 1)).all fun value => inverse encoder (encoder value) == value

theorem validates_iff (encoder : Fin (width + 1) → Fin (width + 1)) :
    validates encoder = true ↔ Function.LeftInverse (inverse encoder) encoder := by
  simp [validates, List.all_eq_true, Function.LeftInverse]

theorem inverse_of_injective (encoder : Fin (width + 1) → Fin (width + 1))
    (injective : Function.Injective encoder) (value : Fin (width + 1)) : inverse encoder (encoder value) = value := by
  have foundSome : ((List.finRange (width + 1)).find? fun candidate => encoder candidate == encoder value).isSome :=
    List.find?_isSome.mpr ⟨value, by simp, by simp⟩
  cases found : (List.finRange (width + 1)).find? (fun candidate => encoder candidate == encoder value) with
  | none => simp [found] at foundSome
  | some candidate =>
      have equal : encoder candidate = encoder value := by simpa using List.find?_some found
      simpa only [inverse, found, Option.getD_some] using injective equal

theorem validates_bijective (encoder : Fin (width + 1) → Fin (width + 1)) :
    validates encoder = true ↔ Function.Bijective encoder := by
  constructor
  · intro checked
    have injective := ((validates_iff encoder).mp checked).injective
    exact ⟨injective, Finite.surjective_of_injective injective⟩
  · intro bijective
    exact (validates_iff encoder).mpr (inverse_of_injective encoder bijective.1)

def checkedEquiv (encoder : Fin (width + 1) → Fin (width + 1)) (checked : validates encoder = true) :
    Fin (width + 1) ≃ Fin (width + 1) where
  toFun := encoder
  invFun := inverse encoder
  left_inv := (validates_iff encoder).mp checked
  right_inv := by
    intro stored
    obtain ⟨value, rfl⟩ := ((validates_bijective encoder).mp checked).2 stored
    rw [(validates_iff encoder).mp checked value]

def compile (encoder : Fin (width + 1) → Fin (width + 1)) : Option (Fin (width + 1) ≃ Fin (width + 1)) :=
  if checked : validates encoder = true then some (checkedEquiv encoder checked) else none

theorem compile_complete (encoder : Fin (width + 1) → Fin (width + 1)) :
    (compile encoder).isSome = true ↔ Function.Bijective encoder := by
  rw [← validates_bijective encoder]
  by_cases checked : validates encoder = true <;> simp [compile, checked]

theorem compile_spec (encoder : Fin (width + 1) → Fin (width + 1)) (codec : Fin (width + 1) ≃ Fin (width + 1))
    (compiled : compile encoder = some codec) :
    (∀ value, codec value = encoder value) ∧ (∀ stored, codec.symm stored = inverse encoder stored) := by
  unfold compile at compiled
  split at compiled
  · cases compiled
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · contradiction

theorem decoder_exists_iff (encoder : Fin (width + 1) → Fin (width + 1)) :
    (∃ decode : Fin (width + 1) → Fin (width + 1), Function.LeftInverse decode encoder) ↔ validates encoder = true := by
  constructor
  · rintro ⟨decode, correct⟩
    exact (validates_iff encoder).mpr (inverse_of_injective encoder correct.injective)
  · intro checked
    exact ⟨inverse encoder, (validates_iff encoder).mp checked⟩

theorem collision_rejected (encoder : Fin (width + 1) → Fin (width + 1))
    (left right : Fin (width + 1)) (different : left ≠ right) (collision : encoder left = encoder right) :
    compile encoder = none := by
  unfold compile
  split
  · rename_i checked
    exact False.elim (different (((validates_bijective encoder).mp checked).1 collision))
  · rfl

variable {Index : Type} [Fintype Index]

def validatesFamily (encoder : Index → Fin (width + 1) → Fin (width + 1)) : Bool :=
  decide (∀ index, validates (encoder index) = true)

def compileFamily (encoder : Index → Fin (width + 1) → Fin (width + 1)) :
    Option (Index → Fin (width + 1) ≃ Fin (width + 1)) :=
  if checked : ∀ index, validates (encoder index) = true then
    some (fun index => checkedEquiv (encoder index) (checked index)) else none

theorem family_complete (encoder : Index → Fin (width + 1) → Fin (width + 1)) :
    (compileFamily encoder).isSome = true ↔ ∀ index, Function.Bijective (encoder index) := by
  have pointwise : (∀ index, Function.Bijective (encoder index)) ↔
      ∀ index, validates (encoder index) = true :=
    forall_congr' (fun index => (validates_bijective (encoder index)).symm)
  rw [pointwise]
  by_cases checked : ∀ index, validates (encoder index) = true <;> simp [compileFamily, checked]

theorem family_spec (encoder : Index → Fin (width + 1) → Fin (width + 1))
    (codecs : Index → Fin (width + 1) ≃ Fin (width + 1)) (compiled : compileFamily encoder = some codecs) :
    ∀ index value, codecs index value = encoder index value := by
  unfold compileFamily at compiled
  split at compiled
  · cases compiled
    exact fun _ _ => rfl
  · contradiction

theorem family_inverse_spec (encoder : Index → Fin (width + 1) → Fin (width + 1))
    (codecs : Index → Fin (width + 1) ≃ Fin (width + 1)) (compiled : compileFamily encoder = some codecs) :
    ∀ index stored, (codecs index).symm stored = inverse (encoder index) stored := by
  unfold compileFamily at compiled
  split at compiled
  · cases compiled
    exact fun _ _ => rfl
  · contradiction

end Foundation.Logic.FiniteCodecGenerator
