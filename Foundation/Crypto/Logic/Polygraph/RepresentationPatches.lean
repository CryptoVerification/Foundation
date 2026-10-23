import Foundation.Logic.FiniteCodecDifference

/-! Concrete row-replacement paths and elementary exchange diagrams. Paths
are generated from exact declaration differences, not semantic equality
premises. Only distinct row writes commute; there is no rule for arbitrary
kernels, duplication, discard or horizontal composition in this language. -/
namespace CryptoOracle.RandomOracle.Representation.Patches
open Foundation.Logic
variable {Index : Type} [DecidableEq Index] {width : Nat}
abbrev Encoder (Index : Type) (width : Nat) := Index → Fin (width + 1) → Fin (width + 1)

structure Edit (Index : Type) (width : Nat) where
  index : Index
  forward : Fin (width + 1) → Fin (width + 1)
  deriving DecidableEq

def Edit.apply (edit : Edit Index width) (source : Encoder Index width) : Encoder Index width :=
  Function.update source edit.index edit.forward

def run : List (Edit Index width) → Encoder Index width → Encoder Index width
  | [], source => source
  | edit :: tail, source => run tail (edit.apply source)

def generate (indices : List Index) (target : Encoder Index width) : List (Edit Index width) :=
  indices.map (fun index => ⟨index, target index⟩)

omit [DecidableEq Index] in
theorem generate_length (indices : List Index) (target : Encoder Index width) :
    (generate indices target).length = indices.length := List.length_map _

theorem run_generated (indices : List Index) (source target : Encoder Index width) (index : Index) :
    run (generate indices target) source index = if index ∈ indices then target index else source index := by
  induction indices generalizing source with
  | nil => rfl
  | cons head tail ih =>
    change run (generate tail target) ((Edit.mk head (target head)).apply source) index = _
    rw [ih]
    by_cases inTail : index ∈ tail
    · simp [inTail]
    · by_cases same : index = head
      · subst index
        simp [inTail, Edit.apply]
      · simp [inTail, same, Edit.apply]

/-- An explicit enumeration makes path construction executable without
choosing an order on an arbitrary finite-set quotient. Repeated indices are
allowed but repeat the same replacement. -/
def generated (indices : List Index) (source target : Encoder Index width) : List (Edit Index width) :=
  generate (indices.filter (fun index => source index ≠ target index)) target

omit [DecidableEq Index] in
theorem generated_length (indices : List Index) (source target : Encoder Index width) :
    (generated indices source target).length = (indices.filter (fun index => source index ≠ target index)).length := by
  exact generate_length _ _

theorem generated_endpoint (indices : List Index) (source target : Encoder Index width) :
    run (generated indices source target) source = fun index => if index ∈ indices then target index else source index := by
  funext index
  rw [generated, run_generated]
  simp only [List.mem_filter, decide_eq_true_eq]
  by_cases included : index ∈ indices
  · by_cases same : source index = target index <;> simp [included, same]
  · simp [included]

theorem generated_compile_eq (indices : List Index) (source target : Encoder Index width) :
    FiniteCodecRestriction.compile indices.toFinset (run (generated indices source target) source) =
      FiniteCodecRestriction.compile indices.toFinset target := by
  apply FiniteCodecRestriction.compile_congr
  intro index included
  rw [generated_endpoint]
  simp only [List.mem_toFinset] at included
  exact if_pos included

omit [DecidableEq Index] in
theorem generated_member (indices : List Index) (source target : Encoder Index width)
    (edit : Edit Index width) (member : edit ∈ generated indices source target) :
    edit.index ∈ indices ∧ edit.forward = target edit.index := by
  obtain ⟨index, included, same⟩ := List.mem_map.mp member
  cases same
  exact ⟨(List.mem_filter.mp included).1, rfl⟩

theorem run_bijective (used : Finset Index) (word : List (Edit Index width)) (source : Encoder Index width)
    (initial : ∀ index ∈ used, Function.Bijective (source index))
    (writes : ∀ edit ∈ word, Function.Bijective edit.forward) :
    ∀ index ∈ used, Function.Bijective (run word source index) := by
  induction word generalizing source with
  | nil => exact initial
  | cons head tail ih =>
    apply ih (head.apply source)
    · intro index included
      by_cases same : index = head.index
      · subst index
        simpa only [Edit.apply, Function.update_self] using writes head (by simp)
      · simpa [Edit.apply, same] using initial index included
    · intro edit member
      exact writes edit (List.mem_cons_of_mem _ member)

/-- Successful final validation certifies every intermediate generated path
prefix, not merely the final overwritten declaration. -/
theorem generated_prefix_accepted (indices : List Index) (source target : Encoder Index width)
    (earlier later : List (Edit Index width)) (split : earlier ++ later = generated indices source target)
    (oldAccepted : (FiniteCodecRestriction.compile indices.toFinset source).isSome = true)
    (newAccepted : (FiniteCodecRestriction.compile indices.toFinset target).isSome = true) :
    (FiniteCodecRestriction.compile indices.toFinset (run earlier source)).isSome = true := by
  apply (FiniteCodecRestriction.complete _ _).mpr
  apply run_bijective indices.toFinset earlier source ((FiniteCodecRestriction.complete _ _).mp oldAccepted)
  intro edit member
  have inGenerated : edit ∈ generated indices source target := by
    rw [← split]
    exact List.mem_append_left later member
  obtain ⟨included, same⟩ := generated_member indices source target edit inGenerated
  rw [same]
  exact (FiniteCodecRestriction.complete _ _).mp newAccepted edit.index (List.mem_toFinset.mpr included)

theorem Edit.exchange (first second : Edit Index width) (different : first.index ≠ second.index)
    (source : Encoder Index width) : second.apply (first.apply source) = first.apply (second.apply source) := by
  funext index
  by_cases one : index = first.index
  · subst index
    simp [Edit.apply, different]
  · by_cases two : index = second.index
    · subst index
      simp [Edit.apply, Ne.symm different]
    · simp [Edit.apply, one, two]

inductive Cell : List (Edit Index width) → List (Edit Index width) → Type where
  | refl (word) : Cell word word
  | exchange (first second : Edit Index width) (different : first.index ≠ second.index) (tail) :
      Cell (first :: second :: tail) (second :: first :: tail)
  | cons (edit) {first second} : Cell first second → Cell (edit :: first) (edit :: second)
  | symm {first second} : Cell first second → Cell second first
  | trans {first middle last} : Cell first middle → Cell middle last → Cell first last

theorem Cell.sound {first second : List (Edit Index width)} (cell : Cell first second) (source : Encoder Index width) :
    run first source = run second source := by
  induction cell generalizing source with
  | refl => rfl
  | exchange first second different tail =>
    change run tail (second.apply (first.apply source)) = run tail (first.apply (second.apply source))
    rw [Edit.exchange first second different]
  | cons edit cell ih => exact ih (edit.apply source)
  | symm cell ih => exact (ih source).symm
  | trans first second ihFirst ihSecond => exact (ihFirst source).trans (ihSecond source)

/-- A concrete elementary exchange diagram for generated replacements.
If both indices coincide the generated words already coincide. -/
def exchangeCell (first second : Index) (tail : List Index) (target : Encoder Index width) :
    Cell (generate (first :: second :: tail) target) (generate (second :: first :: tail) target) := by
  by_cases same : first = second
  · subst second
    exact .refl _
  · exact .exchange ⟨first, target first⟩ ⟨second, target second⟩ same _

/-- Any permutation is accounted for by the elementary schemata. This is
existence from a proposition, not an algorithm extracting a sorting script. -/
theorem order_cell_exists {first second : List Index} (order : first.Perm second) (target : Encoder Index width) :
    Nonempty (Cell (generate first target) (generate second target)) := by
  induction order with
  | nil => exact ⟨.refl []⟩
  | cons index order ih =>
    obtain ⟨cell⟩ := ih
    exact ⟨.cons ⟨index, target index⟩ cell⟩
  | swap first second tail => exact ⟨exchangeCell second first tail target⟩
  | trans first second ihFirst ihSecond =>
    obtain ⟨one⟩ := ihFirst
    obtain ⟨two⟩ := ihSecond
    exact ⟨.trans one two⟩

theorem order_sound {first second : List Index} (order : first.Perm second)
    (source target : Encoder Index width) : run (generate first target) source = run (generate second target) source := by
  obtain ⟨cell⟩ := order_cell_exists order target
  exact cell.sound source

end CryptoOracle.RandomOracle.Representation.Patches
