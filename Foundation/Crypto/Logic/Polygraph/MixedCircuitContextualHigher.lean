import Foundation.Crypto.Logic.Polygraph.MixedCircuitPresentedHigher

/-! Close an explicit higher presentation under the four mixed placements.
This supplies contextual reuse, not missing critical generators or completeness.
All recursively used guards remain visible. -/
namespace CryptoLogic.Polygraph.MixedCircuit
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}

inductive ContextualGenerator (basis : HigherBasis relators) : {n m : Port signature} →
    {a b : Circuit signature n m} → RewriteTrack (relators := relators) a b → RewriteTrack (relators := relators) a b → Type where
  | root {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
      (generator : basis.Generator p q) : ContextualGenerator basis p q
  | placed {a b c d} (place : Placement (signature := signature) a b c d)
      {x y : Circuit signature a b} {p q : RewriteTrack (relators := relators) x y}
      (child : ContextualGenerator basis p q) : ContextualGenerator basis (place.track p) (place.track q)

namespace ContextualGenerator
variable {basis : HigherBasis relators}

def support : {n m : Port signature} → {a b : Circuit signature n m} →
    {p q : RewriteTrack (relators := relators) a b} → ContextualGenerator basis p q → Finset Requirement
  | _, _, _, _, _, _, .root generator => basis.requirements generator
  | _, _, _, _, _, _, .placed place child => support child ∪ place.needs

theorem boundaries {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (generator : ContextualGenerator basis p q) :
    RewriteTrack.support p ⊆ generator.support ∧ RewriteTrack.support q ⊆ generator.support := by
  induction generator with
  | root generator => exact basis.covered generator
  | placed place child ih =>
      simp only [Placement.track_support, support]
      exact ⟨Finset.union_subset_union ih.1 (Finset.Subset.refl _),
        Finset.union_subset_union ih.2 (Finset.Subset.refl _)⟩

end ContextualGenerator

def contextualBasis (basis : HigherBasis relators) : HigherBasis relators where
  Generator := ContextualGenerator basis
  requirements := ContextualGenerator.support
  covered := ContextualGenerator.boundaries

namespace PresentedCell
variable {basis : HigherBasis relators}

def embed : {n m : Port signature} → {a b : Circuit signature n m} →
    {p q : RewriteTrack (relators := relators) a b} → PresentedCell basis p q → PresentedCell (contextualBasis basis) p q
  | _, _, _, _, _, _, .refl p => .refl p
  | _, _, _, _, _, _, .generator generator => .generator (.root generator)
  | _, _, _, _, _, _, .symm child => (embed child).symm
  | _, _, _, _, _, _, .trans first second => (embed first).trans (embed second)
  | _, _, _, _, _, _, .comp first second => .comp (embed first) (embed second)
  | _, _, _, _, _, _, .inverse child => .inverse (embed child)
  | _, _, _, _, _, _, .assoc p q r => .assoc p q r
  | _, _, _, _, _, _, .leftUnit p => .leftUnit p
  | _, _, _, _, _, _, .rightUnit p => .rightUnit p
  | _, _, _, _, _, _, .leftInv p => .leftInv p
  | _, _, _, _, _, _, .rightInv p => .rightInv p

theorem embed_support {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (cell : PresentedCell basis p q) : support cell.embed = support cell := by
  induction cell <;> simp_all only [embed, support, contextualBasis, ContextualGenerator.support]

def whisker {a b c d} (place : Placement (signature := signature) a b c d) :
    {x y : Circuit signature a b} → {p q : RewriteTrack (relators := relators) x y} →
    PresentedCell (contextualBasis basis) p q →
      PresentedCell (contextualBasis basis) (place.track p) (place.track q)
  | _, _, _, _, .refl p => .refl _
  | _, _, _, _, .generator generator => .generator (.placed place generator)
  | _, _, _, _, .symm cell => (whisker place cell).symm
  | _, _, _, _, .trans first second => (whisker place first).trans (whisker place second)
  | _, _, _, _, .comp first second => .comp (whisker place first) (whisker place second)
  | _, _, _, _, .inverse child => .inverse (whisker place child)
  | _, _, _, _, .assoc p q r => .assoc _ _ _
  | _, _, _, _, .leftUnit p => .leftUnit _
  | _, _, _, _, .rightUnit p => .rightUnit _
  | _, _, _, _, .leftInv p => .leftInv _
  | _, _, _, _, .rightInv p => .rightInv _

theorem whisker_support {a b c d} (place : Placement (signature := signature) a b c d)
    {x y : Circuit signature a b} {p q : RewriteTrack (relators := relators) x y}
    (cell : PresentedCell (contextualBasis basis) p q) :
    support (cell.whisker place) = support cell ∪ place.needs := by
  induction cell with
  | refl path => exact place.track_support path
  | generator generator => rfl
  | symm cell ih | inverse cell ih => exact ih
  | trans first second one two | comp first second one two =>
      simp only [whisker, support, one, two, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm, Finset.union_left_idem]
  | assoc p q r =>
      simp only [whisker, support, Placement.map_support, Finset.union_assoc, Finset.union_left_comm,
        Finset.union_comm, Finset.union_left_idem]
  | leftUnit p | rightUnit p | leftInv p | rightInv p => exact place.track_support p

theorem whisker_constructorCount {a b c d} (place : Placement (signature := signature) a b c d)
    {x y : Circuit signature a b} {p q : RewriteTrack (relators := relators) x y}
    (cell : PresentedCell (contextualBasis basis) p q) :
    constructorCount (cell.whisker place) = constructorCount cell := by
  induction cell <;> simp_all only [whisker, constructorCount]

theorem embed_constructorCount {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (cell : PresentedCell basis p q) : constructorCount cell.embed = constructorCount cell := by
  induction cell <;> simp_all only [embed, constructorCount]

theorem whisker_fresh {a b c d} (place : Placement (signature := signature) a b c d)
    {x y : Circuit signature a b} {p q : RewriteTrack (relators := relators) x y}
    (cell : PresentedCell (contextualBasis basis) p q) (changed : Finset Requirement) :
    fresh (support (cell.whisker place)) changed = fresh (support cell) changed ∪ fresh place.needs changed := by
  rw [whisker_support]
  exact Finset.union_inter_distrib_right _ _ _

end PresentedCell
end CryptoLogic.Polygraph.MixedCircuit
