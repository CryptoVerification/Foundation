import Foundation.Crypto.Logic.Polygraph.MixedCircuitComputational

/-! Directed mixed-path comparison. Comparisons may be reversed, but the
underlying reductions are never reversed. A basis is supplied explicitly;
finiteness, completeness and contextual computational contracts are not
inferred from the stochastic mixed model. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Computational
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.General
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false

structure Basis (relators : Rule → Relator signature) where
  Generator : {n m : Port signature} → {a b : Circuit signature n m} →
    Path (relators := relators) a b → Path (relators := relators) a b → Type
  support : ∀ {n m} {a b : Circuit signature n m} {p q : Path (relators := relators) a b},
    Generator p q → Finset Requirement
  covered : ∀ {n m} {a b : Circuit signature n m} {p q : Path (relators := relators) a b}
    (generator : Generator p q), Path.support p ⊆ support generator ∧ Path.support q ⊆ support generator

inductive Cell (basis : Basis relators) : {n m : Port signature} → {a b : Circuit signature n m} →
    Path (relators := relators) a b → Path (relators := relators) a b → Type where
  | refl {n m} {a b : Circuit signature n m} (path : Path (relators := relators) a b) : Cell basis path path
  | generator {n m} {a b : Circuit signature n m} {p q : Path (relators := relators) a b}
      (generator : basis.Generator p q) : Cell basis p q
  | symm {n m} {a b : Circuit signature n m} {p q : Path (relators := relators) a b} :
      Cell basis p q → Cell basis q p
  | trans {n m} {a b : Circuit signature n m} {p q r : Path (relators := relators) a b} :
      Cell basis p q → Cell basis q r → Cell basis p r
  | comp {n m} {a b c : Circuit signature n m}
      {p p' : Path (relators := relators) a b} {q q' : Path (relators := relators) b c} :
      Cell basis p p' → Cell basis q q' → Cell basis (p.comp q) (p'.comp q')

namespace Cell
variable {basis : Basis relators}

def support : {n m : Port signature} → {a b : Circuit signature n m} →
    {p q : Path (relators := relators) a b} → Cell basis p q → Finset Requirement
  | _, _, _, _, _, _, .refl path => Path.support path
  | _, _, _, _, _, _, .generator witness => basis.support witness
  | _, _, _, _, _, _, .symm child => support child
  | _, _, _, _, _, _, .trans first second | _, _, _, _, _, _, .comp first second => support first ∪ support second

theorem boundaries {n m} {a b : Circuit signature n m} {p q : Path (relators := relators) a b}
    (cell : Cell basis p q) : Path.support p ⊆ support cell ∧ Path.support q ⊆ support cell := by
  induction cell with
  | refl => simp only [support]; exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | generator generator => simp only [support]; exact basis.covered generator
  | symm child ih => simp only [support]; exact ⟨ih.2, ih.1⟩
  | trans first second one two =>
      simp only [support]
      exact ⟨fun _ h => Finset.mem_union_left _ (one.1 h), fun _ h => Finset.mem_union_right _ (two.2 h)⟩
  | comp first second one two =>
      simp only [support, Path.comp_support]
      exact ⟨Finset.union_subset_union one.1 two.1, Finset.union_subset_union one.2 two.2⟩

end Cell

structure HigherModel (K : CodeSystem) (basis : Basis relators) (condition : Requirement → Prop) where
  base : Model K relators condition
  comparison : ∀ {n m} {a b : Circuit signature n m} {p q : Path (relators := relators) a b}
    (generator : basis.Generator p q), Holds condition (basis.support generator) →
    ∀ (left : Holds condition (Path.support p)) (right : Holds condition (Path.support q)),
      CertifiedComparison (extract base p left) (extract base q right)

theorem compare {K : CodeSystem} {condition : Requirement → Prop} {basis : Basis relators}
    (model : HigherModel K basis condition) {n m} {a b : Circuit signature n m}
    {p q : Path (relators := relators) a b} (cell : Cell basis p q)
    (valid : Holds condition cell.support)
    (left : Holds condition (Path.support p)) (right : Holds condition (Path.support q)) :
    CertifiedComparison (extract model.base p left) (extract model.base q right) := by
  induction cell with
  | refl => exact CertifiedComparison.refl _
  | generator generator =>
      simp only [Cell.support] at valid
      exact model.comparison generator valid left right
  | symm child ih =>
      simp only [Cell.support] at valid
      exact (ih valid right left).symm
  | trans first second one two =>
      simp only [Cell.support] at valid
      have firstValid := valid.restrict Finset.subset_union_left
      have secondValid := valid.restrict Finset.subset_union_right
      have middle := firstValid.restrict first.boundaries.2
      exact (one firstValid left middle).trans (two secondValid middle right)
  | @comp a b c p p' q q' first second one two =>
      simp only [Cell.support] at valid
      have firstValid := valid.restrict Finset.subset_union_left
      have secondValid := valid.restrict Finset.subset_union_right
      have pValid := firstValid.restrict first.boundaries.1
      have p'Valid := firstValid.restrict first.boundaries.2
      have qValid := secondValid.restrict second.boundaries.1
      have q'Valid := secondValid.restrict second.boundaries.2
      exact (extract_comp model.base p q pValid qValid left).symm.trans
        (((one firstValid pValid p'Valid).comp (two secondValid qValid q'Valid)).trans
          (extract_comp model.base p' q' p'Valid q'Valid right))

theorem repaired_comparison {K : CodeSystem} {old updated : Requirement → Prop} {basis : Basis relators}
    (model : HigherModel K basis updated) {n m} {a b : Circuit signature n m}
    {p q : Path (relators := relators) a b} (cell : Cell basis p q)
    (changed : Finset Requirement) (cached : Holds old cell.support)
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh cell.support changed)) :
    let valid := repair cached unchanged rechecked
    CertifiedComparison (extract model.base p (valid.restrict cell.boundaries.1))
      (extract model.base q (valid.restrict cell.boundaries.2)) :=
  compare model cell (repair cached unchanged rechecked) _ _

end CryptoLogic.Polygraph.MixedCircuit.Computational
