import Foundation.Logic.Polygraph.StructuralCartesianProductCritical

/-! Two local distribution/projection diagrams extend the product-critical
basis. Each new boundary has two actual rewrites. Opaque wire arguments are
parameters; no whole-normalization comparison is a generator. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.DistributionCritical
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def fstDistributed {a b c d : Shape Atom} (p : Wire a b) (q : Wire b c) (r : Wire b d) :=
  Track.comp (.step (Step.seqLeft (.root (.forkAfter p q r)) (fst c d)))
    (.step (.root (.betaFst (.seq p q) (.seq p r))))

def fstAssociated {a b c d : Shape Atom} (p : Wire a b) (q : Wire b c) (r : Wire b d) :=
  Track.comp (.step (Step.root (.assoc p (fork q r) (fst c d))))
    (.step (.seqRight p (.root (.betaFst q r))))

def sndDistributed {a b c d : Shape Atom} (p : Wire a b) (q : Wire b c) (r : Wire b d) :=
  Track.comp (.step (Step.seqLeft (.root (.forkAfter p q r)) (snd c d)))
    (.step (.root (.betaSnd (.seq p q) (.seq p r))))

def sndAssociated {a b c d : Shape Atom} (p : Wire a b) (q : Wire b c) (r : Wire b d) :=
  Track.comp (.step (Step.root (.assoc p (fork q r) (snd c d))))
    (.step (.seqRight p (.root (.betaSnd q r))))

inductive Generator : {a b : Shape Atom} → {p q : Wire a b} → ProofTrack p q → ProofTrack p q → Type where
  | existing {a b} {p q : Wire a b} {first second : ProofTrack p q}
      (old : ProductCritical.Generator first second) : Generator first second
  | fst {a b c d} (p : Wire a b) (q : Wire b c) (r : Wire b d) : Generator (fstDistributed p q r) (fstAssociated p q r)
  | snd {a b c d} (p : Wire a b) (q : Wire b c) (r : Wire b d) : Generator (sndDistributed p q r) (sndAssociated p q r)
  | placed {a b c d} (place : Placement a b c d) {p q : Wire a b} {first second : ProofTrack p q}
      (child : Generator first second) : Generator (place.track first) (place.track second)

def Generator.code : {a b : Shape Atom} → {p q : Wire a b} → {first second : ProofTrack p q} →
    Generator first second → Fin 27
  | _, _, _, _, _, _, .existing old => Fin.castAdd 2 old.code
  | _, _, _, _, _, _, .fst _ _ _ => ⟨25, by decide⟩
  | _, _, _, _, _, _, .snd _ _ _ => ⟨26, by decide⟩
  | _, _, _, _, _, _, .placed _ child => child.code

theorem Generator.boundaries_bounded {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (generator : Generator first second) : stepCount first ≤ 3 ∧ stepCount second ≤ 3 := by
  induction generator with
  | existing old => exact old.boundaries_bounded
  | fst | snd => change 2 ≤ 3 ∧ 2 ≤ 3; decide
  | placed place child ih => simpa only [Placement.track_count] using ih

theorem Generator.new_boundaries_two {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (generator : Generator first second) : 25 ≤ generator.code.val → stepCount first = 2 ∧ stepCount second = 2 := by
  induction generator with
  | existing old =>
      intro member
      change 25 ≤ old.code.val at member
      have bound := old.code.isLt
      omega
  | fst | snd => intro _; exact ⟨rfl, rfl⟩
  | placed place child ih => intro member; simpa only [Placement.track_count] using ih member

abbrev Cell {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) := Four Generator first second

def embed {a b : Shape Atom} : {p q : Wire a b} → {first second : ProofTrack p q} →
    ProductCritical.Cell first second → Cell first second
  | _, _, _, _, .refl path => .refl path
  | _, _, _, _, .generator old => .generator (.existing old)
  | _, _, _, _, .symm child => (embed child).symm
  | _, _, _, _, .trans first second => (embed first).trans (embed second)
  | _, _, _, _, .comp first second => .comp (embed first) (embed second)
  | _, _, _, _, .inverse child => .inverse (embed child)
  | _, _, _, _, .assoc p q r => .assoc p q r
  | _, _, _, _, .leftUnit path => .leftUnit path
  | _, _, _, _, .rightUnit path => .rightUnit path
  | _, _, _, _, .leftInv path => .leftInv path
  | _, _, _, _, .rightInv path => .rightInv path

def whisker {a b c d : Shape Atom} (place : Placement a b c d) : {p q : Wire a b} →
    {first second : ProofTrack p q} → Cell first second → Cell (place.track first) (place.track second)
  | _, _, _, _, .refl path => .refl _
  | _, _, _, _, .generator g => .generator (.placed place g)
  | _, _, _, _, .symm child => (whisker place child).symm
  | _, _, _, _, .trans first second => .trans (whisker place first) (whisker place second)
  | _, _, _, _, .comp first second => .comp (whisker place first) (whisker place second)
  | _, _, _, _, .inverse child => .inverse (whisker place child)
  | _, _, _, _, .assoc p q r => .assoc _ _ _
  | _, _, _, _, .leftUnit path => .leftUnit _
  | _, _, _, _, .rightUnit path => .rightUnit _
  | _, _, _, _, .leftInv path => .leftInv _
  | _, _, _, _, .rightInv path => .rightInv _

def fstCell {a b c d : Shape Atom} (p : Wire a b) (q : Wire b c) (r : Wire b d) :
    Cell (fstDistributed p q r) (fstAssociated p q r) := .generator (.fst p q r)
def sndCell {a b c d : Shape Atom} (p : Wire a b) (q : Wire b c) (r : Wire b d) :
    Cell (sndDistributed p q r) (sndAssociated p q r) := .generator (.snd p q r)

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.DistributionCritical
