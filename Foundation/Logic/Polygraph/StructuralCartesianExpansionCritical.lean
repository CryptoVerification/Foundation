import Foundation.Logic.Polygraph.StructuralCartesianExpansionUnitPeak

/-! Four bounded local expansion diagrams retain the previous distribution
basis. Tensor/projection boundaries have seven and one rewrite leaves, with
one inverse association; unit boundaries have two and three forward leaves.
No whole-normalization comparison is a generator. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

inductive Generator : {a b : Shape Atom} → {p q : Wire a b} → ProofTrack p q → ProofTrack p q → Type where
  | existing {a b} {p q : Wire a b} {first second : ProofTrack p q}
      (old : DistributionCritical.Generator first second) : Generator first second
  | fst {a b c} (p : Wire a b) (q : Wire a c) : Generator (TensorProjectionPeak.fstExpanded p q) (TensorProjectionPeak.fstDirect p q)
  | snd {a b c} (p : Wire a b) (q : Wire a c) : Generator (TensorProjectionPeak.sndExpanded p q) (TensorProjectionPeak.sndDirect p q)
  | leftUnit (a : Shape Atom) : Generator (ExpansionUnitPeak.leftExpanded a) (ExpansionUnitPeak.leftCopied a)
  | rightUnit (a : Shape Atom) : Generator (ExpansionUnitPeak.rightExpanded a) (ExpansionUnitPeak.rightCopied a)
  | placed {a b c d} (place : Placement a b c d) {p q : Wire a b} {first second : ProofTrack p q}
      (child : Generator first second) : Generator (place.track first) (place.track second)

def Generator.code : {a b : Shape Atom} → {p q : Wire a b} → {first second : ProofTrack p q} →
    Generator first second → Fin 31
  | _, _, _, _, _, _, .existing old => Fin.castAdd 4 old.code
  | _, _, _, _, _, _, .fst _ _ => ⟨27, by decide⟩
  | _, _, _, _, _, _, .snd _ _ => ⟨28, by decide⟩
  | _, _, _, _, _, _, .leftUnit _ => ⟨29, by decide⟩
  | _, _, _, _, _, _, .rightUnit _ => ⟨30, by decide⟩
  | _, _, _, _, _, _, .placed _ child => child.code

theorem Generator.boundaries_bounded {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (generator : Generator first second) : stepCount first ≤ 7 ∧ stepCount second ≤ 7 := by
  induction generator with
  | existing old =>
      have bound := old.boundaries_bounded
      exact ⟨by omega, by omega⟩
  | fst | snd => change 7 ≤ 7 ∧ 1 ≤ 7; decide
  | leftUnit | rightUnit => change 2 ≤ 7 ∧ 3 ≤ 7; decide
  | placed place child ih => simpa only [Placement.track_count] using ih

abbrev Cell {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) := Four Generator first second

def embed {a b : Shape Atom} : {p q : Wire a b} → {first second : ProofTrack p q} →
    DistributionCritical.Cell first second → Cell first second
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

def oldLift {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (cell : Homotopy first second) : Cell first second := embed (DistributionCritical.oldLift cell)

def extension : PresentedObservation.Extension Atom where
  Generator := Generator
  embed := oldLift
  whisker := whisker

def fstCell {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    Cell (TensorProjectionPeak.fstExpanded p q) (TensorProjectionPeak.fstDirect p q) := .generator (.fst p q)
def sndCell {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    Cell (TensorProjectionPeak.sndExpanded p q) (TensorProjectionPeak.sndDirect p q) := .generator (.snd p q)
def leftUnitCell (a : Shape Atom) : Cell (ExpansionUnitPeak.leftExpanded a) (ExpansionUnitPeak.leftCopied a) :=
  .generator (.leftUnit a)
def rightUnitCell (a : Shape Atom) : Cell (ExpansionUnitPeak.rightExpanded a) (ExpansionUnitPeak.rightCopied a) :=
  .generator (.rightUnit a)

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical
