import Foundation.Logic.Polygraph.StructuralCartesianUnitCritical

/-! Four explicit categorical root-overlap diagrams extend the unit-critical
presentation: pentagon and the three association/unit overlaps. Boundaries
contain at most three actual rewrites. Completeness for the full eighteen-law
cartesian language is not asserted. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.CategoryCritical
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def associate {a b c d : Shape Atom} (p : Wire a b) (q : Wire b c) (r : Wire c d) :
    Step (.seq (.seq p q) r) (.seq p (.seq q r)) := .root (.assoc p q r)

def leftUnit {a b : Shape Atom} (p : Wire a b) : Step (.seq (.identity a) p) p := .root (.leftId p)
def rightUnit {a b : Shape Atom} (p : Wire a b) : Step (.seq p (.identity b)) p := .root (.rightId p)

def two {a b : Shape Atom} {p q r : Wire a b} (one : Step p q) (two : Step q r) : ProofTrack p r :=
  .comp (.step one) (.step two)

def three {a b : Shape Atom} {p q r s : Wire a b} (one : Step p q) (two : Step q r) (three : Step r s) :
    ProofTrack p s := .comp (.step one) (CategoryCritical.two two three)

inductive Generator : {a b : Shape Atom} → {p q : Wire a b} → ProofTrack p q → ProofTrack p q → Type where
  | existing {a b} {p q : Wire a b} {first second : ProofTrack p q}
      (old : UnitCritical.Generator first second) : Generator first second
  | pentagon {a b c d e} (p : Wire a b) (q : Wire b c) (r : Wire c d) (s : Wire d e) :
      Generator (two (associate (.seq p q) r s) (associate p q (.seq r s)))
        (three (.seqLeft (associate p q r) s) (associate p (.seq q r) s) (.seqRight p (associate q r s)))
  | leftUnit {a b c} (p : Wire a b) (q : Wire b c) :
      Generator (two (associate (.identity a) p q) (CategoryCritical.leftUnit (.seq p q)))
        (.step (.seqLeft (CategoryCritical.leftUnit p) q))
  | middleUnit {a b c} (p : Wire a b) (q : Wire b c) :
      Generator (two (associate p (.identity b) q) (.seqRight p (CategoryCritical.leftUnit q)))
        (.step (.seqLeft (CategoryCritical.rightUnit p) q))
  | rightUnit {a b c} (p : Wire a b) (q : Wire b c) :
      Generator (two (associate p q (.identity c)) (.seqRight p (CategoryCritical.rightUnit q)))
        (.step (CategoryCritical.rightUnit (.seq p q)))
  | placed {a b c d} (place : Placement a b c d) {p q : Wire a b} {first second : ProofTrack p q}
      (child : Generator first second) : Generator (place.track first) (place.track second)

def Generator.code : {a b : Shape Atom} → {p q : Wire a b} → {first second : ProofTrack p q} →
    Generator first second → Fin 23
  | _, _, _, _, _, _, .existing old => Fin.castAdd 4 old.code
  | _, _, _, _, _, _, .pentagon _ _ _ _ => ⟨19, by decide⟩
  | _, _, _, _, _, _, .leftUnit _ _ => ⟨20, by decide⟩
  | _, _, _, _, _, _, .middleUnit _ _ => ⟨21, by decide⟩
  | _, _, _, _, _, _, .rightUnit _ _ => ⟨22, by decide⟩
  | _, _, _, _, _, _, .placed _ child => child.code

theorem Generator.boundaries_bounded {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (generator : Generator first second) : stepCount first ≤ 3 ∧ stepCount second ≤ 3 := by
  induction generator with
  | existing old => exact old.boundaries_bounded
  | pentagon | leftUnit | middleUnit | rightUnit => simp only [two, three, stepCount]; omega
  | placed place child ih => simpa only [Placement.track_count] using ih

abbrev Cell {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) := Four Generator first second

def embed {a b : Shape Atom} : {p q : Wire a b} → {first second : ProofTrack p q} →
    UnitCritical.Cell first second → Cell first second
  | _, _, _, _, .refl p => .refl p
  | _, _, _, _, .generator old => .generator (.existing old)
  | _, _, _, _, .symm child => (embed child).symm
  | _, _, _, _, .trans one two => (embed one).trans (embed two)
  | _, _, _, _, .comp one two => .comp (embed one) (embed two)
  | _, _, _, _, .inverse child => .inverse (embed child)
  | _, _, _, _, .assoc one two three => .assoc one two three
  | _, _, _, _, .leftUnit path => .leftUnit path
  | _, _, _, _, .rightUnit path => .rightUnit path
  | _, _, _, _, .leftInv path => .leftInv path
  | _, _, _, _, .rightInv path => .rightInv path

def unitCell (a : Shape Atom) := embed (UnitCritical.unitCell a)

def pentagonCell {a b c d e : Shape Atom} (p : Wire a b) (q : Wire b c) (r : Wire c d) (s : Wire d e) :
    Cell (two (associate (.seq p q) r s) (associate p q (.seq r s)))
      (three (.seqLeft (associate p q r) s) (associate p (.seq q r) s) (.seqRight p (associate q r s))) :=
  .generator (.pentagon p q r s)

def leftUnitCell {a b c : Shape Atom} (p : Wire a b) (q : Wire b c) :
    Cell (two (associate (.identity a) p q) (leftUnit (.seq p q))) (.step (.seqLeft (leftUnit p) q)) :=
  .generator (.leftUnit p q)

def middleUnitCell {a b c : Shape Atom} (p : Wire a b) (q : Wire b c) :
    Cell (two (associate p (.identity b) q) (.seqRight p (leftUnit q))) (.step (.seqLeft (rightUnit p) q)) :=
  .generator (.middleUnit p q)

def rightUnitCell {a b c : Shape Atom} (p : Wire a b) (q : Wire b c) :
    Cell (two (associate p q (.identity c)) (.seqRight p (rightUnit q))) (.step (rightUnit (.seq p q))) :=
  .generator (.rightUnit p q)

def whisker {a b c d : Shape Atom} (place : Placement a b c d) : {p q : Wire a b} →
    {first second : ProofTrack p q} → Cell first second → Cell (place.track first) (place.track second)
  | _, _, _, _, .refl path => .refl _
  | _, _, _, _, .generator generator => .generator (.placed place generator)
  | _, _, _, _, .symm child => (whisker place child).symm
  | _, _, _, _, .trans one two => (whisker place one).trans (whisker place two)
  | _, _, _, _, .comp one two => .comp (whisker place one) (whisker place two)
  | _, _, _, _, .inverse child => .inverse (whisker place child)
  | _, _, _, _, .assoc one two three => .assoc _ _ _
  | _, _, _, _, .leftUnit path => .leftUnit _
  | _, _, _, _, .rightUnit path => .rightUnit _
  | _, _, _, _, .leftInv path => .leftInv _
  | _, _, _, _, .rightInv path => .rightInv _

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.CategoryCritical
