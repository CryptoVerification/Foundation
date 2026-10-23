import Foundation.Logic.Polygraph.StructuralCartesianCoherenceInvariant

/-! One explicit categorical critical overlap extends the partial cartesian
higher presentation. The old basis cannot compare the two unit reductions at
an atomic identity. This addition resolves that family only, not all overlaps. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.UnitCritical
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

inductive Generator : {a b : Shape Atom} → {p q : Wire a b} → ProofTrack p q → ProofTrack p q → Type where
  | existing {a b} {p q : Wire a b} {first second : ProofTrack p q}
      (old : Cartesian.Higher.Generator first second) : Generator first second
  | unit (a : Shape Atom) :
      Generator (.step (.root (Cartesian.Root.leftId (Wire.identity a))))
        (.step (.root (Cartesian.Root.rightId (Wire.identity a))))
  | placed {a b c d} (place : Placement a b c d) {p q : Wire a b} {first second : ProofTrack p q}
      (child : Generator first second) : Generator (place.track first) (place.track second)

def Generator.code : {a b : Shape Atom} → {p q : Wire a b} → {first second : ProofTrack p q} →
    Generator first second → Fin 19
  | _, _, _, _, _, _, .existing old => Fin.castSucc old.code
  | _, _, _, _, _, _, .unit _ => ⟨18, by decide⟩
  | _, _, _, _, _, _, .placed _ child => child.code

theorem Generator.boundaries_bounded {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (generator : Generator first second) : stepCount first ≤ 3 ∧ stepCount second ≤ 3 := by
  induction generator with
  | existing old => exact old.boundaries_bounded
  | unit => change 1 ≤ 3 ∧ 1 ≤ 3; decide
  | placed place child ih => simpa only [Placement.track_count] using ih

abbrev Cell {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) := Four Generator first second

def unitCell (a : Shape Atom) :
    Cell (.step (.root (Cartesian.Root.leftId (Wire.identity a))))
      (.step (.root (Cartesian.Root.rightId (Wire.identity a)))) := .generator (.unit a)

def embed {a b : Shape Atom} : {p q : Wire a b} → {first second : ProofTrack p q} →
    Cartesian.Higher.Homotopy first second → Cell first second
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

/-- The extension supplies an actual missing local comparison, while retaining
all old derivations. No global coherence conclusion is drawn. -/
theorem strict_extension (name : Atom) :
    Nonempty (Cell (.step (.root (Cartesian.Root.leftId (Wire.identity (.atom name)))))
      (.step (.root (Cartesian.Root.rightId (Wire.identity (.atom name)))))) ∧
    ¬ Nonempty (Cartesian.Higher.Homotopy
      (.step (.root (Cartesian.Root.leftId (Wire.identity (.atom name)))))
      (.step (.root (Cartesian.Root.rightId (Wire.identity (.atom name)))))) :=
  ⟨⟨unitCell (.atom name)⟩, CoherenceInvariant.unit_overlap_not_comparable name⟩

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.UnitCritical
