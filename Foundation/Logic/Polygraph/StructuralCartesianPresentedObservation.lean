import Foundation.Logic.Polygraph.StructuralCartesianObservationCoherence
import Foundation.Logic.Polygraph.StructuralCartesianProductCritical

/-! Output-observation proof reconstruction in an explicitly supplied higher
extension. The old local diagrams and contextual placement are inputs; no
arbitrary comparison is postulated. Instantiate both categorical and product
critical presentations, so atomic witnesses may use the added local cells. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.PresentedObservation
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

structure Extension (Atom : Type) where
  Generator : {a b : Shape Atom} → {p q : Wire a b} → ProofTrack p q → ProofTrack p q → Type
  embed : {a b : Shape Atom} → {p q : Wire a b} → {first second : ProofTrack p q} →
    Homotopy first second → Four Generator first second
  whisker : {a b c d : Shape Atom} → (place : Placement a b c d) → {p q : Wire a b} →
    {first second : ProofTrack p q} → Four Generator first second → Four Generator (place.track first) (place.track second)

abbrev Cell (basis : Extension Atom) {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) :=
  Four basis.Generator first second

def categorical : Extension Atom where
  Generator := CategoryCritical.Generator
  embed := CategoryCritical.oldLift
  whisker := CategoryCritical.whisker

def product : Extension Atom where
  Generator := ProductCritical.Generator
  embed := fun cell => ProductCritical.embed (CategoryCritical.oldLift cell)
  whisker := ProductCritical.whisker

def tensorCells (basis : Extension Atom) {a b c d : Shape Atom} {p p' : Wire a b} {q q' : Wire c d}
    {one one' : ProofTrack p p'} {two two' : ProofTrack q q'}
    (first : Cell basis one one') (second : Cell basis two two') :
    Cell basis (ProductTracks.tensor one two) (ProductTracks.tensor one' two') :=
  .comp (basis.whisker (.tensorLeft q) first) (basis.whisker (.tensorRight p') second)

def etaNatural (basis : Extension Atom) {a b c : Shape Atom} : {p q : Wire a (.pair b c)} →
    (path : ProofTrack p q) →
    Cell basis (.comp ((Variation.eta a b c).left.track path) (.step (.root (.eta q))))
      (.comp (.step (.root (.eta p))) path)
  | _, _, .refl _ => (Four.leftUnit _).trans (Four.rightUnit _).symm
  | _, _, .step change => basis.embed (argumentCell (Variation.eta a b c) change)
  | _, _, .comp first second =>
      (Four.assoc _ _ _).trans
        ((Four.comp (.refl _) (etaNatural basis second)).trans
          ((Four.assoc _ _ _).symm.trans
            ((Four.comp (etaNatural basis first) (.refl _)).trans (Four.assoc _ _ _))))
  | p, q, .inv child =>
      FourNaturality.invertSquare ((Variation.eta a b c).left.track child)
        (.step (.root (.eta p))) (.step (.root (.eta q))) child (etaNatural basis child)

def reflect (basis : Extension Atom) {a b c : Shape Atom} {p q : Wire a (.pair b c)} (first second : ProofTrack p q)
    (left : Cell basis (ProductTracks.firstProjection first) (ProductTracks.firstProjection second))
    (right : Cell basis (ProductTracks.secondProjection first) (ProductTracks.secondProjection second)) : Cell basis first second := by
  have observed : Cell basis ((Variation.eta a b c).left.track first) ((Variation.eta a b c).left.track second) :=
    (basis.embed (ProductTracks.etaSplit first)).trans
      ((basis.whisker (.seqRight (.copy a)) (tensorCells basis left right)).trans
        (basis.embed (ProductTracks.etaSplit second)).symm)
  exact FourNaturality.cancelPrefix (.step (.root (.eta p)))
    ((etaNatural basis first).symm.trans ((Four.comp observed (.refl _)).trans (etaNatural basis second)))

def AtomicCertificate (basis : Extension Atom) {a : Shape Atom} : {b : Shape Atom} → {p q : Wire a b} →
    (first second : ProofTrack p q) → Type
  | .atom _, _, _, first, second => Cell basis first second
  | .unit, _, _, _, _ => PUnit
  | .pair _ _, _, _, first, second =>
      AtomicCertificate basis (ProductTracks.firstProjection first) (ProductTracks.firstProjection second) ×
      AtomicCertificate basis (ProductTracks.secondProjection first) (ProductTracks.secondProjection second)

def reconstruct (basis : Extension Atom) {a : Shape Atom} : {b : Shape Atom} → {p q : Wire a b} →
    (first second : ProofTrack p q) → AtomicCertificate basis first second → Cell basis first second
  | .atom _, _, _, _, _, cell => cell
  | .unit, _, _, first, second, _ => basis.embed (ObservationCoherence.terminalParallel first second)
  | .pair _ _, _, _, first, second, certificate =>
      reflect basis first second (reconstruct basis _ _ certificate.1) (reconstruct basis _ _ certificate.2)

def observe (basis : Extension Atom) {a : Shape Atom} : {b : Shape Atom} → {p q : Wire a b} →
    {first second : ProofTrack p q} → Cell basis first second → AtomicCertificate basis first second
  | .atom _, _, _, _, _, cell => cell
  | .unit, _, _, _, _, _ => PUnit.unit
  | .pair b c, _, _, _, _, cell =>
      (observe basis (basis.whisker (.seqLeft (fst b c)) cell), observe basis (basis.whisker (.seqLeft (snd b c)) cell))

theorem comparable_iff_atomic (basis : Extension Atom) {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) :
    Nonempty (Cell basis first second) ↔ Nonempty (AtomicCertificate basis first second) :=
  ⟨fun ⟨cell⟩ => ⟨observe basis cell⟩, fun ⟨certificate⟩ => ⟨reconstruct basis first second certificate⟩⟩

def fromOldCertificate (basis : Extension Atom) {a : Shape Atom} : {b : Shape Atom} → {p q : Wire a b} →
    {first second : ProofTrack p q} → ObservationCoherence.AtomicCertificate first second → AtomicCertificate basis first second
  | .atom _, _, _, _, _, cell => basis.embed cell
  | .unit, _, _, _, _, _ => PUnit.unit
  | .pair _ _, _, _, _, _, certificate => (fromOldCertificate basis certificate.1, fromOldCertificate basis certificate.2)

def certificateLeaves (basis : Extension Atom) {a : Shape Atom} : {b : Shape Atom} → {p q : Wire a b} →
    {first second : ProofTrack p q} → AtomicCertificate basis first second → Nat
  | .atom _, _, _, _, _, _ => 1
  | .unit, _, _, _, _, _ => 0
  | .pair _ _, _, _, _, _, certificate => certificateLeaves basis certificate.1 + certificateLeaves basis certificate.2

theorem certificateLeaves_eq (basis : Extension Atom) {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (certificate : AtomicCertificate basis first second) : certificateLeaves basis certificate = ObservationCoherence.atomCount b := by
  induction b with
  | atom => rfl
  | unit => rfl
  | pair b c ih₁ ih₂ => exact congrArg₂ (· + ·) (ih₁ certificate.1) (ih₂ certificate.2)

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.PresentedObservation
