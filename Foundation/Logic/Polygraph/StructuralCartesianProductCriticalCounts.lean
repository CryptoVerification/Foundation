import Foundation.Logic.Polygraph.StructuralCartesianProductTriangleCoherence

/-! Count only uses of the two new projection critical generator families.
All payload sizes, groupoid constructors, old generators and checker costs
are excluded. This is not a total certificate complexity claim. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductCritical
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def Generator.productCount {a b : Shape Atom} : {p q : Wire a b} → {first second : ProofTrack p q} →
    Generator first second → Nat
  | _, _, _, _, .existing _ => 0
  | _, _, _, _, .fst _ | _, _, _, _, .snd _ => 1
  | _, _, _, _, .placed _ child => child.productCount

def productCount {a b : Shape Atom} : {p q : Wire a b} → {first second : ProofTrack p q} → Cell first second → Nat
  | _, _, _, _, .generator g => g.productCount
  | _, _, _, _, .symm child | _, _, _, _, .inverse child => productCount child
  | _, _, _, _, .trans first second | _, _, _, _, .comp first second => productCount first + productCount second
  | _, _, _, _, _ => 0

theorem embed_productCount {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (cell : CategoryCritical.Cell first second) : productCount (embed cell) = 0 := by
  induction cell <;> simp_all only [embed, productCount, Generator.productCount, Nat.add_zero]

theorem whisker_productCount {a b c d : Shape Atom} (place : Placement a b c d) {p q : Wire a b}
    {first second : ProofTrack p q} (cell : Cell first second) : productCount (whisker place cell) = productCount cell := by
  induction cell <;> simp_all only [whisker, productCount, Generator.productCount]

theorem etaNatural_productCount {a b c : Shape Atom} {p q : Wire a (.pair b c)} (path : ProofTrack p q) :
    productCount (PresentedObservation.etaNatural PresentedObservation.product path) = 0 := by
  induction path with
  | refl => rfl
  | step => exact embed_productCount _
  | comp one two ih₁ ih₂ =>
      simp only [PresentedObservation.etaNatural, productCount, ih₁, ih₂, Nat.add_zero]
  | inv child ih =>
      simp only [PresentedObservation.etaNatural, FourNaturality.invertSquare, FourNaturality.cancelPrefix,
        FourNaturality.undoInversePrefix, FourNaturality.undoLeft, FourNaturality.undoRight,
        productCount, ih, Nat.add_zero]

theorem cancelProofSuffix_productCount {a b : Shape Atom} {p q r : Wire a b} {first second : ProofTrack p q}
    (suffix : ProofTrack q r) (square : Cell (.comp first suffix) (.comp second suffix)) :
    productCount (cancelProofSuffix suffix square) = productCount square := by
  simp only [cancelProofSuffix, productCount, Nat.add_zero, Nat.zero_add]

theorem reflection_productCount {a b c : Shape Atom} {p q : Wire a (.pair b c)} (first second : ProofTrack p q)
    (left : Cell (ProductTracks.firstProjection first) (ProductTracks.firstProjection second))
    (right : Cell (ProductTracks.secondProjection first) (ProductTracks.secondProjection second)) :
    productCount (PresentedObservation.reflect PresentedObservation.product first second left right) =
      productCount left + productCount right := by
  simp only [PresentedObservation.reflect, PresentedObservation.tensorCells,
    PresentedObservation.product, FourNaturality.cancelPrefix, FourNaturality.undoInversePrefix,
    productCount, embed_productCount, whisker_productCount, Nat.add_zero, Nat.zero_add]
  have one := etaNatural_productCount first
  have two := etaNatural_productCount second
  simp only [PresentedObservation.product] at one two
  rw [one, two]
  omega

theorem forkFstSquare_productCount {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    productCount (forkFstSquare p q) = 0 := by
  simp only [forkFstSquare, liftOld, productCount, embed_productCount, Nat.add_zero]

theorem forkSndSquare_productCount {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    productCount (forkSndSquare p q) = 0 := by
  simp only [forkSndSquare, liftOld, productCount, embed_productCount, Nat.add_zero]

theorem forkCell_productCount {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) : productCount (forkCell p q) = 2 := by
  simp only [forkCell, reflection_productCount, cancelProofSuffix_productCount, productCount,
    fstCell, sndCell, Generator.productCount, forkFstSquare_productCount, forkSndSquare_productCount,
    Nat.zero_add]

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductCritical
