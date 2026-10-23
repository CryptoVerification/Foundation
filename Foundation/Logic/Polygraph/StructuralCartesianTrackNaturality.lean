import Foundation.Logic.Polygraph.StructuralCartesianLocalHigher
import Foundation.Logic.Polygraph.FourPathNaturality

/-! Extend the existing sixteen argument squares to actual proof tracks.
Template substitution changes every occurrence of the same argument, including
zero/two occurrences, without adding a whole-track generator. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def Template.track {u v a b : Shape Atom} (template : Template u v a b)
    {p q : Wire u v} (path : ProofTrack p q) :
    ProofTrack (template.apply p) (template.apply q) :=
  FourPathNaturality.replace template.apply (fun change => template.change change) path

theorem Template.track_count {u v a b : Shape Atom} (template : Template u v a b)
    {p q : Wire u v} (path : ProofTrack p q) :
    stepCount (template.track path) = template.holes * stepCount path := by
  induction path <;> simp_all only [Template.track, FourPathNaturality.replace,
    stepCount, Template.change_count, Nat.mul_zero, Nat.mul_one, Nat.mul_add]

def argumentTrack {u v a b : Shape Atom} (variation : Variation u v a b)
    {p q : Wire u v} (path : ProofTrack p q) :
    Homotopy
      (.comp (variation.left.track path) (.step (.root (variation.rootAt q))))
      (.comp (.step (.root (variation.rootAt p))) (variation.right.track path)) :=
  FourPathNaturality.natural variation.left.apply variation.right.apply
    (fun change => variation.left.change change) (fun change => variation.right.change change)
    (fun wire => .step (.root (variation.rootAt wire)))
    (fun change => argumentCell variation change) path

namespace Homotopy

theorem invertSquare_generatorCount {a b : Shape Atom} {p q r s : Wire a b}
    (one : ProofTrack p q) (two : ProofTrack q s) (three : ProofTrack p r) (four : ProofTrack r s)
    (cell : Homotopy (.comp one two) (.comp three four)) :
    generatorCount (FourNaturality.invertSquare one two three four cell) = generatorCount cell := by
  simp only [FourNaturality.invertSquare, FourNaturality.cancelPrefix,
    FourNaturality.undoInversePrefix, FourNaturality.undoLeft, FourNaturality.undoRight,
    generatorCount, Nat.zero_add, Nat.add_zero]

end Homotopy

theorem argumentTrack_generatorCount {u v a b : Shape Atom} (variation : Variation u v a b)
    {p q : Wire u v} (path : ProofTrack p q) :
    Homotopy.generatorCount (argumentTrack variation path) = stepCount path := by
  unfold argumentTrack
  induction path with
  | refl => rfl
  | step change => rfl
  | comp one two ih₁ ih₂ =>
      simp only [FourPathNaturality.natural, Homotopy.generatorCount, ih₁, ih₂,
        stepCount, Nat.zero_add, Nat.add_zero]
      omega
  | inv child ih =>
      exact (Homotopy.invertSquare_generatorCount _ _ _ _ _).trans ih

def tensorFirstTrack {a b c d : Shape Atom} {p p' : Wire a b}
    (path : ProofTrack p p') (q : Wire c d) := argumentTrack (Variation.tensorFirst q) path

def tensorLastTrack {a b c d : Shape Atom} (p : Wire a b) {q q' : Wire c d}
    (path : ProofTrack q q') := argumentTrack (Variation.tensorLast p) path

theorem tensorFirstTrack_generatorCount {a b c d : Shape Atom} {p p' : Wire a b}
    (path : ProofTrack p p') (q : Wire c d) :
    Homotopy.generatorCount (tensorFirstTrack path q) = stepCount path :=
  argumentTrack_generatorCount _ _

theorem tensorLastTrack_generatorCount {a b c d : Shape Atom} (p : Wire a b)
    {q q' : Wire c d} (path : ProofTrack q q') :
    Homotopy.generatorCount (tensorLastTrack p path) = stepCount path :=
  argumentTrack_generatorCount _ _

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher
