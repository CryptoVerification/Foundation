import Foundation.Logic.Polygraph.StructuralCartesianPresentedObservation
import Foundation.Logic.Polygraph.StructuralCartesianProductProjectionNaturality

/-! The fork/eta critical triangle is derived from the TWO projection/eta
critical diagrams, old argument naturality, and output-observation reflection.
No fork/eta generator is used in this construction. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductCritical
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def liftOld {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (cell : Homotopy first second) : Cell first second := embed (CategoryCritical.oldLift cell)

def cancelProofSuffix {a b : Shape Atom} {p q r : Wire a b} {first second : ProofTrack p q}
    (suffix : ProofTrack q r) (square : Cell (.comp first suffix) (.comp second suffix)) : Cell first second :=
  (Four.rightUnit (G := Generator) first).symm.trans
    ((Four.comp (.refl first) (Four.rightInv suffix).symm).trans
      ((Four.assoc first suffix (.inv suffix)).symm.trans
        ((Four.comp square (.refl (.inv suffix))).trans
          ((Four.assoc second suffix (.inv suffix)).trans
            ((Four.comp (.refl second) (Four.rightInv suffix)).trans (Four.rightUnit second))))))

def forkFstSquare {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    Cell
      (.comp (ProductTracks.firstProjection (forkBeta p q)) (.step (.root (.betaFst p q))))
      (.comp (betaEtaFst (fork p q)) (.step (.root (.betaFst p q)))) :=
  (Four.assoc _ _ _).trans
    ((Four.comp (.refl _) (liftOld (ProductProjectionNaturality.fstRight p (.root (.betaSnd p q))))).trans
      (liftOld (ProductProjectionNaturality.fstLeft (.root (.betaFst p q)) (.seq (fork p q) (snd b c)))))

def forkSndSquare {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    Cell
      (.comp (ProductTracks.secondProjection (forkBeta p q)) (.step (.root (.betaSnd p q))))
      (.comp (betaEtaSnd (fork p q)) (.step (.root (.betaSnd p q)))) :=
  (Four.assoc _ _ _).trans
    ((Four.comp (.refl _) (liftOld (ProductProjectionNaturality.sndRight p (.root (.betaSnd p q))))).trans
      ((Four.assoc _ _ _).symm.trans
        (Four.comp (liftOld (ProductProjectionNaturality.sndLeft (.root (.betaFst p q)) (.seq (fork p q) (snd b c)))) (.refl _))))

def forkCell {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) : Cell (forkBeta p q) (forkEta p q) :=
  PresentedObservation.reflect PresentedObservation.product (forkBeta p q) (forkEta p q)
    ((cancelProofSuffix (.step (.root (.betaFst p q))) (forkFstSquare p q)).trans (fstCell (fork p q)).symm)
    ((cancelProofSuffix (.step (.root (.betaSnd p q))) (forkSndSquare p q)).trans (sndCell (fork p q)).symm)

def forkOtherOrder {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    Cell (forkLastFirst p q) (forkEta p q) :=
  (embed (CategoryCritical.oldLift
    (Cartesian.Higher.Homotopy.whisker (.seqRight (.copy a))
      (Four.generator (Cartesian.Higher.Generator.tensorExchange
        (Step.root (Root.betaFst p q)) (Step.root (Root.betaSnd p q))))))).symm.trans
      (forkCell p q)

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductCritical
