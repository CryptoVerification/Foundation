import Foundation.Logic.Polygraph.StructuralCartesianDistributionCritical
import Foundation.Logic.Polygraph.StructuralCartesianPresentedObservation
import Foundation.Logic.Polygraph.StructuralCartesianProductProjectionNaturality

/-! Identity/distribution coherence is derived by projecting to the two
outputs, using the two local distribution/projection diagrams and categorical
unit diagrams, then reconstructing. It is not a new higher generator. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.DistributionCritical
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def categoryLift {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (cell : CategoryCritical.Cell first second) : Cell first second := embed (ProductCritical.embed cell)

def oldLift {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (cell : Homotopy first second) : Cell first second := categoryLift (CategoryCritical.oldLift cell)

def extension : PresentedObservation.Extension Atom where
  Generator := Generator
  embed := oldLift
  whisker := whisker

def forkChanges {a b c : Shape Atom} {p p' : Wire a b} {q q' : Wire a c}
    (first : Step p p') (second : Step q q') :=
  Track.comp (.step (ProductProjectionNaturality.forkLeft first q))
    (.step (ProductProjectionNaturality.forkRight p' second))

def forkFstNatural {a b c : Shape Atom} {p p' : Wire a b} {q q' : Wire a c}
    (first : Step p p') (second : Step q q') :
    Homotopy (.comp (seqLeftTrack (fst b c) (forkChanges first second)) (.step (.root (.betaFst p' q'))))
      (.comp (.step (.root (.betaFst p q))) (.step first)) :=
  (Four.assoc _ _ _).trans
    ((Four.comp (.refl _) (ProductProjectionNaturality.fstRight p' second)).trans
      (ProductProjectionNaturality.fstLeft first q))

def forkSndNatural {a b c : Shape Atom} {p p' : Wire a b} {q q' : Wire a c}
    (first : Step p p') (second : Step q q') :
    Homotopy (.comp (seqLeftTrack (snd b c) (forkChanges first second)) (.step (.root (.betaSnd p' q'))))
      (.comp (.step (.root (.betaSnd p q))) (.step second)) :=
  (Four.assoc _ _ _).trans
    ((Four.comp (.refl _) (ProductProjectionNaturality.sndRight p' second)).trans
      ((Four.assoc _ _ _).symm.trans (Four.comp (ProductProjectionNaturality.sndLeft first q) (.refl _))))

def identityDistributed {a b c : Shape Atom} (q : Wire a b) (r : Wire a c) :=
  Track.comp (.step (Step.root (.forkAfter (.identity a) q r)))
    (forkChanges (Step.root (.leftId q)) (Step.root (.leftId r)))

def identityDirect {a b c : Shape Atom} (q : Wire a b) (r : Wire a c) :=
  Track.step (Step.root (Root.leftId (fork q r)))

def identityFstSquare {a b c : Shape Atom} (q : Wire a b) (r : Wire a c) :
    Cell (.comp (ProductTracks.firstProjection (identityDistributed q r)) (.step (.root (.betaFst q r))))
      (.comp (ProductTracks.firstProjection (identityDirect q r)) (.step (.root (.betaFst q r)))) :=
  (Four.assoc _ _ _).trans
    ((Four.comp (.refl _) (oldLift (forkFstNatural (.root (.leftId q)) (.root (.leftId r))))).trans
      ((Four.assoc _ _ _).symm.trans
        ((Four.comp (fstCell (.identity a) q r) (.refl _)).trans
          ((Four.assoc _ _ _).trans
            ((Four.comp (.refl _) (categoryLift (CategoryCritical.leftNatural (.root (.betaFst q r)))).symm).trans
              ((Four.assoc _ _ _).symm.trans
                (Four.comp (categoryLift (CategoryCritical.leftUnitCell (fork q r) (fst b c))) (.refl _))))))))

def identitySndSquare {a b c : Shape Atom} (q : Wire a b) (r : Wire a c) :
    Cell (.comp (ProductTracks.secondProjection (identityDistributed q r)) (.step (.root (.betaSnd q r))))
      (.comp (ProductTracks.secondProjection (identityDirect q r)) (.step (.root (.betaSnd q r)))) :=
  (Four.assoc _ _ _).trans
    ((Four.comp (.refl _) (oldLift (forkSndNatural (.root (.leftId q)) (.root (.leftId r))))).trans
      ((Four.assoc _ _ _).symm.trans
        ((Four.comp (sndCell (.identity a) q r) (.refl _)).trans
          ((Four.assoc _ _ _).trans
            ((Four.comp (.refl _) (categoryLift (CategoryCritical.leftNatural (.root (.betaSnd q r)))).symm).trans
              ((Four.assoc _ _ _).symm.trans
                (Four.comp (categoryLift (CategoryCritical.leftUnitCell (fork q r) (snd b c))) (.refl _))))))))

def cancelProofSuffix {a b : Shape Atom} {p q r : Wire a b} {first second : ProofTrack p q}
    (suffix : ProofTrack q r) (square : Cell (.comp first suffix) (.comp second suffix)) : Cell first second :=
  (Four.rightUnit (G := Generator) first).symm.trans
    ((Four.comp (.refl first) (Four.rightInv suffix).symm).trans
      ((Four.assoc first suffix (.inv suffix)).symm.trans
        ((Four.comp square (.refl (.inv suffix))).trans
          ((Four.assoc second suffix (.inv suffix)).trans
            ((Four.comp (.refl second) (Four.rightInv suffix)).trans (Four.rightUnit second))))))

def identityCell {a b c : Shape Atom} (q : Wire a b) (r : Wire a c) :
    Cell (identityDistributed q r) (identityDirect q r) :=
  PresentedObservation.reflect extension (identityDistributed q r) (identityDirect q r)
    (cancelProofSuffix (.step (.root (.betaFst q r))) (identityFstSquare q r))
    (cancelProofSuffix (.step (.root (.betaSnd q r))) (identitySndSquare q r))

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.DistributionCritical
