import Foundation.Logic.Polygraph.FourAssociation
import Foundation.Logic.Polygraph.StructuralCartesianExpansionCritical

/-! Categorical path-level associator squares and a corner of the pentagon,
derived in the retained presentation. These paste selector compatibility
proofs; no new higher generator is introduced. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.AssociatorPaths
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def categorical {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (cell : CategoryCritical.Cell first second) : Cell first second := embed (DistributionCritical.categoryLift cell)

def alpha {a b c d : Shape Atom} (p : Wire a b) (q : Wire b c) (r : Wire c d) :=
  Track.step (Step.root (.assoc p q r))

def firstPath {a b c d : Shape Atom} {p p' : Wire a b} (path : ProofTrack p p') (q : Wire b c) (r : Wire c d) :
    Cell (.comp (alpha p q r) (seqLeftTrack (.seq q r) path))
      (.comp (seqLeftTrack r (seqLeftTrack q path)) (alpha p' q r)) := by
  have square := FourNaturality.natural (Cells := Generator)
    (fun w : Wire a b => Wire.seq (Wire.seq w q) r) (fun w => Wire.seq w (Wire.seq q r))
    (fun change => Step.seqLeft (.seqLeft change q) r) (fun change => Step.seqLeft change (.seq q r))
    (fun w => alpha w q r) (fun change => (categorical (CategoryCritical.assocFirstNatural change q r)).symm) path
  simpa only [seqLeftTrack, FourNaturality.map_map] using square.symm

def postfixInverse {a b c d : Shape Atom} {p p' : Wire a b} (path : ProofTrack p p') (q : Wire b c) (r : Wire c d) :
    Cell (.comp (seqLeftTrack (.seq q r) path) (.inv (alpha p' q r)))
      (.comp (.inv (alpha p q r)) (seqLeftTrack r (seqLeftTrack q path))) :=
  (FourNaturality.invertSquare (alpha p q r) (seqLeftTrack (.seq q r) path)
    (seqLeftTrack r (seqLeftTrack q path)) (alpha p' q r) (firstPath path q r)).symm

def middleStep {a b c d : Shape Atom} (p : Wire a b) {q q' : Wire b c} (change : Step q q') (r : Wire c d) :
    Cell (.comp (seqLeftTrack r (seqRightTrack p (.step change))) (alpha p q' r))
      (.comp (alpha p q r) (seqRightTrack p (seqLeftTrack r (.step change)))) :=
  (categorical (CategoryCritical.assocMiddleNatural p change r)).symm

def pentagonCorner {a b c d e : Shape Atom} (p : Wire a b) (q : Wire b c) (r : Wire c d) (s : Wire d e) :
    Cell (.comp (.inv (alpha (.seq p q) r s))
      (.comp (seqLeftTrack s (alpha p q r)) (alpha p (.seq q r) s)))
      (.comp (alpha p q (.seq r s)) (.inv (seqRightTrack p (alpha q r s)))) := by
  let a1 := alpha (.seq p q) r s
  let a2 := alpha p q (.seq r s)
  let b1 := seqLeftTrack s (alpha p q r)
  let b2 := alpha p (.seq q r) s
  let b3 := seqRightTrack p (alpha q r s)
  have face : Cell (.comp a1 a2) (.comp (.comp b1 b2) b3) :=
    (categorical (CategoryCritical.pentagonCell p q r s)).trans (by four_assoc)
  exact FourNaturality.invertSquare a1 a2 (.comp b1 b2) b3 face

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.AssociatorPaths
