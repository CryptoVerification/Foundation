import Foundation.Logic.Polygraph.StructuralCartesianProductProjectionNaturality
import Foundation.Logic.Polygraph.StructuralCartesianProductTracks

/-! Projection argument diagrams extended to actual finite paths, including
inverses and erased branches. Only old argument/exchange cells are used. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProjectedTrackNaturality
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

private theorem mapIdentity {a b : Shape Atom} {p q : Wire a b} (path : ProofTrack p q) :
    path.map (fun x => x) (fun change => change) = path := by
  induction path <;> simp_all only [Track.map]

def forkFirst {a b c : Shape Atom} {p p' : Wire a b} (path : ProofTrack p p') (q : Wire a c) :=
  seqRightTrack (.copy a) (tensorLeftTrack q path)

def forkLast {a b c : Shape Atom} (p : Wire a b) {q q' : Wire a c} (path : ProofTrack q q') :=
  seqRightTrack (.copy a) (tensorRightTrack p path)

def fstFirst {a b c : Shape Atom} {p p' : Wire a b} (path : ProofTrack p p') (q : Wire a c) :
    Homotopy (.comp (seqLeftTrack (fst b c) (forkFirst path q)) (.step (.root (.betaFst p' q))))
      (.comp (.step (.root (.betaFst p q))) path) := by
  have square := FourNaturality.natural (Cells := Generator)
    (fun w : Wire a b => Wire.seq (fork w q) (fst b c)) (fun w => w)
    (fun change => Step.seqLeft (ProductProjectionNaturality.forkLeft change q) (fst b c))
    (fun change => change) (fun w => Track.step (Step.root (.betaFst w q)))
    (fun change => ProductProjectionNaturality.fstLeft change q) path
  simpa only [forkFirst, seqLeftTrack, seqRightTrack, tensorLeftTrack, FourNaturality.map_map,
    ProductProjectionNaturality.forkLeft, Cartesian.fork, mapIdentity] using square

def sndLast {a b c : Shape Atom} (p : Wire a b) {q q' : Wire a c} (path : ProofTrack q q') :
    Homotopy (.comp (seqLeftTrack (snd b c) (forkLast p path)) (.step (.root (.betaSnd p q'))))
      (.comp (.step (.root (.betaSnd p q))) path) := by
  have square := FourNaturality.natural (Cells := Generator)
    (fun w : Wire a c => Wire.seq (fork p w) (snd b c)) (fun w => w)
    (fun change => Step.seqLeft (ProductProjectionNaturality.forkRight p change) (snd b c))
    (fun change => change) (fun w => Track.step (Step.root (.betaSnd p w)))
    (fun change => ProductProjectionNaturality.sndRight p change) path
  simpa only [forkLast, seqLeftTrack, seqRightTrack, tensorRightTrack, FourNaturality.map_map,
    ProductProjectionNaturality.forkRight, Cartesian.fork, mapIdentity] using square

def fstLast {a b c : Shape Atom} (p : Wire a b) : {q q' : Wire a c} → (path : ProofTrack q q') →
    Homotopy (.comp (seqLeftTrack (fst b c) (forkLast p path)) (.step (.root (.betaFst p q'))))
      (.step (.root (.betaFst p q)))
  | _, _, .refl _ => Four.leftUnit _
  | _, _, .step change => ProductProjectionNaturality.fstRight p change
  | _, _, .comp one two =>
      (Four.assoc _ _ _).trans ((Four.comp (.refl _) (fstLast p two)).trans (fstLast p one))
  | _, _, .inv child =>
      (Four.comp (.refl _) (fstLast p child).symm).trans (FourNaturality.undoInversePrefix _ _)

def sndFirst {a b c : Shape Atom} : {p p' : Wire a b} → (path : ProofTrack p p') → (q : Wire a c) →
    Homotopy (.comp (seqLeftTrack (snd b c) (forkFirst path q)) (.step (.root (.betaSnd p' q))))
      (.step (.root (.betaSnd p q)))
  | _, _, .refl _, _ => Four.leftUnit _
  | _, _, .step change, q => ProductProjectionNaturality.sndLeft change q
  | _, _, .comp one two, q =>
      (Four.assoc _ _ _).trans ((Four.comp (.refl _) (sndFirst two q)).trans (sndFirst one q))
  | _, _, .inv child, q =>
      (Four.comp (.refl _) (sndFirst child q).symm).trans (FourNaturality.undoInversePrefix _ _)

def forkPaths {a b c : Shape Atom} {p p' : Wire a b} {q q' : Wire a c}
    (first : ProofTrack p p') (second : ProofTrack q q') :=
  Track.comp (forkFirst first q) (forkLast p' second)

def fstBoth {a b c : Shape Atom} {p p' : Wire a b} {q q' : Wire a c}
    (first : ProofTrack p p') (second : ProofTrack q q') :
    Homotopy (.comp (seqLeftTrack (fst b c) (forkPaths first second)) (.step (.root (.betaFst p' q'))))
      (.comp (.step (.root (.betaFst p q))) first) :=
  (Four.assoc _ _ _).trans ((Four.comp (.refl _) (fstLast p' second)).trans (fstFirst first q))

def sndBoth {a b c : Shape Atom} {p p' : Wire a b} {q q' : Wire a c}
    (first : ProofTrack p p') (second : ProofTrack q q') :
    Homotopy (.comp (seqLeftTrack (snd b c) (forkPaths first second)) (.step (.root (.betaSnd p' q'))))
      (.comp (.step (.root (.betaSnd p q))) second) :=
  (Four.assoc _ _ _).trans
    ((Four.comp (.refl _) (sndLast p' second)).trans
      ((Four.assoc _ _ _).symm.trans (Four.comp (sndFirst first q) (.refl _))))

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProjectedTrackNaturality
