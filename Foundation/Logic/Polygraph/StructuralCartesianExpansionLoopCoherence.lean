import Foundation.Logic.Polygraph.StructuralCartesianExpansionCritical
import Foundation.Logic.Polygraph.StructuralCartesianProductTriangleCoherence

/-! A derived expansion/restoration loop for arbitrary opaque pairing
arguments. It uses the two projected expansion diagrams and existing eta
coherence; no loop or normalization comparison is added as a generator. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.LoopCoherence
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def forkTracks {a b c : Shape Atom} {p p' : Wire a b} {q q' : Wire a c}
    (first : ProofTrack p p') (second : ProofTrack q q') :=
  seqRightTrack (.copy a) (ProductTracks.tensor first second)

def forkCells {a b c : Shape Atom} {p p' : Wire a b} {q q' : Wire a c}
    {first first' : ProofTrack p p'} {second second' : ProofTrack q q'}
    (left : Cell first first') (right : Cell second second') :
    Cell (forkTracks first second) (forkTracks first' second') :=
  whisker (.seqRight (.copy a)) (PresentedObservation.tensorCells extension left right)

def forkComp {a b c : Shape Atom} {p p' p'' : Wire a b} {q q' q'' : Wire a c}
    (one : ProofTrack p p') (two : ProofTrack p' p'')
    (three : ProofTrack q q') (four : ProofTrack q' q'') :
    Cell (forkTracks (.comp one two) (.comp three four)) (.comp (forkTracks one three) (forkTracks two four)) :=
  whisker (.seqRight (.copy a)) (oldLift (ProductTracks.tensorComp one two three four))

/-- Moving eta backwards across an actual path, derived from eta naturality. -/
def inverseEtaNatural {a b c : Shape Atom} {p q : Wire a (.pair b c)} (path : ProofTrack p q) :
    Cell (.comp path (.inv (.step (.root (.eta q)))))
      (.comp (.inv (.step (.root (.eta p)))) ((Variation.eta a b c).left.track path)) :=
  FourNaturality.cancelPrefix (.step (.root (.eta p)))
    ((Four.assoc (.step (.root (.eta p))) path (.inv (.step (.root (.eta q))))).symm.trans
      ((Four.comp (PresentedObservation.etaNatural extension path).symm (.refl (.inv (.step (.root (.eta q)))))).trans
        ((FourNaturality.undoRight ((Variation.eta a b c).left.track path) (.step (.root (.eta q)))).trans
          (FourNaturality.undoLeft (.step (.root (.eta p))) ((Variation.eta a b c).left.track path)).symm)))

def expandedPair {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Wire.seq (.copy a) (fork (.seq (fst a a) p) (.seq (snd a a) q))

def expand {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Track.step (Step.seqRight (.copy a) (.root (.tensorExpand p q)))

def restore {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Track.comp (.inv (Track.step (Step.root (.eta (expandedPair p q)))))
    (forkTracks (TensorProjectionPeak.fstTail p q) (TensorProjectionPeak.sndTail p q))

def loop {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :=
  Track.comp (expand p q) (restore p q)

def loopCell {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    Cell (loop p q) (.refl (fork p q)) :=
  (Four.assoc _ _ _).symm.trans
    ((Four.comp (inverseEtaNatural (expand p q)) (.refl _)).trans
      ((Four.assoc _ _ _).trans
        ((Four.comp (.refl _) (Four.comp (oldLift (ProductTracks.etaSplit (expand p q))) (.refl _))).trans
          ((Four.comp (.refl _) (forkComp (ProductTracks.firstProjection (expand p q)) (TensorProjectionPeak.fstTail p q)
            (ProductTracks.secondProjection (expand p q)) (TensorProjectionPeak.sndTail p q)).symm).trans
            ((Four.comp (.refl _) (forkCells (fstCell p q) (sndCell p q))).trans
              ((Four.comp (.refl _) (embed (DistributionCritical.embed (ProductCritical.forkCell p q)))).trans
                (Four.leftInv _)))))))

/-- The one-step expansion equals the inverse of the thirteen-step restore. -/
def expansionCell {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) :
    Cell (expand p q) (.inv (restore p q)) :=
  (FourNaturality.undoRight (expand p q) (restore p q)).symm.trans
    ((Four.comp (loopCell p q) (.refl _)).trans (Four.leftUnit _))

theorem restore_count {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) : stepCount (restore p q) = 13 := by
  rfl

theorem loop_count {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) : stepCount (loop p q) = 14 := by
  rfl

/-- The loop cancellation is new relative to the previous pure basis. -/
theorem loop_missing_before (name : Atom) :
    ¬ Nonempty (DistributionCritical.Cell
      (loop (Wire.identity (.atom name)) (Wire.identity (.atom name)))
      (.refl (fork (Wire.identity (.atom name)) (Wire.identity (.atom name))))) := by
  rintro ⟨cell⟩
  have same := congrArg Prod.fst
    (DistributionCritical.Annotation.homotopy_weight TensorProjectionPeak.tensorCoeff_admissible cell)
  change (1 : Int) = 0 at same
  omega

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.LoopCoherence
