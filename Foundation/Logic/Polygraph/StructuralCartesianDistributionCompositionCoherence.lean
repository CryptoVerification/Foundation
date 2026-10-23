import Foundation.Logic.Polygraph.StructuralCartesianSubstitutionUnitCoherence

/-! Distribution of a composite prefix and pathwise naturality in the two
outputs, derived from the retained finite local basis. No generator compares
arbitrary normalization paths. Projection tails are cancelled as proof paths;
no noninvertible wire or probability observation is cancelled. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.DistributionComposition
open AssociatorPaths
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
local infixr:70 " ⊙ " => Track.comp

def distribute {x a b c : Shape Atom} (f : Wire x a) (p : Wire a b) (q : Wire a c) :=
  Track.step (Step.root (.forkAfter f p q))

def sequential {x a b c d : Shape Atom} (f : Wire x a) (g : Wire a b) (p : Wire b c) (q : Wire b d) :=
  alpha f g (fork p q) ⊙ (seqRightTrack f (distribute g p q) ⊙ distribute f (.seq g p) (.seq g q))

def combined {x a b c d : Shape Atom} (f : Wire x a) (g : Wire a b) (p : Wire b c) (q : Wire b d) :=
  distribute (.seq f g) p q ⊙ ProjectedTrackNaturality.forkPaths (alpha f g p) (alpha f g q)

def fstAssociation {x a b c d : Shape Atom} (f : Wire x a) (g : Wire a b) (p : Wire b c) (q : Wire b d) :
    Cell (seqLeftTrack (fst c d) (sequential f g p q) ⊙
      .step (.root (.betaFst (.seq f (.seq g p)) (.seq f (.seq g q)))))
      (seqLeftTrack (fst c d) (combined f g p q) ⊙
        .step (.root (.betaFst (.seq f (.seq g p)) (.seq f (.seq g q))))) := by
  let h := fst c d
  let k := fork p q
  let gp := Wire.seq g p
  let gq := Wire.seq g q
  let beta := Step.root (Root.betaFst p q)
  have one : Cell (seqLeftTrack h (sequential f g p q) ⊙
      .step (.root (.betaFst (.seq f gp) (.seq f gq))))
      (seqLeftTrack h (alpha f g k) ⊙ (seqLeftTrack h (seqRightTrack f (distribute g p q)) ⊙
        (alpha f (fork gp gq) h ⊙ seqRightTrack f (.step (.root (.betaFst gp gq)))))) := by
    four_rewrite_ctx (embed (DistributionCritical.fstCell f gp gq))
  have two : Cell
      (seqLeftTrack h (alpha f g k) ⊙ (seqLeftTrack h (seqRightTrack f (distribute g p q)) ⊙
        (alpha f (fork gp gq) h ⊙ seqRightTrack f (.step (.root (.betaFst gp gq))))))
      (seqLeftTrack h (alpha f g k) ⊙ (alpha f (.seq g k) h ⊙
        (seqRightTrack f (seqLeftTrack h (distribute g p q)) ⊙ seqRightTrack f (.step (.root (.betaFst gp gq)))))) := by
    four_rewrite_ctx (UnitSelectionPasting.middlePath f (distribute g p q) h)
  have three : Cell
      (seqLeftTrack h (alpha f g k) ⊙ (alpha f (.seq g k) h ⊙
        (seqRightTrack f (seqLeftTrack h (distribute g p q)) ⊙ seqRightTrack f (.step (.root (.betaFst gp gq))))))
      (seqLeftTrack h (alpha f g k) ⊙ (alpha f (.seq g k) h ⊙
        (seqRightTrack f (alpha g k h) ⊙ seqRightTrack f (seqRightTrack g (.step beta))))) := by
    four_rewrite_ctx (whisker (.seqRight f) (embed (DistributionCritical.fstCell g p q)))
  have four : Cell
      (seqLeftTrack h (alpha f g k) ⊙ (alpha f (.seq g k) h ⊙
        (seqRightTrack f (alpha g k h) ⊙ seqRightTrack f (seqRightTrack g (.step beta)))))
      (alpha (.seq f g) k h ⊙ (alpha f g (.seq k h) ⊙ seqRightTrack f (seqRightTrack g (.step beta)))) := by
    four_rewrite_ctx (categorical (CategoryCritical.pentagonCell f g k h)).symm
  have five : Cell
      (alpha (.seq f g) k h ⊙ (alpha f g (.seq k h) ⊙ seqRightTrack f (seqRightTrack g (.step beta))))
      (alpha (.seq f g) k h ⊙ (seqRightTrack (.seq f g) (.step beta) ⊙ alpha f g p)) := by
    four_rewrite_ctx (categorical (CategoryCritical.assocLastNatural f g beta))
  have otherOne : Cell (seqLeftTrack h (combined f g p q) ⊙
      .step (.root (.betaFst (.seq f gp) (.seq f gq))))
      (seqLeftTrack h (distribute (.seq f g) p q) ⊙
        (.step (.root (.betaFst (.seq (.seq f g) p) (.seq (.seq f g) q))) ⊙ alpha f g p)) := by
    four_rewrite_ctx (oldLift (ProjectedTrackNaturality.fstBoth (alpha f g p) (alpha f g q)))
  have otherTwo : Cell
      (seqLeftTrack h (distribute (.seq f g) p q) ⊙
        (.step (.root (.betaFst (.seq (.seq f g) p) (.seq (.seq f g) q))) ⊙ alpha f g p))
      (alpha (.seq f g) k h ⊙ (seqRightTrack (.seq f g) (.step beta) ⊙ alpha f g p)) := by
    four_rewrite_ctx (embed (DistributionCritical.fstCell (.seq f g) p q))
  exact one.trans (two.trans (three.trans (four.trans (five.trans (otherOne.trans otherTwo).symm))))

def sndAssociation {x a b c d : Shape Atom} (f : Wire x a) (g : Wire a b) (p : Wire b c) (q : Wire b d) :
    Cell (seqLeftTrack (snd c d) (sequential f g p q) ⊙
      .step (.root (.betaSnd (.seq f (.seq g p)) (.seq f (.seq g q)))))
      (seqLeftTrack (snd c d) (combined f g p q) ⊙
        .step (.root (.betaSnd (.seq f (.seq g p)) (.seq f (.seq g q))))) := by
  let h := snd c d
  let k := fork p q
  let gp := Wire.seq g p
  let gq := Wire.seq g q
  let beta := Step.root (Root.betaSnd p q)
  have one : Cell (seqLeftTrack h (sequential f g p q) ⊙
      .step (.root (.betaSnd (.seq f gp) (.seq f gq))))
      (seqLeftTrack h (alpha f g k) ⊙ (seqLeftTrack h (seqRightTrack f (distribute g p q)) ⊙
        (alpha f (fork gp gq) h ⊙ seqRightTrack f (.step (.root (.betaSnd gp gq)))))) := by
    four_rewrite_ctx (embed (DistributionCritical.sndCell f gp gq))
  have two : Cell
      (seqLeftTrack h (alpha f g k) ⊙ (seqLeftTrack h (seqRightTrack f (distribute g p q)) ⊙
        (alpha f (fork gp gq) h ⊙ seqRightTrack f (.step (.root (.betaSnd gp gq))))))
      (seqLeftTrack h (alpha f g k) ⊙ (alpha f (.seq g k) h ⊙
        (seqRightTrack f (seqLeftTrack h (distribute g p q)) ⊙ seqRightTrack f (.step (.root (.betaSnd gp gq)))))) := by
    four_rewrite_ctx (UnitSelectionPasting.middlePath f (distribute g p q) h)
  have three : Cell
      (seqLeftTrack h (alpha f g k) ⊙ (alpha f (.seq g k) h ⊙
        (seqRightTrack f (seqLeftTrack h (distribute g p q)) ⊙ seqRightTrack f (.step (.root (.betaSnd gp gq))))))
      (seqLeftTrack h (alpha f g k) ⊙ (alpha f (.seq g k) h ⊙
        (seqRightTrack f (alpha g k h) ⊙ seqRightTrack f (seqRightTrack g (.step beta))))) := by
    four_rewrite_ctx (whisker (.seqRight f) (embed (DistributionCritical.sndCell g p q)))
  have four : Cell
      (seqLeftTrack h (alpha f g k) ⊙ (alpha f (.seq g k) h ⊙
        (seqRightTrack f (alpha g k h) ⊙ seqRightTrack f (seqRightTrack g (.step beta)))))
      (alpha (.seq f g) k h ⊙ (alpha f g (.seq k h) ⊙ seqRightTrack f (seqRightTrack g (.step beta)))) := by
    four_rewrite_ctx (categorical (CategoryCritical.pentagonCell f g k h)).symm
  have five : Cell
      (alpha (.seq f g) k h ⊙ (alpha f g (.seq k h) ⊙ seqRightTrack f (seqRightTrack g (.step beta))))
      (alpha (.seq f g) k h ⊙ (seqRightTrack (.seq f g) (.step beta) ⊙ alpha f g q)) := by
    four_rewrite_ctx (categorical (CategoryCritical.assocLastNatural f g beta))
  have otherOne : Cell (seqLeftTrack h (combined f g p q) ⊙
      .step (.root (.betaSnd (.seq f gp) (.seq f gq))))
      (seqLeftTrack h (distribute (.seq f g) p q) ⊙
        (.step (.root (.betaSnd (.seq (.seq f g) p) (.seq (.seq f g) q))) ⊙ alpha f g q)) := by
    four_rewrite_ctx (oldLift (ProjectedTrackNaturality.sndBoth (alpha f g p) (alpha f g q)))
  have otherTwo : Cell
      (seqLeftTrack h (distribute (.seq f g) p q) ⊙
        (.step (.root (.betaSnd (.seq (.seq f g) p) (.seq (.seq f g) q))) ⊙ alpha f g q))
      (alpha (.seq f g) k h ⊙ (seqRightTrack (.seq f g) (.step beta) ⊙ alpha f g q)) := by
    four_rewrite_ctx (embed (DistributionCritical.sndCell (.seq f g) p q))
  exact one.trans (two.trans (three.trans (four.trans (five.trans (otherOne.trans otherTwo).symm))))

/-- Associativity of distribution, with both actual paths constructed from
local steps. Output reconstruction is applied only to higher proof cells. -/
def association {x a b c d : Shape Atom} (f : Wire x a) (g : Wire a b) (p : Wire b c) (q : Wire b d) :
    Cell (sequential f g p q) (combined f g p q) :=
  PresentedObservation.reflect extension _ _
    (SubstitutionUnit.cancelSuffix _ (fstAssociation f g p q))
    (SubstitutionUnit.cancelSuffix _ (sndAssociation f g p q))

/-- The same square after cancelling only the initial associator proof. -/
def associationCorner {x a b c d : Shape Atom} (f : Wire x a) (g : Wire a b) (p : Wire b c) (q : Wire b d) :
    Cell (seqRightTrack f (distribute g p q) ⊙ distribute f (.seq g p) (.seq g q))
      (.inv (alpha f g (fork p q)) ⊙ combined f g p q) :=
  ((Four.comp (.refl (.inv (alpha f g (fork p q)))) (association f g p q).symm).trans
    (FourNaturality.undoInversePrefix _ _)).symm

def argumentFirst {x a b c : Shape Atom} (f : Wire x a) {p p' : Wire a b} {q q' : Wire a c}
    (first : ProofTrack p p') (second : ProofTrack q q') :=
  seqRightTrack f (ProjectedTrackNaturality.forkPaths first second) ⊙ distribute f p' q'

def argumentSecond {x a b c : Shape Atom} (f : Wire x a) {p p' : Wire a b} {q q' : Wire a c}
    (first : ProofTrack p p') (second : ProofTrack q q') :=
  distribute f p q ⊙ ProjectedTrackNaturality.forkPaths (seqRightTrack f first) (seqRightTrack f second)

def fstArguments {x a b c : Shape Atom} (f : Wire x a) {p p' : Wire a b} {q q' : Wire a c}
    (first : ProofTrack p p') (second : ProofTrack q q') :
    Cell (seqLeftTrack (fst b c) (argumentFirst f first second) ⊙ .step (.root (.betaFst (.seq f p') (.seq f q'))))
      (seqLeftTrack (fst b c) (argumentSecond f first second) ⊙ .step (.root (.betaFst (.seq f p') (.seq f q')))) := by
  let h := fst b c
  let paths := ProjectedTrackNaturality.forkPaths first second
  have one : Cell
      (seqLeftTrack h (argumentFirst f first second) ⊙ .step (.root (.betaFst (.seq f p') (.seq f q'))))
      (seqLeftTrack h (seqRightTrack f paths) ⊙
        (alpha f (fork p' q') h ⊙ seqRightTrack f (.step (.root (.betaFst p' q'))))) := by
    four_rewrite_ctx (embed (DistributionCritical.fstCell f p' q'))
  have two : Cell
      (seqLeftTrack h (seqRightTrack f paths) ⊙
        (alpha f (fork p' q') h ⊙ seqRightTrack f (.step (.root (.betaFst p' q')))))
      (alpha f (fork p q) h ⊙
        (seqRightTrack f (seqLeftTrack h paths) ⊙ seqRightTrack f (.step (.root (.betaFst p' q'))))) := by
    four_rewrite_ctx (UnitSelectionPasting.middlePath f paths h)
  have three : Cell
      (alpha f (fork p q) h ⊙
        (seqRightTrack f (seqLeftTrack h paths) ⊙ seqRightTrack f (.step (.root (.betaFst p' q')))))
      (alpha f (fork p q) h ⊙ (seqRightTrack f (.step (.root (.betaFst p q))) ⊙ seqRightTrack f first)) := by
    four_rewrite_ctx (whisker (.seqRight f) (oldLift (ProjectedTrackNaturality.fstBoth first second)))
  have other : Cell
      (seqLeftTrack h (argumentSecond f first second) ⊙ .step (.root (.betaFst (.seq f p') (.seq f q'))))
      (alpha f (fork p q) h ⊙ (seqRightTrack f (.step (.root (.betaFst p q))) ⊙ seqRightTrack f first)) := by
    four_rewrite_ctx (SelectionPasting.fstSquare f p q (seqRightTrack f first) (seqRightTrack f second))
  exact one.trans (two.trans (three.trans other.symm))

def sndArguments {x a b c : Shape Atom} (f : Wire x a) {p p' : Wire a b} {q q' : Wire a c}
    (first : ProofTrack p p') (second : ProofTrack q q') :
    Cell (seqLeftTrack (snd b c) (argumentFirst f first second) ⊙ .step (.root (.betaSnd (.seq f p') (.seq f q'))))
      (seqLeftTrack (snd b c) (argumentSecond f first second) ⊙ .step (.root (.betaSnd (.seq f p') (.seq f q')))) := by
  let h := snd b c
  let paths := ProjectedTrackNaturality.forkPaths first second
  have one : Cell
      (seqLeftTrack h (argumentFirst f first second) ⊙ .step (.root (.betaSnd (.seq f p') (.seq f q'))))
      (seqLeftTrack h (seqRightTrack f paths) ⊙
        (alpha f (fork p' q') h ⊙ seqRightTrack f (.step (.root (.betaSnd p' q'))))) := by
    four_rewrite_ctx (embed (DistributionCritical.sndCell f p' q'))
  have two : Cell
      (seqLeftTrack h (seqRightTrack f paths) ⊙
        (alpha f (fork p' q') h ⊙ seqRightTrack f (.step (.root (.betaSnd p' q')))))
      (alpha f (fork p q) h ⊙
        (seqRightTrack f (seqLeftTrack h paths) ⊙ seqRightTrack f (.step (.root (.betaSnd p' q'))))) := by
    four_rewrite_ctx (UnitSelectionPasting.middlePath f paths h)
  have three : Cell
      (alpha f (fork p q) h ⊙
        (seqRightTrack f (seqLeftTrack h paths) ⊙ seqRightTrack f (.step (.root (.betaSnd p' q')))))
      (alpha f (fork p q) h ⊙ (seqRightTrack f (.step (.root (.betaSnd p q))) ⊙ seqRightTrack f second)) := by
    four_rewrite_ctx (whisker (.seqRight f) (oldLift (ProjectedTrackNaturality.sndBoth first second)))
  have other : Cell
      (seqLeftTrack h (argumentSecond f first second) ⊙ .step (.root (.betaSnd (.seq f p') (.seq f q'))))
      (alpha f (fork p q) h ⊙ (seqRightTrack f (.step (.root (.betaSnd p q))) ⊙ seqRightTrack f second)) := by
    four_rewrite_ctx (SelectionPasting.sndSquare f p q (seqRightTrack f first) (seqRightTrack f second))
  exact one.trans (two.trans (three.trans other.symm))

/-- Distribution is natural in both arbitrary argument paths, including
inverse and composite paths and paths in the discarded output branch. -/
def arguments {x a b c : Shape Atom} (f : Wire x a) {p p' : Wire a b} {q q' : Wire a c}
    (first : ProofTrack p p') (second : ProofTrack q q') :
    Cell (argumentFirst f first second) (argumentSecond f first second) :=
  PresentedObservation.reflect extension _ _
    (SubstitutionUnit.cancelSuffix _ (fstArguments f first second))
    (SubstitutionUnit.cancelSuffix _ (sndArguments f first second))

def prefixFirst {x a b c : Shape Atom} {f f' : Wire x a} (path : ProofTrack f f') (p : Wire a b) (q : Wire a c) :=
  seqLeftTrack (fork p q) path ⊙ distribute f' p q

def prefixSecond {x a b c : Shape Atom} {f f' : Wire x a} (path : ProofTrack f f') (p : Wire a b) (q : Wire a c) :=
  distribute f p q ⊙ ProjectedTrackNaturality.forkPaths (seqLeftTrack p path) (seqLeftTrack q path)

def fstPrefix {x a b c : Shape Atom} {f f' : Wire x a} (path : ProofTrack f f') (p : Wire a b) (q : Wire a c) :
    Cell (seqLeftTrack (fst b c) (prefixFirst path p q) ⊙ .step (.root (.betaFst (.seq f' p) (.seq f' q))))
      (seqLeftTrack (fst b c) (prefixSecond path p q) ⊙ .step (.root (.betaFst (.seq f' p) (.seq f' q)))) := by
  let h := fst b c
  let beta := Step.root (Root.betaFst p q)
  have one : Cell
      (seqLeftTrack h (prefixFirst path p q) ⊙ .step (.root (.betaFst (.seq f' p) (.seq f' q))))
      (seqLeftTrack h (seqLeftTrack (fork p q) path) ⊙
        (alpha f' (fork p q) h ⊙ seqRightTrack f' (.step beta))) := by
    four_rewrite_ctx (embed (DistributionCritical.fstCell f' p q))
  have two : Cell
      (seqLeftTrack h (seqLeftTrack (fork p q) path) ⊙
        (alpha f' (fork p q) h ⊙ seqRightTrack f' (.step beta)))
      (alpha f (fork p q) h ⊙ (seqLeftTrack (.seq (fork p q) h) path ⊙ seqRightTrack f' (.step beta))) := by
    four_rewrite_ctx (firstPath path (fork p q) h).symm
  have three : Cell
      (alpha f (fork p q) h ⊙ (seqLeftTrack (.seq (fork p q) h) path ⊙ seqRightTrack f' (.step beta)))
      (alpha f (fork p q) h ⊙ (seqRightTrack f (.step beta) ⊙ seqLeftTrack p path)) := by
    four_rewrite_ctx (SubstitutionUnit.exchangeStep path beta)
  have other : Cell
      (seqLeftTrack h (prefixSecond path p q) ⊙ .step (.root (.betaFst (.seq f' p) (.seq f' q))))
      (alpha f (fork p q) h ⊙ (seqRightTrack f (.step beta) ⊙ seqLeftTrack p path)) := by
    four_rewrite_ctx (SelectionPasting.fstSquare f p q (seqLeftTrack p path) (seqLeftTrack q path))
  exact one.trans (two.trans (three.trans other.symm))

def sndPrefix {x a b c : Shape Atom} {f f' : Wire x a} (path : ProofTrack f f') (p : Wire a b) (q : Wire a c) :
    Cell (seqLeftTrack (snd b c) (prefixFirst path p q) ⊙ .step (.root (.betaSnd (.seq f' p) (.seq f' q))))
      (seqLeftTrack (snd b c) (prefixSecond path p q) ⊙ .step (.root (.betaSnd (.seq f' p) (.seq f' q)))) := by
  let h := snd b c
  let beta := Step.root (Root.betaSnd p q)
  have one : Cell
      (seqLeftTrack h (prefixFirst path p q) ⊙ .step (.root (.betaSnd (.seq f' p) (.seq f' q))))
      (seqLeftTrack h (seqLeftTrack (fork p q) path) ⊙
        (alpha f' (fork p q) h ⊙ seqRightTrack f' (.step beta))) := by
    four_rewrite_ctx (embed (DistributionCritical.sndCell f' p q))
  have two : Cell
      (seqLeftTrack h (seqLeftTrack (fork p q) path) ⊙
        (alpha f' (fork p q) h ⊙ seqRightTrack f' (.step beta)))
      (alpha f (fork p q) h ⊙ (seqLeftTrack (.seq (fork p q) h) path ⊙ seqRightTrack f' (.step beta))) := by
    four_rewrite_ctx (firstPath path (fork p q) h).symm
  have three : Cell
      (alpha f (fork p q) h ⊙ (seqLeftTrack (.seq (fork p q) h) path ⊙ seqRightTrack f' (.step beta)))
      (alpha f (fork p q) h ⊙ (seqRightTrack f (.step beta) ⊙ seqLeftTrack q path)) := by
    four_rewrite_ctx (SubstitutionUnit.exchangeStep path beta)
  have other : Cell
      (seqLeftTrack h (prefixSecond path p q) ⊙ .step (.root (.betaSnd (.seq f' p) (.seq f' q))))
      (alpha f (fork p q) h ⊙ (seqRightTrack f (.step beta) ⊙ seqLeftTrack q path)) := by
    four_rewrite_ctx (SelectionPasting.sndSquare f p q (seqLeftTrack p path) (seqLeftTrack q path))
  exact one.trans (two.trans (three.trans other.symm))

/-- Naturality in the common prefix. Both copies receive the same path;
this is a syntactic higher comparison, not independent resampling. -/
def prefixPath {x a b c : Shape Atom} {f f' : Wire x a} (path : ProofTrack f f') (p : Wire a b) (q : Wire a c) :
    Cell (prefixFirst path p q) (prefixSecond path p q) :=
  PresentedObservation.reflect extension _ _
    (SubstitutionUnit.cancelSuffix _ (fstPrefix path p q))
    (SubstitutionUnit.cancelSuffix _ (sndPrefix path p q))

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.DistributionComposition
