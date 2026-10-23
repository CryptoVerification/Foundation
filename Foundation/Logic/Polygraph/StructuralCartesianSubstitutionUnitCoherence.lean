import Foundation.Logic.Polygraph.StructuralCartesianSelectionUnitCoherence
import Foundation.Logic.Polygraph.FourAssociationContext

/-! Left unit for the actual seqNormal substitution calculation, following
the actual identity normalization, for every typed routing layout. The proof
uses atomic selection units and reconstructs product comparisons from their
actual projected higher cells. No normalization generator is added. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.SubstitutionUnit
open TypedRouting
open AssociatorPaths
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
local infixr:70 " ⊙ " => Track.comp

def unitLayout {a b : Shape Atom} (layout : Layout a b) : Layout a b :=
  substitute (a := a) (b := a) (c := b) (universal a) layout

def correction {a : Shape Atom} : {b : Shape Atom} → (layout : Layout a b) → ProofTrack (reify layout) (reify (unitLayout layout))
  | .atom _, slot => SelectionUnit.correction slot
  | .unit, _ => .refl (Wire.discard a)
  | .pair _ _, layout => ProjectedTrackNaturality.forkPaths (correction layout.1) (correction layout.2)

theorem fork_count {a b c : Shape Atom} {p p' : Wire a b} {q q' : Wire a c}
    (first : ProofTrack p p') (second : ProofTrack q q') :
    stepCount (ProjectedTrackNaturality.forkPaths first second) = stepCount first + stepCount second := by
  simp only [ProjectedTrackNaturality.forkPaths, ProjectedTrackNaturality.forkFirst, ProjectedTrackNaturality.forkLast,
    seqRightTrack, tensorLeftTrack, tensorRightTrack, stepCount, stepCount_map]

theorem correction_count {a b : Shape Atom} (layout : Layout a b) : stepCount (correction (a := a) (b := b) layout) = 0 := by
  induction b with
  | atom => exact SelectionUnit.correction_count layout
  | unit => rfl
  | pair b c one two =>
      rw [correction, fork_count, one layout.1, two layout.2]

def first {a b : Shape Atom} (layout : Layout a b) :=
  seqLeftTrack (reify layout) (identityNormal a).toTrack ⊙
    (seqNormal (a := a) (b := a) (universal a) (c := b) layout).toTrack

def second {a b : Shape Atom} (layout : Layout a b) :=
  Track.step (Step.root (.leftId (reify layout))) ⊙ correction (a := a) (b := b) layout

def exchangeStep {a b c : Shape Atom} {p p' : Wire a b} (path : ProofTrack p p')
    {q q' : Wire b c} (change : Step q q') :
    Cell (seqLeftTrack q path ⊙ seqRightTrack p' (.step change))
      (seqRightTrack p (.step change) ⊙ seqLeftTrack q' path) := by
  have square := FourNaturality.natural (Cells := Generator)
    (fun w : Wire a b => Wire.seq w q) (fun w => Wire.seq w q')
    (fun edge => Step.seqLeft edge q) (fun edge => Step.seqLeft edge q')
    (fun w => Track.step (Step.seqRight w change))
    (fun edge => oldLift (.generator (.seqExchange edge change))) path
  simpa only [seqLeftTrack, seqRightTrack, Track.map] using square

def cancelSuffix {a b : Shape Atom} {p q r : Wire a b} {one two : ProofTrack p q} (suffix : ProofTrack q r)
    (cell : Cell (one ⊙ suffix) (two ⊙ suffix)) : Cell one two :=
  (Four.rightUnit (G := Generator) one).symm.trans
    ((Four.comp (.refl one) (Four.rightInv suffix).symm).trans
      ((Four.assoc one suffix (.inv suffix)).symm.trans
        ((Four.comp cell (.refl (.inv suffix))).trans
          ((Four.assoc two suffix (.inv suffix)).trans
            ((Four.comp (.refl two) (Four.rightInv suffix)).trans (Four.rightUnit two))))))

def pairFst {a b c : Shape Atom} (left : Layout a b) (right : Layout a c)
    (child : Cell (first (a := a) (b := b) left) (second (a := a) (b := b) left)) :
    Cell (ProductTracks.firstProjection (first (a := a) (b := .pair b c) (left,right)) ⊙
      .step (.root (.betaFst (reify (unitLayout left)) (reify (unitLayout right)))))
      (ProductTracks.firstProjection (second (a := a) (b := .pair b c) (left,right)) ⊙
        .step (.root (.betaFst (reify (unitLayout left)) (reify (unitLayout right))))) := by
  let p : Wire a b := reify left
  let q : Wire a c := reify right
  let v : Wire a a := reify (universal a)
  let n := (identityNormal a).toTrack
  let l := (seqNormal (a := a) (b := a) (universal a) (c := b) left).toTrack
  let r := (seqNormal (a := a) (b := a) (universal a) (c := c) right).toTrack
  let beta := Step.root (Root.betaFst p q)
  have one : Cell (ProductTracks.firstProjection (first (a := a) (b := .pair b c) (left,right)) ⊙
      .step (.root (.betaFst (reify (unitLayout left)) (reify (unitLayout right)))))
      (seqLeftTrack (fst b c) (seqLeftTrack (fork p q) n) ⊙
        (alpha v (fork p q) (fst b c) ⊙ (seqRightTrack v (.step beta) ⊙ l))) := by
    four_rewrite_ctx (SelectionPasting.fstSquare v p q l r)
  have two : Cell
      (seqLeftTrack (fst b c) (seqLeftTrack (fork p q) n) ⊙
        (alpha v (fork p q) (fst b c) ⊙ (seqRightTrack v (.step beta) ⊙ l)))
      (alpha (.identity a) (fork p q) (fst b c) ⊙
        (seqLeftTrack (.seq (fork p q) (fst b c)) n ⊙ (seqRightTrack v (.step beta) ⊙ l))) := by
    four_rewrite_ctx (firstPath n (fork p q) (fst b c)).symm
  have three : Cell
      (alpha (.identity a) (fork p q) (fst b c) ⊙
        (seqLeftTrack (.seq (fork p q) (fst b c)) n ⊙ (seqRightTrack v (.step beta) ⊙ l)))
      (alpha (.identity a) (fork p q) (fst b c) ⊙
        (seqRightTrack (.identity a) (.step beta) ⊙ (seqLeftTrack p n ⊙ l))) := by
    four_rewrite_ctx (exchangeStep n beta)
  have four : Cell
      (alpha (.identity a) (fork p q) (fst b c) ⊙
        (seqRightTrack (.identity a) (.step beta) ⊙ (seqLeftTrack p n ⊙ l)))
      (alpha (.identity a) (fork p q) (fst b c) ⊙
        (seqRightTrack (.identity a) (.step beta) ⊙ (.step (.root (.leftId p)) ⊙ correction (a := a) left))) := by
    four_rewrite_ctx child
  have five : Cell
      (alpha (.identity a) (fork p q) (fst b c) ⊙
        (seqRightTrack (.identity a) (.step beta) ⊙ (.step (.root (.leftId p)) ⊙ correction (a := a) left)))
      (alpha (.identity a) (fork p q) (fst b c) ⊙
        (.step (.root (.leftId (.seq (fork p q) (fst b c)))) ⊙ (.step beta ⊙ correction (a := a) left))) := by
    four_rewrite_ctx (categorical (CategoryCritical.leftNatural beta)).symm
  have six : Cell
      (alpha (.identity a) (fork p q) (fst b c) ⊙
        (.step (.root (.leftId (.seq (fork p q) (fst b c)))) ⊙ (.step beta ⊙ correction (a := a) left)))
      (seqLeftTrack (fst b c) (.step (.root (.leftId (fork p q)))) ⊙ (.step beta ⊙ correction (a := a) left)) := by
    four_rewrite_ctx (categorical (CategoryCritical.leftUnitCell (fork p q) (fst b c)))
  have other : Cell (ProductTracks.firstProjection (second (a := a) (b := .pair b c) (left,right)) ⊙
        .step (.root (.betaFst (reify (unitLayout left)) (reify (unitLayout right)))))
      (seqLeftTrack (fst b c) (.step (.root (.leftId (fork p q)))) ⊙ (.step beta ⊙ correction (a := a) left)) := by
    four_rewrite_ctx (oldLift (ProjectedTrackNaturality.fstBoth (correction (a := a) left) (correction (a := a) right)))
  exact one.trans (two.trans (three.trans (four.trans (five.trans (six.trans other.symm)))))

def pairSnd {a b c : Shape Atom} (left : Layout a b) (right : Layout a c)
    (child : Cell (first (a := a) (b := c) right) (second (a := a) (b := c) right)) :
    Cell (ProductTracks.secondProjection (first (a := a) (b := .pair b c) (left,right)) ⊙
      .step (.root (.betaSnd (reify (unitLayout left)) (reify (unitLayout right)))))
      (ProductTracks.secondProjection (second (a := a) (b := .pair b c) (left,right)) ⊙
        .step (.root (.betaSnd (reify (unitLayout left)) (reify (unitLayout right))))) := by
  let p : Wire a b := reify left
  let q : Wire a c := reify right
  let v : Wire a a := reify (universal a)
  let n := (identityNormal a).toTrack
  let l := (seqNormal (a := a) (b := a) (universal a) (c := b) left).toTrack
  let r := (seqNormal (a := a) (b := a) (universal a) (c := c) right).toTrack
  let beta := Step.root (Root.betaSnd p q)
  have one : Cell (ProductTracks.secondProjection (first (a := a) (b := .pair b c) (left,right)) ⊙
      .step (.root (.betaSnd (reify (unitLayout left)) (reify (unitLayout right)))))
      (seqLeftTrack (snd b c) (seqLeftTrack (fork p q) n) ⊙
        (alpha v (fork p q) (snd b c) ⊙ (seqRightTrack v (.step beta) ⊙ r))) := by
    four_rewrite_ctx (SelectionPasting.sndSquare v p q l r)
  have two : Cell
      (seqLeftTrack (snd b c) (seqLeftTrack (fork p q) n) ⊙
        (alpha v (fork p q) (snd b c) ⊙ (seqRightTrack v (.step beta) ⊙ r)))
      (alpha (.identity a) (fork p q) (snd b c) ⊙
        (seqLeftTrack (.seq (fork p q) (snd b c)) n ⊙ (seqRightTrack v (.step beta) ⊙ r))) := by
    four_rewrite_ctx (firstPath n (fork p q) (snd b c)).symm
  have three : Cell
      (alpha (.identity a) (fork p q) (snd b c) ⊙
        (seqLeftTrack (.seq (fork p q) (snd b c)) n ⊙ (seqRightTrack v (.step beta) ⊙ r)))
      (alpha (.identity a) (fork p q) (snd b c) ⊙
        (seqRightTrack (.identity a) (.step beta) ⊙ (seqLeftTrack q n ⊙ r))) := by
    four_rewrite_ctx (exchangeStep n beta)
  have four : Cell
      (alpha (.identity a) (fork p q) (snd b c) ⊙
        (seqRightTrack (.identity a) (.step beta) ⊙ (seqLeftTrack q n ⊙ r)))
      (alpha (.identity a) (fork p q) (snd b c) ⊙
        (seqRightTrack (.identity a) (.step beta) ⊙ (.step (.root (.leftId q)) ⊙ correction (a := a) right))) := by
    four_rewrite_ctx child
  have five : Cell
      (alpha (.identity a) (fork p q) (snd b c) ⊙
        (seqRightTrack (.identity a) (.step beta) ⊙ (.step (.root (.leftId q)) ⊙ correction (a := a) right)))
      (alpha (.identity a) (fork p q) (snd b c) ⊙
        (.step (.root (.leftId (.seq (fork p q) (snd b c)))) ⊙ (.step beta ⊙ correction (a := a) right))) := by
    four_rewrite_ctx (categorical (CategoryCritical.leftNatural beta)).symm
  have six : Cell
      (alpha (.identity a) (fork p q) (snd b c) ⊙
        (.step (.root (.leftId (.seq (fork p q) (snd b c)))) ⊙ (.step beta ⊙ correction (a := a) right)))
      (seqLeftTrack (snd b c) (.step (.root (.leftId (fork p q)))) ⊙ (.step beta ⊙ correction (a := a) right)) := by
    four_rewrite_ctx (categorical (CategoryCritical.leftUnitCell (fork p q) (snd b c)))
  have other : Cell (ProductTracks.secondProjection (second (a := a) (b := .pair b c) (left,right)) ⊙
        .step (.root (.betaSnd (reify (unitLayout left)) (reify (unitLayout right)))))
      (seqLeftTrack (snd b c) (.step (.root (.leftId (fork p q)))) ⊙ (.step beta ⊙ correction (a := a) right)) := by
    four_rewrite_ctx (oldLift (ProjectedTrackNaturality.sndBoth (correction (a := a) left) (correction (a := a) right)))
  exact one.trans (two.trans (three.trans (four.trans (five.trans (six.trans other.symm)))))

theorem unitLayout_eq {a b : Shape Atom} (layout : Layout a b) : unitLayout (a := a) (b := b) layout = layout := by
  simp only [unitLayout, substitute, read_universal, map_identity]

def compare {a : Shape Atom} : {b : Shape Atom} → (layout : Layout a b) →
    Cell (first (a := a) (b := b) layout) (second (a := a) (b := b) layout)
  | .atom _, slot => SelectionUnit.compare slot
  | .unit, _ => oldLift (ObservationCoherence.terminalParallel _ _)
  | .pair b c, layout =>
      PresentedObservation.reflect extension (first (a := a) (b := .pair b c) layout) (second (a := a) (b := .pair b c) layout)
        (cancelSuffix (.step (.root (.betaFst (reify (unitLayout layout.1)) (reify (unitLayout layout.2)))))
          (pairFst layout.1 layout.2 (compare layout.1)))
        (cancelSuffix (.step (.root (.betaSnd (reify (unitLayout layout.1)) (reify (unitLayout layout.2)))))
          (pairSnd layout.1 layout.2 (compare layout.2)))

def publicFirst {a b : Shape Atom} (layout : Layout a b) :=
  seqLeftTrack (reify layout) (normalizeCell (Wire.identity a)).toTrack ⊙
    (seqNormal (a := a) (b := a) (universal a) (c := b) layout).toTrack

def publicCompare {a b : Shape Atom} (layout : Layout a b) :
    Cell (publicFirst (a := a) (b := b) layout) (second (a := a) (b := b) layout) := by
  rw [publicFirst, ProjectionCoherence.normalizeIdentity]
  exact compare layout

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.SubstitutionUnit
