import Foundation.Logic.Polygraph.StructuralCartesianRightUnitPasting

/-! Right unit of the retained routing-substitution calculation. This follows
the actual identityNormal path in the second operand, then the actual
seqNormal path. Recursive endpoint corrections have zero rewrite leaves. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.SubstitutionRightUnit
open TypedRouting AssociatorPaths
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
local infixr:70 " ⊙ " => Track.comp

def unitLayout {a b : Shape Atom} (layout : Layout a b) : Layout a b :=
  substitute (a := a) (b := b) (c := b) layout (universal b)

theorem unitLayout_eq {a b : Shape Atom} (layout : Layout a b) : unitLayout (a := a) (b := b) layout = layout :=
  map_universal b layout

def correction {a : Shape Atom} : {b : Shape Atom} → (layout : Layout a b) →
    ProofTrack (reify layout) (reify (unitLayout layout))
  | .atom _, slot => .refl (reifyRef slot)
  | .unit, _ => .refl (Wire.discard a)
  | .pair b c, layout => ProjectedTrackNaturality.forkPaths
      (correction layout.1 ⊙ ProjectedSubstitution.correction .left layout.1 layout.2 (universal b))
      (correction layout.2 ⊙ ProjectedSubstitution.correction .right layout.2 layout.1 (universal c))

theorem correction_count {a b : Shape Atom} (layout : Layout a b) :
    stepCount (correction (a := a) (b := b) layout) = 0 := by
  induction b with
  | atom => rfl
  | unit => rfl
  | pair b c ih₁ ih₂ =>
      simp only [correction, SubstitutionUnit.fork_count, stepCount, ih₁ layout.1, ih₂ layout.2,
        ProjectedSubstitution.correction_count, Nat.zero_add]

def first {a b : Shape Atom} (layout : Layout a b) :=
  seqRightTrack (reify layout) (identityNormal b).toTrack ⊙
    (seqNormal (a := a) (b := b) layout (c := b) (universal b)).toTrack

def second {a b : Shape Atom} (layout : Layout a b) :=
  Track.step (Step.root (.rightId (reify layout))) ⊙ correction (a := a) (b := b) layout

def pairFst {a b c : Shape Atom} (left : Layout a b) (right : Layout a c)
    (child : Cell (first (a := a) (b := b) left) (second (a := a) (b := b) left)) :
    Cell (seqLeftTrack (fst b c) (first (a := a) (b := .pair b c) (left,right)) ⊙
      .step (.root (.betaFst
        (reify (ProjectedSubstitution.result .left left right (universal b)))
        (reify (ProjectedSubstitution.result .right right left (universal c))))))
      (seqLeftTrack (fst b c) (second (a := a) (b := .pair b c) (left,right)) ⊙
        .step (.root (.betaFst
          (reify (ProjectedSubstitution.result .left left right (universal b)))
          (reify (ProjectedSubstitution.result .right right left (universal c)))))) := by
  let p := fork (reify left) (reify right)
  let h := fst b c
  let v := reify (universal (.pair b c))
  let nl := (seqNormal (a := a) (b := .pair b c) (left,right)
    (c := b) (LiftSelection.mapLayout .left c (a := b) (universal b))).toTrack
  let nr := (seqNormal (a := a) (b := .pair b c) (left,right)
    (c := c) (LiftSelection.mapLayout .right b (a := c) (universal c))).toTrack
  let lc := correction (a := a) (b := b) left ⊙ ProjectedSubstitution.correction .left left right (universal b)
  let rc := correction (a := a) (b := c) right ⊙ ProjectedSubstitution.correction .right right left (universal c)
  let betaCanonical := Step.root (Root.betaFst (ProjectionCoherence.leftCanonical b c) (ProjectionCoherence.rightCanonical b c))
  let betaParent := Step.root (Root.betaFst (reify left) (reify right))
  have projected : Cell (seqLeftTrack h (identityNormal (.pair b c)).toTrack ⊙ .step betaCanonical)
      (.step (.root (.leftId h)) ⊙ (.inv (.step (.root (.rightId h))) ⊙
        (seqRightTrack h (identityNormal b).toTrack ⊙
          (LiftSelection.lift .left c (a := b) (universal b)).toTrack))) := by
    refine Four.trans (ProjectionCoherence.identityNormalFst b c) ?_
    four_assoc_ctx
  have one : Cell (seqLeftTrack h (first (a := a) (b := .pair b c) (left,right)) ⊙
      .step (.root (.betaFst
        (reify (ProjectedSubstitution.result .left left right (universal b)))
        (reify (ProjectedSubstitution.result .right right left (universal c))))))
      (seqLeftTrack h (seqRightTrack p (identityNormal (.pair b c)).toTrack) ⊙
        (alpha p v h ⊙ (seqRightTrack p (.step betaCanonical) ⊙ nl))) := by
    four_rewrite_ctx (SelectionPasting.fstSquare p (ProjectionCoherence.leftCanonical b c)
      (ProjectionCoherence.rightCanonical b c) nl nr)
  have two := RightUnitPasting.branch p h (identityNormal (.pair b c)).toTrack (identityNormal b).toTrack
    betaCanonical betaParent (LiftSelection.lift .left c (a := b) (universal b)).toTrack nl
    (seqNormal (a := a) (b := b) left (c := b) (universal b)).toTrack
    (correction (a := a) (b := b) left) (ProjectedSubstitution.correction .left left right (universal b))
    projected (ProjectedSubstitution.compare .left left right (universal b)) child
  have other : Cell (seqLeftTrack h (second (a := a) (b := .pair b c) (left,right)) ⊙
      .step (.root (.betaFst
        (reify (ProjectedSubstitution.result .left left right (universal b)))
        (reify (ProjectedSubstitution.result .right right left (universal c))))))
      (seqLeftTrack h (.step (.root (.rightId p))) ⊙ (.step betaParent ⊙ lc)) := by
    four_rewrite_ctx (oldLift (ProjectedTrackNaturality.fstBoth lc rc))
  exact one.trans (two.trans other.symm)

def pairSnd {a b c : Shape Atom} (left : Layout a b) (right : Layout a c)
    (child : Cell (first (a := a) (b := c) right) (second (a := a) (b := c) right)) :
    Cell (seqLeftTrack (snd b c) (first (a := a) (b := .pair b c) (left,right)) ⊙
      .step (.root (.betaSnd
        (reify (ProjectedSubstitution.result .left left right (universal b)))
        (reify (ProjectedSubstitution.result .right right left (universal c))))))
      (seqLeftTrack (snd b c) (second (a := a) (b := .pair b c) (left,right)) ⊙
        .step (.root (.betaSnd
          (reify (ProjectedSubstitution.result .left left right (universal b)))
          (reify (ProjectedSubstitution.result .right right left (universal c)))))) := by
  let p := fork (reify left) (reify right)
  let h := snd b c
  let v := reify (universal (.pair b c))
  let nl := (seqNormal (a := a) (b := .pair b c) (left,right)
    (c := b) (LiftSelection.mapLayout .left c (a := b) (universal b))).toTrack
  let nr := (seqNormal (a := a) (b := .pair b c) (left,right)
    (c := c) (LiftSelection.mapLayout .right b (a := c) (universal c))).toTrack
  let lc := correction (a := a) (b := b) left ⊙ ProjectedSubstitution.correction .left left right (universal b)
  let rc := correction (a := a) (b := c) right ⊙ ProjectedSubstitution.correction .right right left (universal c)
  let betaCanonical := Step.root (Root.betaSnd (ProjectionCoherence.leftCanonical b c) (ProjectionCoherence.rightCanonical b c))
  let betaParent := Step.root (Root.betaSnd (reify left) (reify right))
  have projected : Cell (seqLeftTrack h (identityNormal (.pair b c)).toTrack ⊙ .step betaCanonical)
      (.step (.root (.leftId h)) ⊙ (.inv (.step (.root (.rightId h))) ⊙
        (seqRightTrack h (identityNormal c).toTrack ⊙
          (LiftSelection.lift .right b (a := c) (universal c)).toTrack))) := by
    refine Four.trans (ProjectionCoherence.identityNormalSnd b c) ?_
    four_assoc_ctx
  have one : Cell (seqLeftTrack h (first (a := a) (b := .pair b c) (left,right)) ⊙
      .step (.root (.betaSnd
        (reify (ProjectedSubstitution.result .left left right (universal b)))
        (reify (ProjectedSubstitution.result .right right left (universal c))))))
      (seqLeftTrack h (seqRightTrack p (identityNormal (.pair b c)).toTrack) ⊙
        (alpha p v h ⊙ (seqRightTrack p (.step betaCanonical) ⊙ nr))) := by
    four_rewrite_ctx (SelectionPasting.sndSquare p (ProjectionCoherence.leftCanonical b c)
      (ProjectionCoherence.rightCanonical b c) nl nr)
  have two := RightUnitPasting.branch p h (identityNormal (.pair b c)).toTrack (identityNormal c).toTrack
    betaCanonical betaParent (LiftSelection.lift .right b (a := c) (universal c)).toTrack nr
    (seqNormal (a := a) (b := c) right (c := c) (universal c)).toTrack
    (correction (a := a) (b := c) right) (ProjectedSubstitution.correction .right right left (universal c))
    projected (ProjectedSubstitution.compare .right right left (universal c)) child
  have other : Cell (seqLeftTrack h (second (a := a) (b := .pair b c) (left,right)) ⊙
      .step (.root (.betaSnd
        (reify (ProjectedSubstitution.result .left left right (universal b)))
        (reify (ProjectedSubstitution.result .right right left (universal c))))))
      (seqLeftTrack h (.step (.root (.rightId p))) ⊙ (.step betaParent ⊙ rc)) := by
    four_rewrite_ctx (oldLift (ProjectedTrackNaturality.sndBoth lc rc))
  exact one.trans (two.trans other.symm)

/-- The two projection faces are discharged recursively; no atomic witness
or whole-path generator is required from the caller. -/
def compare {a : Shape Atom} : {b : Shape Atom} → (layout : Layout a b) →
    Cell (first (a := a) (b := b) layout) (second (a := a) (b := b) layout)
  | .atom _, slot => by four_assoc_ctx
  | .unit, _ => oldLift (ObservationCoherence.terminalParallel _ _)
  | .pair _ _, layout => PresentedObservation.reflect extension _ _
      (SubstitutionUnit.cancelSuffix _ (pairFst layout.1 layout.2 (compare layout.1)))
      (SubstitutionUnit.cancelSuffix _ (pairSnd layout.1 layout.2 (compare layout.2)))

def publicFirst {a b : Shape Atom} (layout : Layout a b) :=
  seqRightTrack (reify layout) (normalizeCell (Wire.identity b)).toTrack ⊙
    (seqNormal (a := a) (b := b) layout (c := b) (universal b)).toTrack

def publicCompare {a b : Shape Atom} (layout : Layout a b) :
    Cell (publicFirst (a := a) (b := b) layout) (second (a := a) (b := b) layout) := by
  rw [publicFirst, ProjectionCoherence.normalizeIdentity]
  exact compare layout

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.SubstitutionRightUnit
