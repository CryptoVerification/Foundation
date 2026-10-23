import Foundation.Logic.Polygraph.StructuralCartesianUnitSelectionPasting

/-! The actual identity normalization followed by selectNormal on universal
routing agrees with the selector's left unit, for every typed Slot. Endpoint
adjustments are transported identity paths from read_universal/read_map. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.SelectionUnit
open TypedRouting
open AssociatorPaths
open UnitSelectionPasting
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
local infixr:70 " ⊙ " => Track.comp

def correction {a : Shape Atom} {name : Atom} (slot : Slot a name) :=
  castIdentity (congrArg (reifyRef (a := a) (name := name)) (read_universal slot).symm)

theorem correction_count {a : Shape Atom} {name : Atom} (slot : Slot a name) : stepCount (correction slot) = 0 := by
  unfold correction castIdentity
  rw [LiftSelection.targetCast_count]
  rfl

def first {a : Shape Atom} {name : Atom} (slot : Slot a name) :=
  seqLeftTrack (reifyRef slot) (identityNormal a).toTrack ⊙
    (selectNormal (a := a) (b := a) (universal a) slot).toTrack

def second {a : Shape Atom} {name : Atom} (slot : Slot a name) :=
  Track.step (Step.root (.leftId (reifyRef slot))) ⊙ correction slot

def fstFace (a b : Shape Atom) :
    Cell (seqLeftTrack (fst a b) (identityNormal (.pair a b)).toTrack ⊙
      .step (.root (.betaFst (ProjectionCoherence.leftCanonical a b) (ProjectionCoherence.rightCanonical a b))))
      (.step (.root (.leftId (fst a b))) ⊙ (.inv (.step (.root (.rightId (fst a b)))) ⊙
        (seqRightTrack (fst a b) (identityNormal a).toTrack ⊙ (liftLeft (b := b) (universal a)).toTrack))) :=
  (ProjectionCoherence.identityNormalFst a b).trans (by four_assoc)

def sndFace (a b : Shape Atom) :
    Cell (seqLeftTrack (snd a b) (identityNormal (.pair a b)).toTrack ⊙
      .step (.root (.betaSnd (ProjectionCoherence.leftCanonical a b) (ProjectionCoherence.rightCanonical a b))))
      (.step (.root (.leftId (snd a b))) ⊙ (.inv (.step (.root (.rightId (snd a b)))) ⊙
        (seqRightTrack (snd a b) (identityNormal b).toTrack ⊙ (liftRight (a := a) (universal b)).toTrack))) :=
  (ProjectionCoherence.identityNormalSnd a b).trans (by four_assoc)

def leftCorrections (extra : Shape Atom) {a : Shape Atom} {name : Atom} (slot : Slot a name) :
    Cell (seqRightTrack (fst a extra) (correction slot) ⊙
      LiftSelection.correction .left extra (a := a) (b := a) (universal a) slot)
      (correction (Slot.left (b := extra) slot)) :=
  prefixCastComp (fst a extra)
    (congrArg (reifyRef (a := a) (name := name)) (read_universal slot).symm)
    (LiftSelection.readReify .left extra (a := a) (b := a) (universal a) slot).symm
    (congrArg (reifyRef (a := .pair a extra) (name := name)) (read_universal (Slot.left slot)).symm)

def rightCorrections (extra : Shape Atom) {a : Shape Atom} {name : Atom} (slot : Slot a name) :
    Cell (seqRightTrack (snd extra a) (correction slot) ⊙
      LiftSelection.correction .right extra (a := a) (b := a) (universal a) slot)
      (correction (Slot.right (a := extra) slot)) :=
  prefixCastComp (snd extra a)
    (congrArg (reifyRef (a := a) (name := name)) (read_universal slot).symm)
    (LiftSelection.readReify .right extra (a := a) (b := a) (universal a) slot).symm
    (congrArg (reifyRef (a := .pair extra a) (name := name)) (read_universal (Slot.right slot)).symm)

def compare : {a : Shape Atom} → {name : Atom} → (slot : Slot a name) → Cell (first slot) (second slot)
  | .atom name, _, .here _ => by
      refine Four.trans (q := .step (.root (.rightId (.identity (.atom name))))) (by four_assoc) ?_
      exact (categorical (CategoryCritical.unitCell (.atom name))).symm.trans (by four_assoc)
  | .pair a b, _, .left slot => by
      have face := UnitSelectionPasting.branch (fst a b) (reifyRef slot)
        (identityNormal (.pair a b)).toTrack (identityNormal a).toTrack
        (Step.root (.betaFst (ProjectionCoherence.leftCanonical a b) (ProjectionCoherence.rightCanonical a b)))
        (liftLeft (b := b) (universal a)).toTrack
        (selectNormal (a := a) (b := a) (universal a) slot).toTrack
        (selectNormal (a := .pair a b) (b := a)
          (LiftSelection.mapLayout .left b (a := a) (b := a) (universal a)) slot).toTrack
        (correction slot) (LiftSelection.correction .left b (a := a) (b := a) (universal a) slot)
        (correction (Slot.left (b := b) slot)) (fstFace a b)
        (LiftSelection.compare .left b (a := a) (universal a) slot) (compare slot) (leftCorrections b slot)
      refine Four.trans ?_ (Four.trans face ?_)
      · four_assoc
      · four_assoc
  | .pair a b, _, .right slot => by
      have face := UnitSelectionPasting.branch (snd a b) (reifyRef slot)
        (identityNormal (.pair a b)).toTrack (identityNormal b).toTrack
        (Step.root (.betaSnd (ProjectionCoherence.leftCanonical a b) (ProjectionCoherence.rightCanonical a b)))
        (liftRight (a := a) (universal b)).toTrack
        (selectNormal (a := b) (b := b) (universal b) slot).toTrack
        (selectNormal (a := .pair a b) (b := b)
          (LiftSelection.mapLayout .right a (a := b) (b := b) (universal b)) slot).toTrack
        (correction slot) (LiftSelection.correction .right a (a := b) (b := b) (universal b) slot)
        (correction (Slot.right (a := a) slot)) (sndFace a b)
        (LiftSelection.compare .right a (a := b) (universal b) slot) (compare slot) (rightCorrections a slot)
      refine Four.trans ?_ (Four.trans face ?_)
      · four_assoc
      · four_assoc

def publicFirst {a : Shape Atom} {name : Atom} (slot : Slot a name) :=
  seqLeftTrack (reifyRef slot) (normalizeCell (Wire.identity a)).toTrack ⊙
    (selectNormal (a := a) (b := a) (universal a) slot).toTrack

def publicCompare {a : Shape Atom} {name : Atom} (slot : Slot a name) : Cell (publicFirst slot) (second slot) := by
  rw [publicFirst, ProjectionCoherence.normalizeIdentity]
  exact compare slot

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.SelectionUnit
