import Foundation.Logic.Polygraph.StructuralCartesianSelectionPasting

/-! Actual liftLeft/liftRight and selectNormal commute for every typed slot.
Endpoint correction is a transported identity track from read_map, not an
extra rewrite. All comparison faces are derived in the retained basis. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.LiftSelection
open TypedRouting
open AssociatorPaths
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
local infixr:70 " ⊙ " => Track.comp

inductive Side where
  | left
  | right

def domain (side : Side) (a extra : Shape Atom) : Shape Atom :=
  match side with | .left => .pair a extra | .right => .pair extra a

def projection (side : Side) (a extra : Shape Atom) : Wire (domain side a extra) a :=
  match side with | .left => fst a extra | .right => snd extra a

def embedSlot (side : Side) (extra : Shape Atom) {a : Shape Atom} {name : Atom} (slot : Slot a name) :
    Slot (domain side a extra) name :=
  match side with | .left => .left slot | .right => .right slot

def mapLayout (side : Side) (extra : Shape Atom) {a b : Shape Atom} (layout : Layout a b) :
    Layout (domain side a extra) b := b.map (fun _ => embedSlot side extra) layout

def lift (side : Side) (extra : Shape Atom) {a b : Shape Atom} (layout : Layout a b) :
    Cartesian.Cell (.seq (projection side a extra) (reify layout)) (reify (mapLayout side extra (a := a) layout)) :=
  match side with | .left => liftLeft layout | .right => liftRight layout

theorem liftPair (side : Side) (extra : Shape Atom) {a b c : Shape Atom}
    (first : Layout a b) (second : Layout a c) :
    lift side extra (a := a) (b := .pair b c) (first,second) = (Cartesian.Cell.root (.forkAfter (projection side a extra) (reify first) (reify second))).trans
      (Cartesian.Cell.fork (lift side extra (a := a) first) (lift side extra (a := a) second)) := by
  cases side <;> rfl

theorem reifyEmbeddedRef (side : Side) (extra : Shape Atom) {a : Shape Atom} {name : Atom} (slot : Slot a name) :
    reifyRef (embedSlot side extra slot) = Wire.seq (projection side a extra) (reifyRef slot) := by
  cases side <;> rfl

theorem readReify (side : Side) (extra : Shape Atom) {a b : Shape Atom} (layout : Layout a b)
    {name : Atom} (slot : Slot b name) :
    reifyRef (read slot (mapLayout side extra (a := a) layout)) =
      Wire.seq (projection side a extra) (reifyRef (read slot layout)) := by
  rw [mapLayout, read_map]
  exact reifyEmbeddedRef side extra (read slot layout)

def targetCast {a b : Shape Atom} {p q r : Wire a b} (same : q = r) (path : ProofTrack p q) : ProofTrack p r :=
  same ▸ path

def correction (side : Side) (extra : Shape Atom) {a b : Shape Atom} (layout : Layout a b)
    {name : Atom} (slot : Slot b name) :=
  targetCast (readReify side extra layout slot).symm
    (Track.refl (Wire.seq (projection side a extra) (reifyRef (read slot layout))))

theorem targetCast_count {a b : Shape Atom} {p q r : Wire a b} (same : q = r) (path : ProofTrack p q) :
    stepCount (targetCast same path) = stepCount path := by
  cases same
  rfl

theorem correction_count (side : Side) (extra : Shape Atom) {a b : Shape Atom} (layout : Layout a b)
    {name : Atom} (slot : Slot b name) : stepCount (correction side extra (a := a) layout slot) = 0 := by
  unfold correction
  rw [targetCast_count]
  rfl

def first (side : Side) (extra : Shape Atom) {a b : Shape Atom} (layout : Layout a b)
    {name : Atom} (slot : Slot b name) :=
  seqLeftTrack (reifyRef slot) (lift side extra (a := a) layout).toTrack ⊙
    (selectNormal (mapLayout side extra (a := a) layout) slot).toTrack

def second (side : Side) (extra : Shape Atom) {a b : Shape Atom} (layout : Layout a b)
    {name : Atom} (slot : Slot b name) :=
  alpha (projection side a extra) (reify layout) (reifyRef slot) ⊙
    (seqRightTrack (projection side a extra) (selectNormal layout slot).toTrack ⊙ correction side extra (a := a) layout slot)

def liftPairCell (side : Side) (extra : Shape Atom) {a b c : Shape Atom}
    (left : Layout a b) (right : Layout a c) :
    Cell (lift side extra (a := a) (b := .pair b c) (left,right)).toTrack
      (SelectionPasting.distributedLift (projection side a extra) (reify left) (reify right)
        (lift side extra (a := a) left).toTrack (lift side extra (a := a) right).toTrack) := by
  rw [liftPair]
  four_assoc

def liftFstSquare (side : Side) (extra : Shape Atom) {a b c : Shape Atom}
    (left : Layout a b) (right : Layout a c) :
    Cell (seqLeftTrack (fst b c) (lift side extra (a := a) (b := .pair b c) (left,right)).toTrack ⊙
        .step (.root (.betaFst (reify (mapLayout side extra (a := a) left)) (reify (mapLayout side extra (a := a) right)))))
      (alpha (projection side a extra) (fork (reify left) (reify right)) (fst b c) ⊙
        (seqRightTrack (projection side a extra) (.step (.root (.betaFst (reify left) (reify right)))) ⊙
          (lift side extra (a := a) left).toTrack)) :=
  (Four.comp (whisker (.seqLeft (fst b c)) (liftPairCell side extra left right)) (.refl _)).trans
    (SelectionPasting.fstSquare (projection side a extra) (reify left) (reify right)
      (lift side extra (a := a) left).toTrack (lift side extra (a := a) right).toTrack)

def liftSndSquare (side : Side) (extra : Shape Atom) {a b c : Shape Atom}
    (left : Layout a b) (right : Layout a c) :
    Cell (seqLeftTrack (snd b c) (lift side extra (a := a) (b := .pair b c) (left,right)).toTrack ⊙
        .step (.root (.betaSnd (reify (mapLayout side extra (a := a) left)) (reify (mapLayout side extra (a := a) right)))))
      (alpha (projection side a extra) (fork (reify left) (reify right)) (snd b c) ⊙
        (seqRightTrack (projection side a extra) (.step (.root (.betaSnd (reify left) (reify right)))) ⊙
          (lift side extra (a := a) right).toTrack)) :=
  (Four.comp (whisker (.seqLeft (snd b c)) (liftPairCell side extra left right)) (.refl _)).trans
    (SelectionPasting.sndSquare (projection side a extra) (reify left) (reify right)
      (lift side extra (a := a) left).toTrack (lift side extra (a := a) right).toTrack)

def compare (side : Side) (extra : Shape Atom) {a : Shape Atom} : {b : Shape Atom} → (layout : Layout a b) →
    {name : Atom} → (slot : Slot b name) → Cell (first side extra (a := a) layout slot) (second side extra (a := a) layout slot)
  | .atom name, layout, _, .here _ => by
      cases side
      all_goals
        refine Four.trans (q := .step (.root (.rightId _))) (by four_assoc) ?_
        exact (categorical (CategoryCritical.rightUnitCell _ _)).symm.trans (by four_assoc)
  | .pair b c, layout, _, .left slot => by
      have square := SelectionPasting.suffix (projection side a extra) (reify layout)
        (fst _ _) (reifyRef slot)
        (Step.root (.betaFst (reify layout.1) (reify layout.2)))
        (Step.root (.betaFst (reify (mapLayout side extra (a := a) layout.1)) (reify (mapLayout side extra (a := a) layout.2))))
        (lift side extra (a := a) layout).toTrack (lift side extra (a := a) layout.1).toTrack
        (selectNormal layout.1 slot).toTrack (selectNormal (mapLayout side extra (a := a) layout.1) slot).toTrack
        (correction side extra (a := a) layout.1 slot)
        (liftFstSquare side extra layout.1 layout.2) (compare side extra layout.1 slot)
      refine Four.trans ?_ (Four.trans square ?_)
      · four_assoc
      · four_assoc
  | .pair b c, layout, _, .right slot => by
      have square := SelectionPasting.suffix (projection side a extra) (reify layout)
        (snd _ _) (reifyRef slot)
        (Step.root (.betaSnd (reify layout.1) (reify layout.2)))
        (Step.root (.betaSnd (reify (mapLayout side extra (a := a) layout.1)) (reify (mapLayout side extra (a := a) layout.2))))
        (lift side extra (a := a) layout).toTrack (lift side extra (a := a) layout.2).toTrack
        (selectNormal layout.2 slot).toTrack (selectNormal (mapLayout side extra (a := a) layout.2) slot).toTrack
        (correction side extra (a := a) layout.2 slot)
        (liftSndSquare side extra layout.1 layout.2) (compare side extra layout.2 slot)
      refine Four.trans ?_ (Four.trans square ?_)
      · four_assoc
      · four_assoc

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.LiftSelection
