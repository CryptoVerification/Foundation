import Foundation.Logic.Polygraph.StructuralCartesianDistributionSubstitutionPasting

/-! Composition with an embedded child layout, using the actual retained
lift and seqNormal paths. The source parent may copy or discard arbitrary
inputs. Endpoint transport contributes zero rewrite leaves. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.ProjectedSubstitution
open TypedRouting AssociatorPaths LiftSelection
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
local infixr:70 " ⊙ " => Track.comp

def parent (side : Side) {x a extra : Shape Atom} (chosen : Layout x a) (other : Layout x extra) :
    Layout x (domain side a extra) :=
  match side with | .left => (chosen,other) | .right => (other,chosen)

def beta (side : Side) {x a extra : Shape Atom} (chosen : Layout x a) (other : Layout x extra) :
    ProofTrack (.seq (reify (parent side chosen other)) (projection side a extra)) (reify chosen) :=
  match side with
  | .left => .step (.root (.betaFst (reify chosen) (reify other)))
  | .right => .step (.root (.betaSnd (reify other) (reify chosen)))

theorem readEmbedded (side : Side) {x a extra : Shape Atom} (chosen : Layout x a) (other : Layout x extra)
    {name : Atom} (slot : Slot a name) :
    read (embedSlot side extra slot) (parent side chosen other) = read slot chosen := by
  cases side <;> rfl

def result (side : Side) {x a extra b : Shape Atom} (chosen : Layout x a) (other : Layout x extra) (layout : Layout a b) :
    Layout x b := substitute (a := x) (b := domain side a extra) (c := b)
      (parent side chosen other) (mapLayout side extra (a := a) layout)

theorem result_eq (side : Side) {x a extra b : Shape Atom} (chosen : Layout x a) (other : Layout x extra) (layout : Layout a b) :
    result side chosen other layout = substitute chosen layout := by
  simp only [result, substitute, mapLayout, TypedRouting.map_map, readEmbedded]

def correction (side : Side) {x a extra : Shape Atom} (chosen : Layout x a) (other : Layout x extra) :
    {b : Shape Atom} → (layout : Layout a b) →
      ProofTrack (reify (substitute chosen layout)) (reify (result side chosen other layout))
  | .atom _, slot => UnitSelectionPasting.castIdentity
      (congrArg reifyRef (readEmbedded side chosen other slot).symm)
  | .unit, _ => .refl (Wire.discard x)
  | .pair _ _, layout => ProjectedTrackNaturality.forkPaths
      (correction side chosen other layout.1) (correction side chosen other layout.2)

theorem correction_count (side : Side) {x a extra b : Shape Atom}
    (chosen : Layout x a) (other : Layout x extra) (layout : Layout a b) :
    stepCount (correction side chosen other layout) = 0 := by
  induction b with
  | atom => cases side <;> rfl
  | unit => rfl
  | pair b c ih₁ ih₂ =>
      rw [correction, SubstitutionUnit.fork_count, ih₁ layout.1, ih₂ layout.2]

def first (side : Side) {x a extra b : Shape Atom} (chosen : Layout x a) (other : Layout x extra) (layout : Layout a b) :=
  seqRightTrack (reify (parent side chosen other)) (lift side extra (a := a) layout).toTrack ⊙
    (seqNormal (a := x) (b := domain side a extra) (parent side chosen other)
      (c := b) (mapLayout side extra (a := a) layout)).toTrack

def second (side : Side) {x a extra b : Shape Atom} (chosen : Layout x a) (other : Layout x extra) (layout : Layout a b) :=
  .inv (alpha (reify (parent side chosen other)) (projection side a extra) (reify layout)) ⊙
    (seqLeftTrack (reify layout) (beta side chosen other) ⊙
      ((seqNormal (a := x) (b := a) chosen (c := b) layout).toTrack ⊙ correction side chosen other layout))

/-- Both sides of a product are treated, including repeated and unused slots
and terminal outputs. The child faces are constructed recursively here. -/
def compare (side : Side) {x a extra : Shape Atom} (chosen : Layout x a) (other : Layout x extra) :
    {b : Shape Atom} → (layout : Layout a b) →
      Cell (first side chosen other layout) (second side chosen other layout)
  | .atom _, slot => by
      cases side <;> four_assoc_ctx
  | .unit, _ => oldLift (ObservationCoherence.terminalParallel _ _)
  | .pair b c, layout => by
      let p := reify (parent side chosen other)
      let g := projection side a extra
      let l := (lift side extra (a := a) layout.1).toTrack
      let r := (lift side extra (a := a) layout.2).toTrack
      let nl := (seqNormal (a := x) (b := domain side a extra) (parent side chosen other)
        (c := b) (mapLayout side extra (a := a) layout.1)).toTrack
      let nr := (seqNormal (a := x) (b := domain side a extra) (parent side chosen other)
        (c := c) (mapLayout side extra (a := a) layout.2)).toTrack
      let tl := (seqNormal (a := x) (b := a) chosen (c := b) layout.1).toTrack
      let tr := (seqNormal (a := x) (b := a) chosen (c := c) layout.2).toTrack
      let cl := correction side chosen other layout.1
      let cr := correction side chosen other layout.2
      have square := DistributionSubstitutionPasting.pair p g (reify layout.1) (reify layout.2)
        (beta side chosen other) l r nl nr (tl ⊙ cl) (tr ⊙ cr)
        (compare side chosen other layout.1) (compare side chosen other layout.2)
      refine Four.trans ?_ (Four.trans square ?_)
      · four_rewrite_ctx (whisker (.seqRight p) (liftPairCell side extra layout.1 layout.2))
      · four_rewrite_ctx (LoopCoherence.forkComp tl cl tr cr)

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.ProjectedSubstitution
