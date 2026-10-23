import Foundation.Logic.Polygraph.StructuralCartesianSubstitutionRightUnitCoherence

/-! Selecting after actual routing substitution agrees with selecting first
and then substituting. The endpoint adjustment is a transported identity;
no new higher generator or arbitrary normalization comparison is introduced. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.SelectionSubstitution
open TypedRouting AssociatorPaths
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
local infixr:70 " ⊙ " => Track.comp

theorem readSubstitute {x a b : Shape Atom} (first : Layout x a) (second : Layout a b)
    {name : Atom} (slot : Slot b name) :
    read slot (substitute first second) = read (read slot second) first :=
  read_map (fun _ slot => read slot first) slot second

def correction {x a b : Shape Atom} (first : Layout x a) (second : Layout a b)
    {name : Atom} (slot : Slot b name) :=
  UnitSelectionPasting.castIdentity (congrArg reifyRef (readSubstitute first second slot).symm)

theorem correction_count {x a b : Shape Atom} (first : Layout x a) (second : Layout a b)
    {name : Atom} (slot : Slot b name) : stepCount (correction first second slot) = 0 := by
  unfold correction UnitSelectionPasting.castIdentity
  rw [LiftSelection.targetCast_count]
  rfl

def first {x a b : Shape Atom} (f : Layout x a) (g : Layout a b) {name : Atom} (slot : Slot b name) :=
  seqLeftTrack (reifyRef slot) (seqNormal f g).toTrack ⊙ (selectNormal (substitute f g) slot).toTrack

def second {x a b : Shape Atom} (f : Layout x a) (g : Layout a b) {name : Atom} (slot : Slot b name) :=
  alpha (reify f) (reify g) (reifyRef slot) ⊙
    (seqRightTrack (reify f) (selectNormal g slot).toTrack ⊙
      ((selectNormal f (read slot g)).toTrack ⊙ correction f g slot))

def rightNatural {a b : Shape Atom} {p q : Wire a b} (path : ProofTrack p q) :
    Cell (.step (.root (.rightId p)) ⊙ path)
      (seqLeftTrack (.identity b) path ⊙ .step (.root (.rightId q))) := by
  have face := FourNaturality.natural (Cells := Generator)
    (fun w : Wire a b => Wire.seq w (.identity b)) (fun w => w)
    (fun change => Step.seqLeft change (.identity b)) (fun change => change)
    (fun w => Track.step (Step.root (Root.rightId w)))
    (fun change => (categorical (CategoryCritical.rightNatural change)).symm) path
  have same : path.map (fun w => w) (fun change => change) = path := by
    clear face
    induction path <;> simp_all only [Track.map]
  simpa only [seqLeftTrack, same] using face.symm

/-- Projection faces for the actual seqNormal pair definition, including its
zero-step bookkeeping paths. -/
def fstSquare {x a b c : Shape Atom} (f : Layout x a) (left : Layout a b) (right : Layout a c) :
    Cell (seqLeftTrack (fst b c) (seqNormal (a := x) (b := a) f (c := .pair b c) (left,right)).toTrack ⊙
      .step (.root (.betaFst (reify (substitute f left)) (reify (substitute f right)))))
      (alpha (reify f) (fork (reify left) (reify right)) (fst b c) ⊙
        (seqRightTrack (reify f) (.step (.root (.betaFst (reify left) (reify right)))) ⊙ (seqNormal f left).toTrack)) := by
  refine Four.trans ?_ (SelectionPasting.fstSquare (reify f) (reify left) (reify right)
    (seqNormal f left).toTrack (seqNormal f right).toTrack)
  four_assoc_ctx

def sndSquare {x a b c : Shape Atom} (f : Layout x a) (left : Layout a b) (right : Layout a c) :
    Cell (seqLeftTrack (snd b c) (seqNormal (a := x) (b := a) f (c := .pair b c) (left,right)).toTrack ⊙
      .step (.root (.betaSnd (reify (substitute f left)) (reify (substitute f right)))))
      (alpha (reify f) (fork (reify left) (reify right)) (snd b c) ⊙
        (seqRightTrack (reify f) (.step (.root (.betaSnd (reify left) (reify right)))) ⊙ (seqNormal f right).toTrack)) := by
  refine Four.trans ?_ (SelectionPasting.sndSquare (reify f) (reify left) (reify right)
    (seqNormal f left).toTrack (seqNormal f right).toTrack)
  four_assoc_ctx

def compare {x a : Shape Atom} (f : Layout x a) : {b : Shape Atom} → (g : Layout a b) →
    {name : Atom} → (slot : Slot b name) → Cell (first f g slot) (second f g slot)
  | .atom _, g, _, .here _ => by
      have face := (rightNatural (seqNormal f g).toTrack).symm
      refine Four.trans ?_ (Four.trans face ?_)
      · four_assoc_ctx
      · four_rewrite_ctx (categorical (CategoryCritical.rightUnitCell (reify f) (reify g))).symm
  | .pair b c, g, _, .left slot => by
      have square := SelectionPasting.suffix (reify f) (reify g) (fst b c) (reifyRef slot)
        (Step.root (.betaFst (reify g.1) (reify g.2)))
        (Step.root (.betaFst (reify (substitute f g.1)) (reify (substitute f g.2))))
        (seqNormal f g).toTrack (seqNormal f g.1).toTrack
        (selectNormal g.1 slot).toTrack (selectNormal (substitute f g.1) slot).toTrack
        ((selectNormal f (read slot g.1)).toTrack ⊙ correction f g.1 slot)
        (fstSquare f g.1 g.2) (compare f g.1 slot)
      refine Four.trans ?_ (Four.trans square ?_)
      · four_assoc_ctx
      · four_assoc_ctx
  | .pair b c, g, _, .right slot => by
      have square := SelectionPasting.suffix (reify f) (reify g) (snd b c) (reifyRef slot)
        (Step.root (.betaSnd (reify g.1) (reify g.2)))
        (Step.root (.betaSnd (reify (substitute f g.1)) (reify (substitute f g.2))))
        (seqNormal f g).toTrack (seqNormal f g.2).toTrack
        (selectNormal g.2 slot).toTrack (selectNormal (substitute f g.2) slot).toTrack
        ((selectNormal f (read slot g.2)).toTrack ⊙ correction f g.2 slot)
        (sndSquare f g.1 g.2) (compare f g.2 slot)
      refine Four.trans ?_ (Four.trans square ?_)
      · four_assoc_ctx
      · four_assoc_ctx

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.SelectionSubstitution
