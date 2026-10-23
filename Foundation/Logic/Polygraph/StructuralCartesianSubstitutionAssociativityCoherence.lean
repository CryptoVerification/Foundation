import Foundation.Logic.Polygraph.StructuralCartesianSelectionSubstitutionCoherence

/-! Associativity of the actual retained routing substitution calculation.
Both sequential contraction orders use seqNormal, not a replacement normalizer.
The endpoint correction has zero rewrite leaves. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.SubstitutionAssociativity
open TypedRouting AssociatorPaths
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
local infixr:70 " ⊙ " => Track.comp

theorem substitute_assoc {x a b c : Shape Atom} (f : Layout x a) (g : Layout a b) (h : Layout b c) :
    substitute (substitute f g) h = substitute f (substitute g h) := by
  simp only [substitute, map_map, read_map]

def correction {x a b : Shape Atom} (f : Layout x a) (g : Layout a b) :
    {c : Shape Atom} → (h : Layout b c) →
      ProofTrack (reify (substitute (substitute f g) h)) (reify (substitute f (substitute g h)))
  | .atom _, slot => .inv (SelectionSubstitution.correction f g slot)
  | .unit, _ => .refl (Wire.discard x)
  | .pair _ _, h => ProjectedTrackNaturality.forkPaths (correction f g h.1) (correction f g h.2)

theorem correction_count {x a b c : Shape Atom} (f : Layout x a) (g : Layout a b) (h : Layout b c) :
    stepCount (correction f g h) = 0 := by
  induction c with
  | atom => exact SelectionSubstitution.correction_count f g h
  | unit => rfl
  | pair c d ih₁ ih₂ => rw [correction, SubstitutionUnit.fork_count, ih₁ h.1, ih₂ h.2]

def first {x a b c : Shape Atom} (f : Layout x a) (g : Layout a b) (h : Layout b c) :=
  seqRightTrack (reify f) (seqNormal g h).toTrack ⊙ (seqNormal f (substitute g h)).toTrack

def contracted {x a b c : Shape Atom} (f : Layout x a) (g : Layout a b) (h : Layout b c) :=
  seqLeftTrack (reify h) (seqNormal f g).toTrack ⊙
    ((seqNormal (substitute f g) h).toTrack ⊙ correction f g h)

def second {x a b c : Shape Atom} (f : Layout x a) (g : Layout a b) (h : Layout b c) :=
  .inv (alpha (reify f) (reify g) (reify h)) ⊙ contracted f g h

/-- The atomic face is the actual selection/substitution square with its
zero-step endpoint correction cancelled only as a proof path. -/
def atomic {x a b : Shape Atom} (f : Layout x a) (g : Layout a b) {name : Atom} (slot : Slot b name) :
    Cell (first f g (c := .atom name) slot) (second f g (c := .atom name) slot) := by
  let a := alpha (reify f) (reify g) (reifyRef slot)
  let w := seqRightTrack (reify f) (selectNormal g slot).toTrack ⊙ (selectNormal f (read slot g)).toTrack
  let c := SelectionSubstitution.correction f g slot
  have one : Cell (second f g (c := .atom name) slot) (.inv a ⊙ ((a ⊙ (w ⊙ c)) ⊙ .inv c)) := by
    four_rewrite_ctx (SelectionSubstitution.compare f g slot)
  have two : Cell (.inv a ⊙ ((a ⊙ (w ⊙ c)) ⊙ .inv c)) ((w ⊙ c) ⊙ .inv c) := by
    four_rewrite_ctx (FourNaturality.undoInversePrefix (Cells := Generator) a (w ⊙ c))
  have three : Cell ((w ⊙ c) ⊙ .inv c) (first f g (c := .atom name) slot) := by
    exact FourNaturality.undoRight w c
  exact (one.trans (two.trans three)).symm

/-- Every child face is generated recursively. Products may duplicate or
erase arbitrary slots; terminal outputs use retained terminal coherence. -/
def compare {x a b : Shape Atom} (f : Layout x a) (g : Layout a b) :
    {c : Shape Atom} → (h : Layout b c) → Cell (first f g h) (second f g h)
  | .atom _, slot => atomic f g slot
  | .unit, _ => oldLift (ObservationCoherence.terminalParallel _ _)
  | .pair c d, h => by
      let l := (seqNormal g h.1).toTrack
      let r := (seqNormal g h.2).toTrack
      let nl := (seqNormal f (substitute g h.1)).toTrack
      let nr := (seqNormal f (substitute g h.2)).toTrack
      let tl := (seqNormal (substitute f g) h.1).toTrack
      let tr := (seqNormal (substitute f g) h.2).toTrack
      let cl := correction f g h.1
      let cr := correction f g h.2
      have square := DistributionSubstitutionPasting.pair (reify f) (reify g) (reify h.1) (reify h.2)
        (seqNormal f g).toTrack l r nl nr (tl ⊙ cl) (tr ⊙ cr) (compare f g h.1) (compare f g h.2)
      refine Four.trans ?_ (Four.trans square ?_)
      · four_assoc_ctx
      · four_rewrite_ctx (LoopCoherence.forkComp tl cl tr cr)

def associated {x a b c : Shape Atom} (f : Layout x a) (g : Layout a b) (h : Layout b c) :=
  alpha (reify f) (reify g) (reify h) ⊙ first f g h

/-- Forward associativity square: first contract the first two layouts, or
associate then contract the last two. Both end at the same substituted route. -/
def forwardCompare {x a b c : Shape Atom} (f : Layout x a) (g : Layout a b) (h : Layout b c) :
    Cell (contracted f g h) (associated f g h) :=
  ((Four.comp (.refl (alpha (reify f) (reify g) (reify h))) (compare f g h)).trans
    (FourNaturality.undoLeft _ _)).symm

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.SubstitutionAssociativity
