import Foundation.Logic.Polygraph.StructuralCartesianProjectedSubstitutionCoherence

/-! Derived categorical pasting used by the actual right substitution unit.
All projection and child faces are supplied as checked higher cells. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.RightUnitPasting
open AssociatorPaths
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
local infixr:70 " ⊙ " => Track.comp

def lastPath {x a b c : Shape Atom} (f : Wire x a) (g : Wire a b) {p q : Wire b c} (path : ProofTrack p q) :
    Cell (alpha f g p ⊙ seqRightTrack f (seqRightTrack g path))
      (seqRightTrack (.seq f g) path ⊙ alpha f g q) := by
  have face := FourNaturality.natural (Cells := Generator)
    (fun w : Wire b c => Wire.seq (Wire.seq f g) w) (fun w => Wire.seq f (Wire.seq g w))
    (fun change => Step.seqRight (.seq f g) change) (fun change => Step.seqRight f (.seqRight g change))
    (fun w => alpha f g w) (fun change => (categorical (CategoryCritical.assocLastNatural f g change)).symm) path
  simpa only [seqRightTrack, FourNaturality.map_map] using face.symm

def lastPostfixInverse {x a b c : Shape Atom} (f : Wire x a) (g : Wire a b) {p q : Wire b c} (path : ProofTrack p q) :
    Cell (seqRightTrack f (seqRightTrack g path) ⊙ .inv (alpha f g q))
      (.inv (alpha f g p) ⊙ seqRightTrack (.seq f g) path) :=
  (FourNaturality.invertSquare (alpha f g p) (seqRightTrack f (seqRightTrack g path))
    (seqRightTrack (.seq f g) path) (alpha f g q) (lastPath f g path)).symm

def exchange {x a b : Shape Atom} {f f' : Wire x a} (change : Step f f') {p q : Wire a b} (path : ProofTrack p q) :
    Cell (seqLeftTrack p (.step change) ⊙ seqRightTrack f' path)
      (seqRightTrack f path ⊙ seqLeftTrack q (.step change)) := by
  have face := FourNaturality.natural (Cells := Generator)
    (fun w : Wire a b => Wire.seq f w) (fun w => Wire.seq f' w)
    (fun edge => Step.seqRight f edge) (fun edge => Step.seqRight f' edge)
    (fun w => Track.step (Step.seqLeft change w))
    (fun edge => (oldLift (.generator (.seqExchange change edge))).symm) path
  simpa only [seqLeftTrack, seqRightTrack, Track.map] using face.symm

def corner {x a b : Shape Atom} (f : Wire x a) (s : Wire a b) :
    Cell (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
      (.inv (alpha f s (.identity b)) ⊙ .step (.root (.rightId (.seq f s))))) (.refl _) := by
  let unit := seqRightTrack f (Track.step (Step.root (Root.rightId s)))
  have face : Cell (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
      (.inv (alpha f s (.identity b)) ⊙ .step (.root (.rightId (.seq f s)))))
      (.inv unit ⊙ unit) := by
    refine Four.trans ?_ (Four.comp (.refl (.inv unit))
      (FourNaturality.undoInversePrefix (alpha f s (.identity b)) unit))
    four_rewrite_ctx (categorical (CategoryCritical.rightUnitCell f s)).symm
  exact face.trans (Four.leftInv unit)

def branch {x a b : Shape Atom} (f : Wire x a) (s : Wire a b)
    {v : Wire a a} {c : Wire b b} {mapped : Wire a b} {h : Wire x b} {t r : Wire x b}
    (normal : ProofTrack (.identity a) v) (childNormal : ProofTrack (.identity b) c)
    (betaCanonical : Step (.seq v s) mapped) (betaParent : Step (.seq f s) h)
    (lift : ProofTrack (.seq s c) mapped) (select' : ProofTrack (.seq f mapped) r)
    (select : ProofTrack (.seq h c) t) (childCorrection : ProofTrack h t) (mapCorrection : ProofTrack t r)
    (projected : Cell (seqLeftTrack s normal ⊙ .step betaCanonical)
      (.step (.root (.leftId s)) ⊙ (.inv (.step (.root (.rightId s))) ⊙ (seqRightTrack s childNormal ⊙ lift))))
    (substitution : Cell (seqRightTrack f lift ⊙ select')
      (.inv (alpha f s c) ⊙ (seqLeftTrack c (.step betaParent) ⊙ (select ⊙ mapCorrection))))
    (child : Cell (seqRightTrack h childNormal ⊙ select) (.step (.root (.rightId h)) ⊙ childCorrection)) :
    Cell (seqLeftTrack s (seqRightTrack f normal) ⊙
      (alpha f v s ⊙ (seqRightTrack f (.step betaCanonical) ⊙ select')))
      (seqLeftTrack s (.step (.root (.rightId f))) ⊙ (.step betaParent ⊙ (childCorrection ⊙ mapCorrection))) := by
  have one : Cell
      (seqLeftTrack s (seqRightTrack f normal) ⊙
        (alpha f v s ⊙ (seqRightTrack f (.step betaCanonical) ⊙ select')))
      (alpha f (.identity a) s ⊙ (seqRightTrack f (seqLeftTrack s normal) ⊙
        (seqRightTrack f (.step betaCanonical) ⊙ select'))) := by
    four_rewrite_ctx (UnitSelectionPasting.middlePath f normal s)
  have two : Cell
      (alpha f (.identity a) s ⊙ (seqRightTrack f (seqLeftTrack s normal) ⊙
        (seqRightTrack f (.step betaCanonical) ⊙ select')))
      (alpha f (.identity a) s ⊙ (seqRightTrack f (.step (.root (.leftId s))) ⊙
        (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
          (seqRightTrack f (seqRightTrack s childNormal) ⊙ (seqRightTrack f lift ⊙ select'))))) := by
    four_rewrite_ctx (whisker (.seqRight f) projected)
  have three : Cell
      (alpha f (.identity a) s ⊙ (seqRightTrack f (.step (.root (.leftId s))) ⊙
        (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
          (seqRightTrack f (seqRightTrack s childNormal) ⊙ (seqRightTrack f lift ⊙ select')))))
      (seqLeftTrack s (.step (.root (.rightId f))) ⊙
        (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
          (seqRightTrack f (seqRightTrack s childNormal) ⊙
            (.inv (alpha f s c) ⊙ (seqLeftTrack c (.step betaParent) ⊙ (select ⊙ mapCorrection)))))) := by
    refine Four.trans (q := seqLeftTrack s (.step (.root (.rightId f))) ⊙
      (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
        (seqRightTrack f (seqRightTrack s childNormal) ⊙ (seqRightTrack f lift ⊙ select')))) ?_ ?_
    · four_rewrite_ctx (categorical (CategoryCritical.middleUnitCell f s))
    · four_rewrite_ctx substitution
  have four : Cell
      (seqLeftTrack s (.step (.root (.rightId f))) ⊙
        (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
          (seqRightTrack f (seqRightTrack s childNormal) ⊙
            (.inv (alpha f s c) ⊙ (seqLeftTrack c (.step betaParent) ⊙ (select ⊙ mapCorrection))))))
      (seqLeftTrack s (.step (.root (.rightId f))) ⊙
        (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
          (.inv (alpha f s (.identity b)) ⊙
            (seqRightTrack (.seq f s) childNormal ⊙ (seqLeftTrack c (.step betaParent) ⊙ (select ⊙ mapCorrection)))))) := by
    four_rewrite_ctx (lastPostfixInverse f s childNormal)
  have five : Cell
      (seqLeftTrack s (.step (.root (.rightId f))) ⊙
        (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
          (.inv (alpha f s (.identity b)) ⊙
            (seqRightTrack (.seq f s) childNormal ⊙ (seqLeftTrack c (.step betaParent) ⊙ (select ⊙ mapCorrection))))))
      (seqLeftTrack s (.step (.root (.rightId f))) ⊙
        (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
          (.inv (alpha f s (.identity b)) ⊙
            (seqLeftTrack (.identity b) (.step betaParent) ⊙
              (seqRightTrack h childNormal ⊙ (select ⊙ mapCorrection)))))) := by
    four_rewrite_ctx (exchange betaParent childNormal).symm
  have six : Cell
      (seqLeftTrack s (.step (.root (.rightId f))) ⊙
        (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
          (.inv (alpha f s (.identity b)) ⊙
            (seqLeftTrack (.identity b) (.step betaParent) ⊙
              (seqRightTrack h childNormal ⊙ (select ⊙ mapCorrection))))))
      (seqLeftTrack s (.step (.root (.rightId f))) ⊙
        (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
          (.inv (alpha f s (.identity b)) ⊙
            (seqLeftTrack (.identity b) (.step betaParent) ⊙
              (.step (.root (.rightId h)) ⊙ (childCorrection ⊙ mapCorrection)))))) := by
    four_rewrite_ctx child
  have seven : Cell
      (seqLeftTrack s (.step (.root (.rightId f))) ⊙
        (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
          (.inv (alpha f s (.identity b)) ⊙
            (seqLeftTrack (.identity b) (.step betaParent) ⊙
              (.step (.root (.rightId h)) ⊙ (childCorrection ⊙ mapCorrection))))))
      (seqLeftTrack s (.step (.root (.rightId f))) ⊙
        (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
          (.inv (alpha f s (.identity b)) ⊙
            (.step (.root (.rightId (.seq f s))) ⊙ (.step betaParent ⊙ (childCorrection ⊙ mapCorrection)))))) := by
    four_rewrite_ctx (categorical (CategoryCritical.rightNatural betaParent)).symm
  have eight : Cell
      (seqLeftTrack s (.step (.root (.rightId f))) ⊙
        (seqRightTrack f (.inv (.step (.root (.rightId s)))) ⊙
          (.inv (alpha f s (.identity b)) ⊙
            (.step (.root (.rightId (.seq f s))) ⊙ (.step betaParent ⊙ (childCorrection ⊙ mapCorrection))))))
      (seqLeftTrack s (.step (.root (.rightId f))) ⊙ (.step betaParent ⊙ (childCorrection ⊙ mapCorrection))) := by
    four_rewrite_ctx (corner f s)
  exact one.trans (two.trans (three.trans (four.trans (five.trans (six.trans (seven.trans eight))))))

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.RightUnitPasting
