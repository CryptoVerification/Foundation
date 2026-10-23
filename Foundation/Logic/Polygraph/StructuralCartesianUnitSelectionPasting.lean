import Foundation.Logic.Polygraph.StructuralCartesianLiftSelectionCoherence
import Foundation.Logic.Polygraph.StructuralCartesianIdentityProjectionCoherence

/-! Derived pasting faces for the selection/substitution unit law. Actual
projection, lift/selection and child cells are inputs; no new generator or
unconditional arbitrary-path comparison is introduced. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.UnitSelectionPasting
open AssociatorPaths
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
local infixr:70 " ⊙ " => Track.comp

def middlePath {x a b c : Shape Atom} (f : Wire x a) {p q : Wire a b} (path : ProofTrack p q) (s : Wire b c) :
    Cell (seqLeftTrack s (seqRightTrack f path) ⊙ alpha f q s)
      (alpha f p s ⊙ seqRightTrack f (seqLeftTrack s path)) := by
  have face := FourNaturality.natural (Cells := Generator)
    (fun w : Wire a b => Wire.seq (Wire.seq f w) s) (fun w => Wire.seq f (Wire.seq w s))
    (fun change => Step.seqLeft (.seqRight f change) s) (fun change => Step.seqRight f (.seqLeft change s))
    (fun w => alpha f w s) (fun change => (categorical (CategoryCritical.assocMiddleNatural f change s)).symm) path
  simpa only [seqLeftTrack, seqRightTrack, FourNaturality.map_map] using face

def leftCorner {a b c : Shape Atom} (f : Wire a b) (s : Wire b c) :
    Cell (.inv (alpha (.identity a) f s) ⊙ seqLeftTrack s (.step (.root (.leftId f))))
      (.step (.root (.leftId (.seq f s)))) :=
  (Four.comp (.refl _) (categorical (CategoryCritical.leftUnitCell f s)).symm).trans
    (FourNaturality.undoInversePrefix _ _)

def unitCorner {a b c : Shape Atom} (f : Wire a b) (s : Wire b c) :
    Cell (.inv (alpha (.identity a) f s) ⊙ (seqLeftTrack s (.step (.root (.leftId f))) ⊙
      (.inv (seqLeftTrack s (.step (.root (.rightId f)))) ⊙
        (alpha f (.identity b) s ⊙ seqRightTrack f (.step (.root (.leftId s)))))))
      (.step (.root (.leftId (.seq f s)))) := by
  refine Four.trans (q := .inv (alpha (.identity a) f s) ⊙ (seqLeftTrack s (.step (.root (.leftId f))) ⊙
    (.inv (seqLeftTrack s (.step (.root (.rightId f)))) ⊙ seqLeftTrack s (.step (.root (.rightId f)))))) ?_ ?_
  · four_rewrite (categorical (CategoryCritical.middleUnitCell f s))
  · refine Four.trans ?_ (leftCorner f s)
    four_rewrite (Four.leftInv (G := Generator) (seqLeftTrack s (.step (.root (.rightId f)))))

def castIdentity {a b : Shape Atom} {p q : Wire a b} (same : p = q) : ProofTrack p q :=
  LiftSelection.targetCast same (.refl p)

def prefixCastComp {x a b : Shape Atom} (f : Wire x a) {p q : Wire a b} (first : p = q)
    {r : Wire x b} (second : Wire.seq f q = r) (total : Wire.seq f p = r) :
    Cell (seqRightTrack f (castIdentity first) ⊙ castIdentity second) (castIdentity total) := by
  cases first
  cases second
  exact Four.leftUnit _

/-- A projection face, a lift/selection face and the child unit face assemble
into the parent selector unit face. -/
def branch {x a b : Shape Atom} (f : Wire x a) (s : Wire a b)
    {v : Wire x x} {c : Wire a a} {p : Wire x a} {t : Wire a b} {t' : Wire x b}
    (normal : ProofTrack (.identity x) v) (childNormal : ProofTrack (.identity a) c)
    (beta : Step (.seq v f) p) (lift : ProofTrack (.seq f c) p)
    (select : ProofTrack (.seq c s) t) (select' : ProofTrack (.seq p s) t')
    (childCorrection : ProofTrack s t) (mapCorrection : ProofTrack (.seq f t) t')
    (parentCorrection : ProofTrack (.seq f s) t')
    (projected : Cell (seqLeftTrack f normal ⊙ .step beta)
      (.step (.root (.leftId f)) ⊙ (.inv (.step (.root (.rightId f))) ⊙ (seqRightTrack f childNormal ⊙ lift))))
    (liftSelect : Cell (seqLeftTrack s lift ⊙ select')
      (alpha f c s ⊙ (seqRightTrack f select ⊙ mapCorrection)))
    (child : Cell (seqLeftTrack s childNormal ⊙ select)
      (.step (.root (.leftId s)) ⊙ childCorrection))
    (corrections : Cell (seqRightTrack f childCorrection ⊙ mapCorrection) parentCorrection) :
    Cell (seqLeftTrack (.seq f s) normal ⊙ (.inv (alpha v f s) ⊙ (seqLeftTrack s (.step beta) ⊙ select')))
      (.step (.root (.leftId (.seq f s))) ⊙ parentCorrection) := by
  have one : Cell
      (seqLeftTrack (.seq f s) normal ⊙ (.inv (alpha v f s) ⊙ (seqLeftTrack s (.step beta) ⊙ select')))
      (.inv (alpha (.identity x) f s) ⊙ (seqLeftTrack s (seqLeftTrack f normal) ⊙ (seqLeftTrack s (.step beta) ⊙ select'))) := by
    four_rewrite (postfixInverse normal f s)
  have two : Cell
      (.inv (alpha (.identity x) f s) ⊙ (seqLeftTrack s (seqLeftTrack f normal) ⊙ (seqLeftTrack s (.step beta) ⊙ select')))
      (.inv (alpha (.identity x) f s) ⊙ (seqLeftTrack s (.step (.root (.leftId f))) ⊙
        (.inv (seqLeftTrack s (.step (.root (.rightId f)))) ⊙
          (seqLeftTrack s (seqRightTrack f childNormal) ⊙ (seqLeftTrack s lift ⊙ select'))))) := by
    four_rewrite (whisker (.seqLeft s) projected)
  have three : Cell
      (.inv (alpha (.identity x) f s) ⊙ (seqLeftTrack s (.step (.root (.leftId f))) ⊙
        (.inv (seqLeftTrack s (.step (.root (.rightId f)))) ⊙
          (seqLeftTrack s (seqRightTrack f childNormal) ⊙ (seqLeftTrack s lift ⊙ select')))))
      (.inv (alpha (.identity x) f s) ⊙ (seqLeftTrack s (.step (.root (.leftId f))) ⊙
        (.inv (seqLeftTrack s (.step (.root (.rightId f)))) ⊙
          (seqLeftTrack s (seqRightTrack f childNormal) ⊙ (alpha f c s ⊙ (seqRightTrack f select ⊙ mapCorrection)))))) := by
    four_rewrite liftSelect
  have four : Cell
      (.inv (alpha (.identity x) f s) ⊙ (seqLeftTrack s (.step (.root (.leftId f))) ⊙
        (.inv (seqLeftTrack s (.step (.root (.rightId f)))) ⊙
          (seqLeftTrack s (seqRightTrack f childNormal) ⊙ (alpha f c s ⊙ (seqRightTrack f select ⊙ mapCorrection))))))
      (.inv (alpha (.identity x) f s) ⊙ (seqLeftTrack s (.step (.root (.leftId f))) ⊙
        (.inv (seqLeftTrack s (.step (.root (.rightId f)))) ⊙
          (alpha f (.identity a) s ⊙ (seqRightTrack f (seqLeftTrack s childNormal) ⊙ (seqRightTrack f select ⊙ mapCorrection)))))) := by
    four_rewrite (middlePath f childNormal s)
  have five : Cell
      (.inv (alpha (.identity x) f s) ⊙ (seqLeftTrack s (.step (.root (.leftId f))) ⊙
        (.inv (seqLeftTrack s (.step (.root (.rightId f)))) ⊙
          (alpha f (.identity a) s ⊙ (seqRightTrack f (seqLeftTrack s childNormal) ⊙ (seqRightTrack f select ⊙ mapCorrection))))))
      (.inv (alpha (.identity x) f s) ⊙ (seqLeftTrack s (.step (.root (.leftId f))) ⊙
        (.inv (seqLeftTrack s (.step (.root (.rightId f)))) ⊙
          (alpha f (.identity a) s ⊙ (seqRightTrack f (.step (.root (.leftId s))) ⊙ (seqRightTrack f childCorrection ⊙ mapCorrection)))))) := by
    four_rewrite (whisker (.seqRight f) child)
  have six : Cell
      (.inv (alpha (.identity x) f s) ⊙ (seqLeftTrack s (.step (.root (.leftId f))) ⊙
        (.inv (seqLeftTrack s (.step (.root (.rightId f)))) ⊙
          (alpha f (.identity a) s ⊙ (seqRightTrack f (.step (.root (.leftId s))) ⊙ (seqRightTrack f childCorrection ⊙ mapCorrection))))))
      (.step (.root (.leftId (.seq f s))) ⊙ (seqRightTrack f childCorrection ⊙ mapCorrection)) := by
    four_rewrite (unitCorner f s)
  have seven : Cell (.step (.root (.leftId (.seq f s))) ⊙ (seqRightTrack f childCorrection ⊙ mapCorrection))
      (.step (.root (.leftId (.seq f s))) ⊙ parentCorrection) := by
    four_rewrite corrections
  exact one.trans (two.trans (three.trans (four.trans (five.trans (six.trans seven)))))

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.UnitSelectionPasting
