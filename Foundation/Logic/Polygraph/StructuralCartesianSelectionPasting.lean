import Foundation.Logic.Polygraph.StructuralCartesianAssociatorPaths
import Foundation.Logic.Polygraph.StructuralCartesianProjectedTrackNaturality

/-! Bounded projection/distribution squares and a generic selector-suffix
pasting rule, constructed from actual supplied cells. The pasting rule is a
derivation, not a generator accepting arbitrary parallel paths. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.SelectionPasting
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
open AssociatorPaths
local infixr:70 " ⊙ " => Track.comp

def distributedLift {x a b c : Shape Atom} (f : Wire x a) (p : Wire a b) (q : Wire a c)
    {p' : Wire x b} {q' : Wire x c} (first : ProofTrack (.seq f p) p') (second : ProofTrack (.seq f q) q') :=
  Track.step (Step.root (.forkAfter f p q)) ⊙ ProjectedTrackNaturality.forkPaths first second

def fstSquare {x a b c : Shape Atom} (f : Wire x a) (p : Wire a b) (q : Wire a c)
    {p' : Wire x b} {q' : Wire x c} (first : ProofTrack (.seq f p) p') (second : ProofTrack (.seq f q) q') :
    Cell (seqLeftTrack (fst b c) (distributedLift f p q first second) ⊙ .step (.root (.betaFst p' q')))
      (alpha f (fork p q) (fst b c) ⊙ (seqRightTrack f (.step (.root (.betaFst p q))) ⊙ first)) := by
  refine Four.trans (q := seqLeftTrack (fst b c) (.step (.root (.forkAfter f p q))) ⊙
    (.step (.root (.betaFst (.seq f p) (.seq f q))) ⊙ first)) ?_ ?_
  · four_rewrite (oldLift (ProjectedTrackNaturality.fstBoth first second))
  · four_rewrite (embed (DistributionCritical.fstCell f p q))

def sndSquare {x a b c : Shape Atom} (f : Wire x a) (p : Wire a b) (q : Wire a c)
    {p' : Wire x b} {q' : Wire x c} (first : ProofTrack (.seq f p) p') (second : ProofTrack (.seq f q) q') :
    Cell (seqLeftTrack (snd b c) (distributedLift f p q first second) ⊙ .step (.root (.betaSnd p' q')))
      (alpha f (fork p q) (snd b c) ⊙ (seqRightTrack f (.step (.root (.betaSnd p q))) ⊙ second)) := by
  refine Four.trans (q := seqLeftTrack (snd b c) (.step (.root (.forkAfter f p q))) ⊙
    (.step (.root (.betaSnd (.seq f p) (.seq f q))) ⊙ second)) ?_ ?_
  · four_rewrite (oldLift (ProjectedTrackNaturality.sndBoth first second))
  · four_rewrite (embed (DistributionCritical.sndCell f p q))

/-- Extend an actual projection square by a selector suffix and an actual
inductive child square. The only added faces are categorical naturality and
the pentagon; no normalization comparison is assumed. -/
def suffix {u a b c d : Shape Atom} (f : Wire u a) (v : Wire a b) (h : Wire b c) (s : Wire c d)
    {v' : Wire u b} {p : Wire a c} {p' : Wire u c} {t : Wire a d} {t' : Wire u d}
    (beta : Step (.seq v h) p) (beta' : Step (.seq v' h) p')
    (liftV : ProofTrack (.seq f v) v') (liftP : ProofTrack (.seq f p) p')
    (select : ProofTrack (.seq p s) t) (select' : ProofTrack (.seq p' s) t')
    (liftTarget : ProofTrack (.seq f t) t')
    (projection : Cell (seqLeftTrack h liftV ⊙ .step beta')
      (alpha f v h ⊙ (seqRightTrack f (.step beta) ⊙ liftP)))
    (child : Cell (seqLeftTrack s liftP ⊙ select')
      (alpha f p s ⊙ (seqRightTrack f select ⊙ liftTarget))) :
    Cell (seqLeftTrack (.seq h s) liftV ⊙
      (.inv (alpha v' h s) ⊙ (seqLeftTrack s (.step beta') ⊙ select')))
      (alpha f v (.seq h s) ⊙
        (seqRightTrack f (.inv (alpha v h s) ⊙ (seqLeftTrack s (.step beta) ⊙ select)) ⊙ liftTarget)) := by
  have one : Cell
      (seqLeftTrack (.seq h s) liftV ⊙ (.inv (alpha v' h s) ⊙ (seqLeftTrack s (.step beta') ⊙ select')))
      (.inv (alpha (.seq f v) h s) ⊙
        (seqLeftTrack s (seqLeftTrack h liftV) ⊙ (seqLeftTrack s (.step beta') ⊙ select'))) := by
    four_rewrite (postfixInverse liftV h s)
  have two : Cell
      (.inv (alpha (.seq f v) h s) ⊙
        (seqLeftTrack s (seqLeftTrack h liftV) ⊙ (seqLeftTrack s (.step beta') ⊙ select')))
      (.inv (alpha (.seq f v) h s) ⊙ (seqLeftTrack s (alpha f v h) ⊙
        (seqLeftTrack s (seqRightTrack f (.step beta)) ⊙ (seqLeftTrack s liftP ⊙ select')))) := by
    four_rewrite (whisker (.seqLeft s) projection)
  have three : Cell
      (.inv (alpha (.seq f v) h s) ⊙ (seqLeftTrack s (alpha f v h) ⊙
        (seqLeftTrack s (seqRightTrack f (.step beta)) ⊙ (seqLeftTrack s liftP ⊙ select'))))
      (.inv (alpha (.seq f v) h s) ⊙ (seqLeftTrack s (alpha f v h) ⊙
        (seqLeftTrack s (seqRightTrack f (.step beta)) ⊙ (alpha f p s ⊙ (seqRightTrack f select ⊙ liftTarget))))) := by
    four_rewrite child
  have four : Cell
      (.inv (alpha (.seq f v) h s) ⊙ (seqLeftTrack s (alpha f v h) ⊙
        (seqLeftTrack s (seqRightTrack f (.step beta)) ⊙ (alpha f p s ⊙ (seqRightTrack f select ⊙ liftTarget)))))
      (.inv (alpha (.seq f v) h s) ⊙ (seqLeftTrack s (alpha f v h) ⊙
        (alpha f (.seq v h) s ⊙ (seqRightTrack f (seqLeftTrack s (.step beta)) ⊙ (seqRightTrack f select ⊙ liftTarget))))) := by
    four_rewrite (middleStep f beta s)
  have five : Cell
      (.inv (alpha (.seq f v) h s) ⊙ (seqLeftTrack s (alpha f v h) ⊙
        (alpha f (.seq v h) s ⊙ (seqRightTrack f (seqLeftTrack s (.step beta)) ⊙ (seqRightTrack f select ⊙ liftTarget)))))
      (alpha f v (.seq h s) ⊙
        (seqRightTrack f (.inv (alpha v h s) ⊙ (seqLeftTrack s (.step beta) ⊙ select)) ⊙ liftTarget)) := by
    four_rewrite (pentagonCorner f v h s)
  exact one.trans (two.trans (three.trans (four.trans five)))

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.SelectionPasting
