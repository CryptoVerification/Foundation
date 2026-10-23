import Foundation.Logic.Polygraph.StructuralCartesianDistributionCompositionCoherence
import Foundation.Logic.Polygraph.StructuralCartesianExpansionLoopCoherence

/-! Pasting the two child substitution comparisons through a product output.
All paths and both child cells are explicit inputs. This is a derived rule in
the existing finite presentation, not an additional whole-path generator. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.DistributionSubstitutionPasting
open AssociatorPaths DistributionComposition LoopCoherence
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false
local infixr:70 " ⊙ " => Track.comp

/-- Distribution, prefix naturality and the two child comparisons assemble
the product case of composition through a projected layout. -/
def pair {x a b c d : Shape Atom} (f : Wire x a) (g : Wire a b) {h : Wire x b}
    (p : Wire b c) (q : Wire b d) {p' : Wire a c} {q' : Wire a d} {u : Wire x c} {v : Wire x d}
    (beta : ProofTrack (.seq f g) h)
    (left : ProofTrack (.seq g p) p') (right : ProofTrack (.seq g q) q')
    (leftNext : ProofTrack (.seq f p') u) (rightNext : ProofTrack (.seq f q') v)
    (leftTarget : ProofTrack (.seq h p) u) (rightTarget : ProofTrack (.seq h q) v)
    (leftCell : Cell (seqRightTrack f left ⊙ leftNext)
      (.inv (alpha f g p) ⊙ (seqLeftTrack p beta ⊙ leftTarget)))
    (rightCell : Cell (seqRightTrack f right ⊙ rightNext)
      (.inv (alpha f g q) ⊙ (seqLeftTrack q beta ⊙ rightTarget))) :
    Cell (seqRightTrack f (distribute g p q ⊙ forkTracks left right) ⊙
      (distribute f p' q' ⊙ forkTracks leftNext rightNext))
      (.inv (alpha f g (fork p q)) ⊙ (seqLeftTrack (fork p q) beta ⊙
        (distribute h p q ⊙ forkTracks leftTarget rightTarget))) := by
  have one : Cell
      (seqRightTrack f (distribute g p q ⊙ forkTracks left right) ⊙
        (distribute f p' q' ⊙ forkTracks leftNext rightNext))
      (seqRightTrack f (distribute g p q) ⊙ (distribute f (.seq g p) (.seq g q) ⊙
        (forkTracks (seqRightTrack f left) (seqRightTrack f right) ⊙ forkTracks leftNext rightNext))) := by
    four_rewrite_ctx (arguments f left right)
  have two : Cell
      (seqRightTrack f (distribute g p q) ⊙ (distribute f (.seq g p) (.seq g q) ⊙
        (forkTracks (seqRightTrack f left) (seqRightTrack f right) ⊙ forkTracks leftNext rightNext)))
      (seqRightTrack f (distribute g p q) ⊙ (distribute f (.seq g p) (.seq g q) ⊙
        forkTracks (seqRightTrack f left ⊙ leftNext) (seqRightTrack f right ⊙ rightNext))) := by
    four_rewrite_ctx (forkComp (seqRightTrack f left) leftNext (seqRightTrack f right) rightNext).symm
  have three : Cell
      (seqRightTrack f (distribute g p q) ⊙ (distribute f (.seq g p) (.seq g q) ⊙
        forkTracks (seqRightTrack f left ⊙ leftNext) (seqRightTrack f right ⊙ rightNext)))
      (seqRightTrack f (distribute g p q) ⊙ (distribute f (.seq g p) (.seq g q) ⊙
        forkTracks (.inv (alpha f g p) ⊙ (seqLeftTrack p beta ⊙ leftTarget))
          (.inv (alpha f g q) ⊙ (seqLeftTrack q beta ⊙ rightTarget)))) := by
    four_rewrite_ctx (forkCells leftCell rightCell)
  have four : Cell
      (seqRightTrack f (distribute g p q) ⊙ (distribute f (.seq g p) (.seq g q) ⊙
        forkTracks (.inv (alpha f g p) ⊙ (seqLeftTrack p beta ⊙ leftTarget))
          (.inv (alpha f g q) ⊙ (seqLeftTrack q beta ⊙ rightTarget))))
      (.inv (alpha f g (fork p q)) ⊙ (distribute (.seq f g) p q ⊙
        (forkTracks (alpha f g p) (alpha f g q) ⊙
          forkTracks (.inv (alpha f g p) ⊙ (seqLeftTrack p beta ⊙ leftTarget))
            (.inv (alpha f g q) ⊙ (seqLeftTrack q beta ⊙ rightTarget))))) := by
    four_rewrite_ctx (associationCorner f g p q)
  have five : Cell
      (.inv (alpha f g (fork p q)) ⊙ (distribute (.seq f g) p q ⊙
        (forkTracks (alpha f g p) (alpha f g q) ⊙
          forkTracks (.inv (alpha f g p) ⊙ (seqLeftTrack p beta ⊙ leftTarget))
            (.inv (alpha f g q) ⊙ (seqLeftTrack q beta ⊙ rightTarget)))))
      (.inv (alpha f g (fork p q)) ⊙ (distribute (.seq f g) p q ⊙
        forkTracks (alpha f g p ⊙ (.inv (alpha f g p) ⊙ (seqLeftTrack p beta ⊙ leftTarget)))
          (alpha f g q ⊙ (.inv (alpha f g q) ⊙ (seqLeftTrack q beta ⊙ rightTarget))))) := by
    four_rewrite_ctx (forkComp (alpha f g p) (.inv (alpha f g p) ⊙ (seqLeftTrack p beta ⊙ leftTarget))
      (alpha f g q) (.inv (alpha f g q) ⊙ (seqLeftTrack q beta ⊙ rightTarget))).symm
  have six : Cell
      (.inv (alpha f g (fork p q)) ⊙ (distribute (.seq f g) p q ⊙
        forkTracks (alpha f g p ⊙ (.inv (alpha f g p) ⊙ (seqLeftTrack p beta ⊙ leftTarget)))
          (alpha f g q ⊙ (.inv (alpha f g q) ⊙ (seqLeftTrack q beta ⊙ rightTarget)))))
      (.inv (alpha f g (fork p q)) ⊙ (distribute (.seq f g) p q ⊙
        forkTracks (seqLeftTrack p beta ⊙ leftTarget) (seqLeftTrack q beta ⊙ rightTarget))) := by
    four_rewrite_ctx (forkCells (FourNaturality.undoLeft (alpha f g p) (seqLeftTrack p beta ⊙ leftTarget))
      (FourNaturality.undoLeft (alpha f g q) (seqLeftTrack q beta ⊙ rightTarget)))
  have seven : Cell
      (.inv (alpha f g (fork p q)) ⊙ (distribute (.seq f g) p q ⊙
        forkTracks (seqLeftTrack p beta ⊙ leftTarget) (seqLeftTrack q beta ⊙ rightTarget)))
      (.inv (alpha f g (fork p q)) ⊙ (distribute (.seq f g) p q ⊙
        (forkTracks (seqLeftTrack p beta) (seqLeftTrack q beta) ⊙ forkTracks leftTarget rightTarget))) := by
    four_rewrite_ctx (forkComp (seqLeftTrack p beta) leftTarget (seqLeftTrack q beta) rightTarget)
  have eight : Cell
      (.inv (alpha f g (fork p q)) ⊙ (distribute (.seq f g) p q ⊙
        (forkTracks (seqLeftTrack p beta) (seqLeftTrack q beta) ⊙ forkTracks leftTarget rightTarget)))
      (.inv (alpha f g (fork p q)) ⊙ (seqLeftTrack (fork p q) beta ⊙
        (distribute h p q ⊙ forkTracks leftTarget rightTarget))) := by
    four_rewrite_ctx (prefixPath beta p q).symm
  exact one.trans (two.trans (three.trans (four.trans (five.trans (six.trans (seven.trans eight))))))

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ExpansionCritical.DistributionSubstitutionPasting
