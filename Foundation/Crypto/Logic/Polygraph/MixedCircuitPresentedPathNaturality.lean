import Foundation.Crypto.Logic.Polygraph.MixedCircuitPresentedHigher
import Foundation.Crypto.Logic.Polygraph.MixedCircuitPathNaturalitySupport

/-! Path-valued naturality with an arbitrary supplied higher presentation.
Every interior generator guard is kept by the presentation's support function.
No completeness or finiteness of the presentation is inferred. -/
namespace CryptoLogic.Polygraph.MixedCircuit.PresentedPathNaturality
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}
variable {basis : HigherBasis relators}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem undoRight_support {a b} {p q r : Circuit signature a b}
    (one : RewriteTrack (relators := relators) p q) (two : RewriteTrack (relators := relators) q r) :
    PresentedCell.support (basis := basis) (FourNaturality.undoRight one two) = one.support ∪ two.support := by
  simp only [FourNaturality.undoRight, PresentedCell.support, RewriteTrack.support]
  ext label
  simp only [Finset.mem_union]
  tauto

theorem undoLeft_support {a b} {p q r : Circuit signature a b}
    (one : RewriteTrack (relators := relators) p q) (two : RewriteTrack (relators := relators) p r) :
    PresentedCell.support (basis := basis) (FourNaturality.undoLeft one two) = one.support ∪ two.support := by
  simp only [FourNaturality.undoLeft, PresentedCell.support, RewriteTrack.support]
  ext label
  simp only [Finset.mem_union]
  tauto

theorem undoInversePrefix_support {a b} {p q r : Circuit signature a b}
    (one : RewriteTrack (relators := relators) p q) (two : RewriteTrack (relators := relators) q r) :
    PresentedCell.support (basis := basis) (FourNaturality.undoInversePrefix one two) = one.support ∪ two.support := by
  simp only [FourNaturality.undoInversePrefix, PresentedCell.support, RewriteTrack.support]
  ext label
  simp only [Finset.mem_union]
  tauto

theorem cancelPrefix_support {a b} {p q r : Circuit signature a b}
    (head : RewriteTrack (relators := relators) p q)
    {one two : RewriteTrack (relators := relators) q r}
    (cell : PresentedCell basis (.comp head one) (.comp head two)) :
    PresentedCell.support (basis := basis) (FourNaturality.cancelPrefix head cell) = cell.support := by
  simp only [FourNaturality.cancelPrefix, PresentedCell.support, undoInversePrefix_support, RewriteTrack.support]
  ext label
  have left : label ∈ head.support ∪ one.support → label ∈ cell.support := fun member => cell.boundaries.1 member
  have right : label ∈ head.support ∪ two.support → label ∈ cell.support := fun member => cell.boundaries.2 member
  simp only [Finset.mem_union] at *
  tauto

theorem invertSquare_support {a b} {p q r s : Circuit signature a b}
    (one : RewriteTrack (relators := relators) p q) (two : RewriteTrack (relators := relators) q s)
    (three : RewriteTrack (relators := relators) p r) (four : RewriteTrack (relators := relators) r s)
    (cell : PresentedCell basis (.comp one two) (.comp three four)) :
    PresentedCell.support (basis := basis) (FourNaturality.invertSquare one two three four cell) = PresentedCell.support (basis := basis) cell := by
  rw [FourNaturality.invertSquare, cancelPrefix_support]
  simp only [PresentedCell.support, undoLeft_support, undoRight_support, RewriteTrack.support]
  ext label
  have left : label ∈ one.support ∪ two.support → label ∈ cell.support := fun member => cell.boundaries.1 member
  have right : label ∈ three.support ∪ four.support → label ∈ cell.support := fun member => cell.boundaries.2 member
  simp only [Finset.mem_union] at *
  tauto

theorem natural_support {SourceRule : Type} {sourceRules : SourceRule → Relator signature} {a b c d : Port signature}
    (f g : Circuit signature a b → Circuit signature c d)
    (mapF : ∀ {p q}, Step sourceRules p q → RewriteTrack (relators := relators) (f p) (f q))
    (mapG : ∀ {p q}, Step sourceRules p q → RewriteTrack (relators := relators) (g p) (g q))
    (component : ∀ p, RewriteTrack (relators := relators) (f p) (g p))
    (stepSquare : ∀ {p q} (change : Step sourceRules p q),
      PresentedCell basis (.comp (mapF change) (component q)) (.comp (component p) (mapG change)))
    (fixed : Finset Requirement)
    (firstBound : ∀ {p q} (path : RewriteTrack (relators := sourceRules) p q),
      RewriteTrack.support (FourPathNaturality.replace f mapF path) ⊆ RewriteTrack.support path ∪ fixed)
    (secondBound : ∀ {p q} (path : RewriteTrack (relators := sourceRules) p q),
      RewriteTrack.support (FourPathNaturality.replace g mapG path) ⊆ RewriteTrack.support path ∪ fixed)
    (componentSupport : ∀ p, (component p).support = p.needs ∪ fixed)
    (stepSupport : ∀ {p q} (change : Step sourceRules p q), (stepSquare change).support = change.support ∪ fixed)
    {p q} (path : RewriteTrack (relators := sourceRules) p q) :
    PresentedCell.support (basis := basis) (FourPathNaturality.natural f g mapF mapG component stepSquare path) = RewriteTrack.support path ∪ fixed := by
  induction path with
  | refl p => simp only [FourPathNaturality.natural, PresentedCell.support, componentSupport, RewriteTrack.support, Finset.union_self]
  | step change => exact stepSupport change
  | @comp x y z first second one two =>
      simp only [FourPathNaturality.natural, PresentedCell.support, one, two, componentSupport, RewriteTrack.support, FourPathNaturality.replace]
      exact TrackExchange.natural_union (RewriteTrack.support first) (RewriteTrack.support second) fixed
        (RewriteTrack.support (FourPathNaturality.replace f mapF first)) (RewriteTrack.support (FourPathNaturality.replace f mapF second))
        (RewriteTrack.support (FourPathNaturality.replace g mapG first)) (RewriteTrack.support (FourPathNaturality.replace g mapG second))
        x.needs y.needs z.needs (firstBound first) (firstBound second) (secondBound first) (secondBound second)
        (RewriteTrack.boundaries first).1 (RewriteTrack.boundaries first).2 (RewriteTrack.boundaries second).2
  | @inv x y child ih =>
      exact (invertSquare_support (FourPathNaturality.replace f mapF child) (component y) (component x) (FourPathNaturality.replace g mapG child)
        (FourPathNaturality.natural f g mapF mapG component stepSquare child)).trans ih

end CryptoLogic.Polygraph.MixedCircuit.PresentedPathNaturality
