import Foundation.Logic.Polygraph.FourPathNaturality
import Foundation.Crypto.Logic.Polygraph.MixedCircuitTrackExchangeSupport

/-! Exact interior guard accounting for path-valued naturality, retaining
zero-step and multi-step edge images without new higher generators. -/
namespace CryptoLogic.Polygraph.MixedCircuit.PathNaturality
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem natural_support {SourceRule : Type} {sourceRules : SourceRule → Relator signature} {a b c d : Port signature}
    (f g : Circuit signature a b → Circuit signature c d)
    (mapF : ∀ {p q}, Step sourceRules p q → RewriteTrack (relators := relators) (f p) (f q))
    (mapG : ∀ {p q}, Step sourceRules p q → RewriteTrack (relators := relators) (g p) (g q))
    (component : ∀ p, RewriteTrack (relators := relators) (f p) (g p))
    (stepSquare : ∀ {p q} (change : Step sourceRules p q),
      Homotopy (.comp (mapF change) (component q)) (.comp (component p) (mapG change)))
    (fixed : Finset Requirement)
    (firstBound : ∀ {p q} (path : RewriteTrack (relators := sourceRules) p q),
      RewriteTrack.support (FourPathNaturality.replace f mapF path) ⊆ RewriteTrack.support path ∪ fixed)
    (secondBound : ∀ {p q} (path : RewriteTrack (relators := sourceRules) p q),
      RewriteTrack.support (FourPathNaturality.replace g mapG path) ⊆ RewriteTrack.support path ∪ fixed)
    (componentSupport : ∀ p, (component p).support = p.needs ∪ fixed)
    (stepSupport : ∀ {p q} (change : Step sourceRules p q), (stepSquare change).support = change.support ∪ fixed)
    {p q} (path : RewriteTrack (relators := sourceRules) p q) :
    Homotopy.support (FourPathNaturality.natural f g mapF mapG component stepSquare path) = RewriteTrack.support path ∪ fixed := by
  induction path with
  | refl p => simp only [FourPathNaturality.natural, Homotopy.support, componentSupport, RewriteTrack.support, Finset.union_self]
  | step change => exact stepSupport change
  | @comp x y z first second one two =>
      simp only [FourPathNaturality.natural, Homotopy.support, one, two, componentSupport, RewriteTrack.support, FourPathNaturality.replace]
      exact TrackExchange.natural_union (RewriteTrack.support first) (RewriteTrack.support second) fixed
        (RewriteTrack.support (FourPathNaturality.replace f mapF first)) (RewriteTrack.support (FourPathNaturality.replace f mapF second))
        (RewriteTrack.support (FourPathNaturality.replace g mapG first)) (RewriteTrack.support (FourPathNaturality.replace g mapG second))
        x.needs y.needs z.needs (firstBound first) (firstBound second) (secondBound first) (secondBound second)
        (RewriteTrack.boundaries first).1 (RewriteTrack.boundaries first).2 (RewriteTrack.boundaries second).2
  | @inv x y child ih =>
      exact (TrackExchange.invertSquare_support (FourPathNaturality.replace f mapF child) (component y) (component x) (FourPathNaturality.replace g mapG child)
        (FourPathNaturality.natural f g mapF mapG component stepSquare child)).trans ih

end CryptoLogic.Polygraph.MixedCircuit.PathNaturality
