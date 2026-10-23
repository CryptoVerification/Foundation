import Foundation.Crypto.Logic.Polygraph.MixedCircuitHigher

/-! Construct higher comparison data for directed parallel rewrite proofs.
Only separated exchange generators and the free proof-groupoid laws occur.
A common suffix is cancelled in the groupoid of REWRITE PROOFS, never in the
category of stochastic executions. Pure wiring is still fixed by the input
catalogue; its structural rewrite coherence is not inferred. -/
namespace CryptoLogic.Polygraph.MixedCircuit
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}

namespace Resolution

def square {n m} {a b c : Circuit signature n m} {first : Step relators a b} {second : Step relators a c}
    (result : Resolution first second) :
    Homotopy (route first result.join.afterFirst) (route second result.join.afterSecond) :=
  match result with
  | .same destinations edges => by
      cases destinations
      cases eq_of_heq edges
      exact .refl _
  | .separate witness => .generator (.separated witness)

end Resolution

def Step.localSquare (rigid : RootRigid relators) {n m} {a b c : Circuit signature n m}
    (first : Step relators a b) (second : Step relators a c) :
    Homotopy (route first (first.localJoin rigid second).afterFirst) (route second (first.localJoin rigid second).afterSecond) :=
  (first.resolve rigid second).square

namespace Homotopy

def pathComp {n m} : {a b c : Circuit signature n m} → (p : Path (relators := relators) a b) → (q : Path (relators := relators) b c) →
    Homotopy (Track.ofPath (p.comp q)) (.comp (Track.ofPath p) (Track.ofPath q))
  | _, _, _, .refl _, q => (Four.leftUnit (G := Exchange) (Track.ofPath q)).symm
  | _, _, _, .cons change tail, q =>
      (Four.comp (Four.refl (.step change)) (pathComp tail q)).trans
        (Four.assoc (.step change) (Track.ofPath tail) (Track.ofPath q)).symm

def continueRoute {n m} {a b c d : Circuit signature n m} (change : Step relators a b)
    (p : Path (relators := relators) b c) (q : Path (relators := relators) c d) :
    Homotopy (route change (p.comp q)) (.comp (route change p) (Track.ofPath q)) :=
  (Four.comp (Four.refl (.step change)) (pathComp p q)).trans
    (Four.assoc (.step change) (Track.ofPath p) (Track.ofPath q)).symm

/-- Formal inverse here reverses an equality-preserving circuit rewrite,
not execution of a game or its conditional kernel. -/
def cancelRight {n m} {a b c : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (tail : RewriteTrack (relators := relators) b c) (square : Homotopy (.comp p tail) (.comp q tail)) : Homotopy p q :=
  (Four.rightUnit (G := Exchange) p).symm.trans
    ((Four.comp (Four.refl p) (Four.rightInv tail).symm).trans
      ((Four.assoc p tail (.inv tail)).symm.trans
        ((Four.comp square (Four.refl (.inv tail))).trans
          ((Four.assoc q tail (.inv tail)).trans
            ((Four.comp (Four.refl q) (Four.rightInv tail)).trans (Four.rightUnit q))))))

theorem cancelRight_support {n m} {a b c : Circuit signature n m} {p q : RewriteTrack (relators := relators) a b}
    (tail : RewriteTrack (relators := relators) b c) (square : Homotopy (.comp p tail) (.comp q tail)) :
    RewriteTrack.support tail ⊆ Homotopy.support (cancelRight tail square) := by
  intro label member
  simp only [cancelRight, Homotopy.support, RewriteTrack.support, Finset.mem_union]
  tauto

end Homotopy

/-- Complete an actual prefix to a supplied reachable irreducible endpoint.
No normalization-square generator or arbitrary parallel-path oracle is used. -/
def completeToTerminal (strategy : Strategy relators) (rigid : RootRigid relators) {n m}
    {a b terminal : Circuit signature n m} (stopped : ∀ {target}, Step relators terminal target → False)
    (reach : Path (relators := relators) a terminal) (prefixPath : Path (relators := relators) a b) :
    Path (relators := relators) b terminal := by
  let joined := joinPaths strategy rigid prefixPath reach
  have same : terminal = joined.output := joined.right.terminal stopped
  exact same.symm ▸ joined.left

/-- Every pair of directed rewrite paths to the same irreducible endpoint
has a higher witness generated from local exchanges and groupoid laws. -/
def terminalCoherence (strategy : Strategy relators) (rigid : RootRigid relators) :
    {n m : Port signature} → {a terminal : Circuit signature n m} →
    (stopped : ∀ {target}, Step relators terminal target → False) →
    (p q : Path (relators := relators) a terminal) → Homotopy (Track.ofPath p) (Track.ofPath q)
  | _, _, _, _, _, .refl _, .refl _ => .refl _
  | _, _, _, _, stopped, .refl _, .cons change _ => False.elim (stopped change)
  | _, _, _, _, stopped, .cons change _, .refl _ => False.elim (stopped change)
  | _, _, _, _, stopped, .cons first p, .cons second q =>
      let branch := first.localJoin rigid second
      let tail := completeToTerminal strategy rigid stopped p branch.afterFirst
      let one := terminalCoherence strategy rigid stopped p (branch.afterFirst.comp tail)
      let two := terminalCoherence strategy rigid stopped q (branch.afterSecond.comp tail)
      (Four.comp (Four.refl (.step first)) one).trans
        ((Homotopy.continueRoute first branch.afterFirst tail).trans
          ((Four.comp (first.localSquare rigid second) (Four.refl (Track.ofPath tail))).trans
            ((Homotopy.continueRoute second branch.afterSecond tail).symm.trans
              (Four.comp (Four.refl (.step second)) two).symm)))
termination_by _ _ a _ _ _ _ => strategy.rank a
decreasing_by
  · exact strategy.decreases first
  · exact strategy.decreases second

/-- Any directed parallel rewrite proofs, including those ending before
normalization, are compared without an arbitrary higher-cell generator. -/
def directedCoherence (strategy : Strategy relators) (rigid : RootRigid relators) {n m}
    {a b : Circuit signature n m} (p q : Path (relators := relators) a b) : Homotopy (Track.ofPath p) (Track.ofPath q) :=
  let suffix := (normalize strategy b).path
  let whole := terminalCoherence strategy rigid (normalize strategy b).stopped (p.comp suffix) (q.comp suffix)
  Homotopy.cancelRight (Track.ofPath suffix)
    ((Homotopy.pathComp p suffix).symm.trans (whole.trans (Homotopy.pathComp q suffix)))

/-- The chosen normalization suffix is still a dependency of the constructed
witness after formal cancellation; it is not inferred to be necessary. -/
theorem directedCoherence_suffix_support (strategy : Strategy relators) (rigid : RootRigid relators) {n m}
    {a b : Circuit signature n m} (p q : Path (relators := relators) a b) :
    Path.support (normalize strategy b).path ⊆ Homotopy.support (directedCoherence strategy rigid p q) := by
  simpa only [directedCoherence, ← RewriteTrack.ofPath_support] using
    Homotopy.cancelRight_support (Track.ofPath (normalize strategy b).path)
      ((Homotopy.pathComp p (normalize strategy b).path).symm.trans
        ((terminalCoherence strategy rigid (normalize strategy b).stopped
          (p.comp (normalize strategy b).path) (q.comp (normalize strategy b).path)).trans
          (Homotopy.pathComp q (normalize strategy b).path)))

end CryptoLogic.Polygraph.MixedCircuit
