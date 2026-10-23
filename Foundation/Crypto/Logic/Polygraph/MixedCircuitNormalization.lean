import Foundation.Crypto.Logic.Polygraph.MixedCircuitRootResolution

/-! Constructive guarded confluence and normalization for a rigid mixed
catalogue. The input is an actual decreasing step selector, not a supplied
normalizing square. Pure wiring is still whatever the catalogue exposes. -/
namespace CryptoLogic.Polygraph.MixedCircuit
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Foundation.Logic.Polygraph
set_option backward.isDefEq.respectTransparency false
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}

namespace Path

theorem comp_support {n m} {a b c : Circuit signature n m}
    (first : Path (relators := relators) a b) (second : Path (relators := relators) b c) :
    support (first.comp second) = support first ∪ support second := by
  induction first with
  | refl =>
      simpa only [RewritePath.comp, support] using (Finset.union_eq_right.mpr second.boundaries.1).symm
  | cons change tail ih => simp only [RewritePath.comp, support, ih, Finset.union_assoc]

omit [DecidableEq Requirement] in
theorem terminal {n m} {a b : Circuit signature n m} (path : Path (relators := relators) a b)
    (stopped : ∀ {target}, Step relators a target → False) : a = b := by
  cases path with
  | refl => rfl
  | cons change tail => exact False.elim (stopped change)

end Path

inductive Selection {n m} (circuit : Circuit signature n m) where
  | done (stopped : ∀ {target}, Step relators circuit target → False)
  | more {target} (change : Step relators circuit target)

structure Strategy (relators : Rule → Relator signature) where
  rank : {n m : Port signature} → Circuit signature n m → Nat
  decreases : ∀ {n m} {a b : Circuit signature n m}, Step relators a b → rank b < rank a
  select : ∀ {n m} (circuit : Circuit signature n m), Selection (relators := relators) circuit

namespace Path
omit [DecidableEq Requirement] in
theorem rank_le (strategy : Strategy relators) {n m} {a b : Circuit signature n m}
    (path : Path (relators := relators) a b) : strategy.rank b ≤ strategy.rank a := by
  induction path with
  | refl => exact Nat.le_refl _
  | cons change tail ih => exact ih.trans (Nat.le_of_lt (strategy.decreases change))
end Path

structure Normalized {n m} (circuit : Circuit signature n m) where
  output : Circuit signature n m
  path : Path (relators := relators) circuit output
  stopped : ∀ {target}, Step relators output target → False

def normalizeWithin (strategy : Strategy relators) : (bound : Nat) → {n m : Port signature} →
    (circuit : Circuit signature n m) → strategy.rank circuit < bound → Normalized (relators := relators) circuit
  | 0, _, _, _, below => False.elim (Nat.not_lt_zero _ below)
  | fuel + 1, _, _, circuit, below =>
      match strategy.select circuit with
      | .done stopped => ⟨circuit, .refl circuit, stopped⟩
      | .more (target := target) change =>
          let tail := normalizeWithin strategy fuel target
            (lt_of_lt_of_le (strategy.decreases change) (Nat.le_of_lt_succ below))
          ⟨tail.output, .cons change tail.path, tail.stopped⟩

def normalize (strategy : Strategy relators) {n m} (circuit : Circuit signature n m) : Normalized (relators := relators) circuit :=
  normalizeWithin strategy (strategy.rank circuit + 1) circuit (Nat.lt_succ_self _)

/-- Residual routes are bounded by a caller-selected finite guard set. -/
structure GuardedJoin {n m} (first second : Circuit signature n m) (needed : Finset Requirement) where
  output : Circuit signature n m
  left : Path (relators := relators) first output
  right : Path (relators := relators) second output
  leftCovered : Path.support left ⊆ needed
  rightCovered : Path.support right ⊆ needed

/-- No path enumeration: recursively resolve the actual first steps, then
join their residual routes below the strictly smaller source rank. -/
def joinBounded (strategy : Strategy relators) (rigid : RootRigid relators) (needed : Finset Requirement) :
    {n m : Port signature} → {a b c : Circuit signature n m} →
    (first : Path (relators := relators) a b) → (second : Path (relators := relators) a c) →
    Path.support first ⊆ needed → Path.support second ⊆ needed → GuardedJoin (relators := relators) b c needed
  | _, _, _, _, c, .refl _, second, _, covered =>
      ⟨c, second, .refl c, covered, second.boundaries.2.trans covered⟩
  | _, _, _, b, _, first, .refl _, covered, _ =>
      ⟨b, .refl b, first, first.boundaries.2.trans covered, covered⟩
  | _, _, _, _, _, .cons s first, .cons t second, firstCovered, secondCovered =>
      let branch := s.localJoin rigid t
      let sCovered : s.support ⊆ needed := Finset.subset_union_left.trans firstCovered
      let tCovered : t.support ⊆ needed := Finset.subset_union_left.trans secondCovered
      let localCovered := Finset.union_subset sCovered tCovered
      let one := joinBounded strategy rigid needed first branch.afterFirst
        (Finset.subset_union_right.trans firstCovered) (branch.covered.1.trans localCovered)
      let two := joinBounded strategy rigid needed second branch.afterSecond
        (Finset.subset_union_right.trans secondCovered) (branch.covered.2.trans localCovered)
      let three := joinBounded strategy rigid needed one.right two.right one.rightCovered two.rightCovered
      ⟨three.output, one.left.comp three.left, two.left.comp three.right,
        by rw [Path.comp_support]; exact Finset.union_subset one.leftCovered three.leftCovered,
        by rw [Path.comp_support]; exact Finset.union_subset two.leftCovered three.rightCovered⟩
termination_by _ _ a _ _ _ _ _ _ => strategy.rank a
decreasing_by
  · exact strategy.decreases s
  · exact strategy.decreases t
  · exact lt_of_le_of_lt (Path.rank_le strategy (s.localJoin rigid t).afterFirst) (strategy.decreases s)

def joinPaths (strategy : Strategy relators) (rigid : RootRigid relators) {n m} {a b c : Circuit signature n m}
    (first : Path (relators := relators) a b) (second : Path (relators := relators) a c) :
    GuardedJoin (relators := relators) b c (Path.support first ∪ Path.support second) :=
  joinBounded strategy rigid _ first second Finset.subset_union_left Finset.subset_union_right

/-- Any two irreducible endpoints reachable from the same typed circuit
are equal as syntax, not only equal in a chosen probabilistic model. -/
theorem terminal_unique (strategy : Strategy relators) (rigid : RootRigid relators) {n m} {a b c : Circuit signature n m}
    (first : Path (relators := relators) a b) (second : Path (relators := relators) a c)
    (one : ∀ {target}, Step relators b target → False) (two : ∀ {target}, Step relators c target → False) : b = c := by
  let joined := joinPaths strategy rigid first second
  exact (joined.left.terminal one).trans (joined.right.terminal two).symm

theorem normal_reachable (strategy : Strategy relators) (rigid : RootRigid relators) {n m} {a b : Circuit signature n m}
    (path : Path (relators := relators) a b) :
    (normalize strategy a).output = (normalize strategy b).output :=
  terminal_unique strategy rigid (normalize strategy a).path (path.comp (normalize strategy b).path)
    (normalize strategy a).stopped (normalize strategy b).stopped

/-- Repaired residual routes compare complete input-indexed kernels. All
interior conditions are included by the bounded-join result. -/
theorem GuardedJoin.repaired {old updated : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : CheckedModel relators updated Value) {n m} {a b : Circuit signature n m} {needed : Finset Requirement}
    (joined : GuardedJoin (relators := relators) a b needed) (changed : Finset Requirement)
    (cached : Holds old needed) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh needed changed)) :
    ∃ left : Holds updated a.needs, ∃ right : Holds updated b.needs,
      ∀ input, evaluate model.base a left input = evaluate model.base b right input := by
  let valid := repair cached unchanged rechecked
  let leftGuard := valid.restrict joined.leftCovered
  let rightGuard := valid.restrict joined.rightCovered
  refine ⟨leftGuard.restrict joined.left.boundaries.1, rightGuard.restrict joined.right.boundaries.1, ?_⟩
  intro input
  exact (joined.left.sound model leftGuard _ (leftGuard.restrict joined.left.boundaries.2) input).trans
    (joined.right.sound model rightGuard _ (leftGuard.restrict joined.left.boundaries.2) input).symm

end CryptoLogic.Polygraph.MixedCircuit
