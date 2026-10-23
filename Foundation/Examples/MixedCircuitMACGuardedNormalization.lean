import Foundation.Examples.MixedCircuitMACNormalization

/-! A finite static guard envelope for every MAC normalization route, plus
actual nested preparation chains and copy/drop contexts. This envelope is
conservative and does not claim optimal repair cost or structural completeness. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC
open Foundation.Probability
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Foundation.Logic.Polygraph.ScheduleCertificate
set_option backward.isDefEq.respectTransparency false

/-- Include guards that a schedule/elimination contraction may introduce. -/
def footprint : {n m : Port signature} → Circuit signature n m → Finset Nat
  | _, _, .wire _ => ∅
  | _, _, .box (.schedule stage) => {stage, stage + 1}
  | _, _, .box (.eliminate stage) => {stage}
  | _, _, .seq left right => footprint left ∪ footprint right
  | _, _, .tensor left right => footprint left ∪ footprint right

theorem needs_footprint {n m} (circuit : Circuit signature n m) : circuit.needs ⊆ footprint circuit := by
  induction circuit with
  | wire => exact Finset.Subset.refl _
  | box label => cases label <;> simp [Circuit.needs, footprint, signature, MACNormalization.layout]
  | seq left right one two | tensor left right one two => exact Finset.union_subset_union one two

theorem step_footprint {n m} {a b : Circuit signature n m} (change : Step relators a b) :
    footprint b ⊆ footprint a ∧ change.support ⊆ footprint a := by
  induction change with
  | root primitive =>
      cases primitive with
      | rule stage =>
          simp [footprint, Step.support, Primitive.support, Relator.support, relators, before, after,
            Circuit.needs, signature, MACNormalization.layout, Finset.subset_iff, or_comm]
  | seqLeft child fixed ih | tensorLeft child fixed ih =>
      exact ⟨Finset.union_subset_union ih.1 (Finset.Subset.refl _),
        Finset.union_subset_union ih.2 (needs_footprint fixed)⟩
  | seqRight fixed child ih | tensorRight fixed child ih =>
      exact ⟨Finset.union_subset_union (Finset.Subset.refl _) ih.1,
        Finset.union_subset_union (needs_footprint fixed) ih.2⟩

theorem path_footprint {n m} {a b : Circuit signature n m} (path : Path (relators := relators) a b) :
    Path.support path ⊆ footprint a := by
  induction path with
  | refl => exact needs_footprint _
  | cons change tail ih => exact Finset.union_subset (step_footprint change).2 (ih.trans (step_footprint change).1)

/-- The old finite guard cache suffices outside the changed IDs. The model
contract is checked independently; no semantic condition is inferred from IDs. -/
theorem normalized_repaired (old updated : Nat → Schedule 8) {n m} (circuit : Circuit signature n m) (changed : Finset Nat)
    (cached : Holds (MACNormalization.condition old) (footprint circuit))
    (unchanged : ∀ label ∉ changed, old label = updated label)
    (rechecked : Holds (MACNormalization.condition updated) (fresh (footprint circuit) changed)) :
    ∃ left : Holds (MACNormalization.condition updated) circuit.needs,
    ∃ right : Holds (MACNormalization.condition updated) (normalForm circuit).output.needs,
      ∀ input, evaluate (base updated) circuit left input = evaluate (base updated) (normalForm circuit).output right input := by
  let valid := repair cached (fun label outside proof => by
    simpa only [MACNormalization.condition, ← unchanged label outside] using proof) rechecked
  let pathGuard := valid.restrict (path_footprint (normalForm circuit).path)
  refine ⟨pathGuard.restrict (normalForm circuit).path.boundaries.1,
    pathGuard.restrict (normalForm circuit).path.boundaries.2, ?_⟩
  intro input
  exact (normalForm circuit).path.sound (model updated) pathGuard _ _ input

theorem normalized_repaired_joint {Context : Type} (old updated : Nat → Schedule 8) {n m}
    (circuit : Circuit signature n m) (changed : Finset Nat)
    (cached : Holds (MACNormalization.condition old) (footprint circuit))
    (unchanged : ∀ label ∉ changed, old label = updated label)
    (rechecked : Holds (MACNormalization.condition updated) (fresh (footprint circuit) changed))
    (law : PMF (Context × Bundle (family updated) n)) :
    ∃ left : Holds (MACNormalization.condition updated) circuit.needs,
    ∃ right : Holds (MACNormalization.condition updated) (normalForm circuit).output.needs,
      law.bind (fun past => (evaluate (base updated) circuit left past.2).map (fun next => (past, next))) =
        law.bind (fun past => (evaluate (base updated) (normalForm circuit).output right past.2).map (fun next => (past, next))) := by
  let valid := repair cached (fun label outside proof => by
    simpa only [MACNormalization.condition, ← unchanged label outside] using proof) rechecked
  let pathGuard := valid.restrict (path_footprint (normalForm circuit).path)
  exact ⟨pathGuard.restrict (normalForm circuit).path.boundaries.1,
    pathGuard.restrict (normalForm circuit).path.boundaries.2,
    (normalForm circuit).path.sound_joint (model updated) pathGuard _ _ law⟩

/-- Rewriting the inner chain can CREATE the outer redex, so a single
parallel sweep is insufficient. The complete selector handles this case. -/
def chain : (stage : Nat) → Circuit signature (source (stage + 1)) finish
  | 0 => before 0
  | stage + 1 => .seq (.box (signature := signature) (MACNormalization.Atom.schedule (stage + 1))) (chain stage)

def chainPath : (stage : Nat) → Path (relators := relators) (chain stage) (after stage)
  | 0 => RewritePath.single (rewrite 0)
  | stage + 1 =>
      let head : Circuit signature (source (stage + 2)) (source (stage + 1)) :=
        .box (MACNormalization.Atom.schedule (stage + 1))
      ((chainPath stage).map (fun circuit => Circuit.seq head circuit) (fun change => Step.seqRight head change)).comp
        (RewritePath.single (rewrite (stage + 1)))

theorem chain_count (stage : Nat) : boxCount (chain stage) = stage + 2 := by
  induction stage with
  | zero => rfl
  | succ stage ih => simp only [chain, boxCount, ih]; omega

theorem chain_normal (stage : Nat) : (normalForm (chain stage)).output = after stage :=
  terminal_unique normalizationStrategy roots_rigid (normalForm (chain stage)).path (chainPath stage)
    (normalForm (chain stage)).stopped (no_box_step _)

theorem chain_normal_length (stage : Nat) : (normalForm (chain stage)).path.length = stage + 1 := by
  have counted := path_count (normalForm (chain stage)).path
  have beforeCount := chain_count stage
  have afterCount : boxCount (normalForm (chain stage)).output = 1 := by rw [chain_normal]; rfl
  omega

theorem chain_footprint (stage : Nat) : footprint (chain stage) = Finset.range (stage + 2) := by
  induction stage with
  | zero => decide
  | succ stage ih =>
      ext label
      simp only [chain, footprint, ih, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_range]
      omega

/-- info: [(0, 1, 2, 2), (1, 2, 3, 3), (2, 3, 4, 4), (3, 4, 5, 5), (4, 5, 6, 6)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map (fun stage =>
  (stage, (normalForm (chain stage)).path.length, (footprint (chain stage)).card,
    (Path.support (normalForm (chain stage)).path).card))

/-- info: (5, 4, 5, 4) -/
#guard_msgs in
#eval Id.run do
  let pair := Circuit.tensor (chain 2) (chain 1)
  let copied := Circuit.seq pair (Circuit.wire (Foundation.Logic.Polygraph.StructuralTransport.Wire.copy (.pair finish finish)))
  let dropped := Circuit.seq pair (Circuit.wire (Foundation.Logic.Polygraph.StructuralTransport.Wire.discard (.pair finish finish)))
  return ((normalForm copied).path.length, (Path.support (normalForm copied).path).card,
    (normalForm dropped).path.length, (Path.support (normalForm dropped).path).card)

/-- info: (1, 1, 0, 0, 3) -/
#guard_msgs in
#eval Id.run do
  let first := Step.tensorLeft (rewrite 0) (before 1)
  let second := Step.tensorRight (before 0) (rewrite 1)
  let square := (separatedChanges 0).diamond
  let prefixJoin := joinPaths normalizationStrategy roots_rigid (RewritePath.single first) (RewritePath.single second)
  let firstRoute := RewritePath.cons first (RewritePath.single square.afterFirst)
  let secondRoute := RewritePath.cons second (RewritePath.single square.afterSecond)
  let completed := joinPaths normalizationStrategy roots_rigid firstRoute secondRoute
  return (prefixJoin.left.length, prefixJoin.right.length, completed.left.length, completed.right.length,
    (Path.support firstRoute ∪ Path.support secondRoute).card)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC
