import Foundation.Examples.MixedCircuitUnifiedAssociationResolution

/-! Exact guard accounting and bounded higher syntax for the root-specific
association resolver. Costs exclude circuit/context payload and are not
native runtime or common shared-proof certificate-size bounds. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Association
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Overlap
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000


theorem firstNaturality_support {a b c d} {p p' : Circuit signature a b} (change : Step UnionRules p p')
    (q : Circuit signature b c) (r : Circuit signature c d) :
    PresentedCell.support (firstNaturality change q r) = change.support ∪ q.needs ∪ r.needs := by
  simp only [firstNaturality, PresentedCell.support, basis, contextualBasis, ContextualGenerator.support,
    baseBasis, two, RewriteTrack.support, Step.support, associate_support, Circuit.needs]
  ext label
  have one : label ∈ p.needs → label ∈ change.support := fun member => change.boundaries.1 member
  have two : label ∈ p'.needs → label ∈ change.support := fun member => change.boundaries.2 member
  simp only [Finset.mem_union]
  tauto

theorem middleNaturality_support {a b c d} (p : Circuit signature a b) {q q' : Circuit signature b c}
    (change : Step UnionRules q q') (r : Circuit signature c d) :
    PresentedCell.support (middleNaturality p change r) = p.needs ∪ change.support ∪ r.needs := by
  simp only [middleNaturality, PresentedCell.support, basis, contextualBasis, ContextualGenerator.support,
    baseBasis, two, RewriteTrack.support, Step.support, associate_support]
  ext label
  have one : label ∈ q.needs → label ∈ change.support := fun member => change.boundaries.1 member
  have two : label ∈ q'.needs → label ∈ change.support := fun member => change.boundaries.2 member
  simp only [Finset.mem_union]
  tauto

theorem lastNaturality_support {a b c d} (p : Circuit signature a b) (q : Circuit signature b c)
    {r r' : Circuit signature c d} (change : Step UnionRules r r') :
    PresentedCell.support (lastNaturality p q change) = p.needs ∪ q.needs ∪ change.support := by
  simp only [lastNaturality, PresentedCell.support, basis, contextualBasis, ContextualGenerator.support,
    baseBasis, two, RewriteTrack.support, Step.support, associate_support, Circuit.needs]
  ext label
  have one : label ∈ r.needs → label ∈ change.support := fun member => change.boundaries.1 member
  have two : label ∈ r'.needs → label ∈ change.support := fun member => change.boundaries.2 member
  simp only [Finset.mem_union]
  tauto

theorem resolveCase_count {a b c d} {p : Circuit signature a b} {q : Circuit signature b c} {r : Circuit signature c d} {target}
    {change : Step UnionRules (.seq (.seq p q) r) target} (view : AssocCase p q r change) :
    PresentedCell.constructorCount (resolveCase view).comparison ≤ 52 := by
  cases view <;> simp only [resolveCase, PresentedCell.constructorCount, cryptoCritical_count,
    fusionCritical_count, cryptoSuffixAssoc_count, wireSuffixAssoc_count, pentagon, firstNaturality,
    middleNaturality, lastNaturality, fromStructural_count, Structural.LocalDiagram.cell,
    PresentedCell.constructorCount] <;> omega


theorem crypto_support (stage : Nat) : (crypto stage).support = {stage, stage + 1} := by
  simp [crypto, oldStep, oldPrimitive, Step.support, Primitive.support, Relator.support,
    UnionRules, Stateful.WiringUnion.rules, Structural.Fusion.rules, Structural.rules,
    before, after, Circuit.needs, signature, MACNormalization.layout, MAC.relators, Finset.union_comm]

theorem cryptoSuffix_support (stage : Nat) {a} (tail : Circuit signature finish a) :
    (cryptoSuffix stage tail).support = {stage, stage + 1} ∪ tail.needs := by
  simp [cryptoSuffix, oldStep, oldPrimitive, Step.support, Primitive.support, Relator.support,
    UnionRules, Stateful.WiringUnion.rules, Structural.Fusion.rules, Structural.rules,
    after, Circuit.needs, signature, MACNormalization.layout, Finset.union_comm]

theorem schedule_needs (stage : Nat) : signature.needs (MACNormalization.Atom.schedule stage) = ∅ := rfl

theorem eliminate_needs (stage : Nat) : signature.needs (MACNormalization.Atom.eliminate stage) = {stage} := rfl

theorem resolveCase_support {a b c d} {p : Circuit signature a b} {q : Circuit signature b c}
    {r : Circuit signature c d} {target} {change : Step UnionRules (.seq (.seq p q) r) target}
    (view : AssocCase p q r change) :
    PresentedCell.support (resolveCase view).comparison = (associate p q r).support ∪ change.support := by
  have covered : (associate p q r).support ⊆ change.support := by
    rw [associate_support]
    exact change.boundaries.1
  cases view <;> simp only [resolveCase, PresentedCell.support, TwoForward.track, RewriteTrack.support,
    associate_support, cryptoCritical_support, fusionCritical_support, pentagon_support,
    cryptoSuffixAssoc_support, wireSuffixAssoc_support, firstNaturality_support,
    middleNaturality_support, lastNaturality_support, Step.support,
    crypto_support, cryptoSuffix_support, seqFusion_support, suffixStep_support,
    Circuit.needs, schedule_needs, eliminate_needs, Finset.union_empty, Finset.empty_union]
  all_goals ext label
  all_goals have use := @covered label
  all_goals simp only [associate_support, Step.support, Circuit.needs, schedule_needs, eliminate_needs, Finset.mem_union] at use
  all_goals simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  all_goals tauto


theorem resolve_support {a b c d} (p : Circuit signature a b) (q : Circuit signature b c)
    (r : Circuit signature c d) {target} (change : Step UnionRules (.seq (.seq p q) r) target) :
    PresentedCell.support (resolve p q r change).comparison = (associate p q r).support ∪ change.support :=
  resolveCase_support _

theorem resolve_context_support {a b c d x y} (p : Circuit signature a b) (q : Circuit signature b c)
    (r : Circuit signature c d) {target} (change : Step UnionRules (.seq (.seq p q) r) target)
    (place : Placement (signature := signature) a d x y) :
    PresentedCell.support ((resolve p q r change).comparison.whisker place) =
      ((associate p q r).support ∪ change.support) ∪ place.needs := by
  rw [PresentedCell.whisker_support, resolve_support]

theorem resolve_context_count {a b c d x y} (p : Circuit signature a b) (q : Circuit signature b c)
    (r : Circuit signature c d) {target} (change : Step UnionRules (.seq (.seq p q) r) target)
    (place : Placement (signature := signature) a d x y) :
    PresentedCell.constructorCount ((resolve p q r change).comparison.whisker place) ≤ 52 := by
  rw [PresentedCell.whisker_constructorCount]
  exact resolveCase_count _

/-- Endpoint equality in the updated stateful model. This does not compare
emitted programs or elapsed runtime across distinct implementations. -/
theorem resolve_repaired_joint {State Context : Type} {old updated : Nat → Prop}
    {Value : signature.PortAtom → Type} (model : Stateful.CheckedModel MAC.relators updated Value State)
    {a b c d x y} (p : Circuit signature a b) (q : Circuit signature b c)
    (r : Circuit signature c d) {target} (change : Step UnionRules (.seq (.seq p q) r) target)
    (place : Placement (signature := signature) a d x y) (changed : Finset Nat)
    (cached : Holds old (((associate p q r).support ∪ change.support) ∪ place.needs))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (((associate p q r).support ∪ change.support) ∪ place.needs) changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value x))) :
    ∃ before : Holds updated (place.apply (.seq (.seq p q) r)).needs,
    ∃ after : Holds updated (place.apply (resolve p q r change).target).needs,
      law.bind (fun past => (Stateful.evaluate model.base (place.apply (.seq (.seq p q) r)) before past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (Stateful.evaluate model.base (place.apply (resolve p q r change).target) after past.2.1 past.2.2).map (fun next => (past, next))) := by
  have cached' : Holds old (PresentedCell.support ((resolve p q r change).comparison.whisker place)) := by
    rw [resolve_context_support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support ((resolve p q r change).comparison.whisker place)) changed) := by
    rw [resolve_context_support]; exact rechecked
  exact Stateful.cell_repaired_joint (StatefulWiring.checked model) ((resolve p q r change).comparison.whisker place)
    changed cached' unchanged rechecked' law

/-- info: (2, 1, 52, 0) -/
#guard_msgs in
#eval Id.run do
  let p := Wire.identity finish
  let q := Wire.identity finish
  let tail := Circuit.wire (Wire.identity finish)
  let rest := Circuit.wire (Wire.identity finish)
  let result := resolve (.wire p) (.seq (.wire q) tail) rest (.seqLeft (suffixStep p q tail) rest)
  return (result.afterFirst.steps, result.afterSecond.steps,
    PresentedCell.constructorCount result.comparison, (PresentedCell.support result.comparison).card)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Association
