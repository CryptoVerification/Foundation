import Foundation.Examples.MixedCircuitStructuralDiagrams

/-! Reuse the earlier MAC completion in the explicit contextual presentation.
The examples include untouched MAC components, actual pure-wire rewrites, and
copy/discard placements. Counts exclude boundary and context payloads. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
open Foundation.Logic.Polygraph
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

theorem definition_requirements {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := @rules true) p q} (generator : Definition first second) :
    localBasis.requirements (LocalDiagram.definition generator) = completionBasis.requirements generator := by
  cases generator
  simp [localBasis, completionBasis, tailSuffix, tailAssoc, tailCrypto,
    RewriteTrack.support, Step.support, Primitive.support, Relator.support, rules, MAC.relators,
    before, after, Circuit.needs, signature, MACNormalization.layout, Finset.union_comm,
    Finset.insert_comm]

def reuseCompletion {a b : Port signature} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := @rules true) p q} → CompletionCell first second → MixedCell first second
  | _, _, _, _, .refl p => .refl p
  | _, _, _, _, .generator generator => (LocalDiagram.definition generator).cell
  | _, _, _, _, .symm child => (reuseCompletion child).symm
  | _, _, _, _, .trans first second => (reuseCompletion first).trans (reuseCompletion second)
  | _, _, _, _, .comp first second => .comp (reuseCompletion first) (reuseCompletion second)
  | _, _, _, _, .inverse child => .inverse (reuseCompletion child)
  | _, _, _, _, .assoc p q r => .assoc p q r
  | _, _, _, _, .leftUnit p => .leftUnit p
  | _, _, _, _, .rightUnit p => .rightUnit p
  | _, _, _, _, .leftInv p => .leftInv p
  | _, _, _, _, .rightInv p => .rightInv p

theorem reuseCompletion_support {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := @rules true) p q} (cell : CompletionCell first second) :
    PresentedCell.support (reuseCompletion cell) = PresentedCell.support cell := by
  induction cell <;> simp_all only [reuseCompletion, PresentedCell.support, LocalDiagram.cell,
    mixedBasis, contextualBasis, ContextualGenerator.support, definition_requirements]

theorem reuseCompletion_constructorCount {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := @rules true) p q} (cell : CompletionCell first second) :
    PresentedCell.constructorCount (reuseCompletion cell) = PresentedCell.constructorCount cell := by
  induction cell <;> simp_all only [reuseCompletion, PresentedCell.constructorCount, LocalDiagram.cell]

def contextualCritical (stage : Nat) {target} (tail : Circuit signature finish target)
    {a b} (place : Placement (signature := signature) _ target a b) :=
  (reuseCompletion (criticalCell stage tail)).whisker place

theorem contextualCritical_support (stage : Nat) {target} (tail : Circuit signature finish target)
    {a b} (place : Placement (signature := signature) _ target a b) :
    PresentedCell.support (contextualCritical stage tail place) = ({stage, stage + 1} ∪ tail.needs) ∪ place.needs := by
  rw [contextualCritical, PresentedCell.whisker_support, reuseCompletion_support, criticalCell_support]

theorem contextualCritical_constructorCount (stage : Nat) {target} (tail : Circuit signature finish target)
    {a b} (place : Placement (signature := signature) _ target a b) :
    PresentedCell.constructorCount (contextualCritical stage tail place) = 12 := by
  rw [contextualCritical, PresentedCell.whisker_constructorCount, reuseCompletion_constructorCount,
    criticalCell_constructorCount]

def framedCritical (stage : Nat) :=
  contextualCritical stage (.wire copy) (.tensorRight (before (stage + 2)))

theorem framedCritical_support (stage : Nat) :
    PresentedCell.support (framedCritical stage) = {stage, stage + 1, stage + 2} := by
  simp [framedCritical, contextualCritical_support, Placement.needs, before, Circuit.needs,
    signature, MACNormalization.layout]

theorem framedCritical_fresh (stage : Nat) :
    fresh (PresentedCell.support (framedCritical stage)) {stage + 3} = ∅ := by
  rw [framedCritical_support]
  simp [fresh]

def copiedFramedCritical (stage : Nat) :=
  (framedCritical stage).whisker (.seqLeft (.wire (.copy _)))

def discardedFramedCritical (stage : Nat) :=
  (framedCritical stage).whisker (.seqLeft (.wire (.discard _)))

theorem copiedFramedCritical_support (stage : Nat) :
    PresentedCell.support (copiedFramedCritical stage) = {stage, stage + 1, stage + 2} := by
  simp only [copiedFramedCritical, PresentedCell.whisker_support, framedCritical_support,
    Placement.needs, Circuit.needs, Finset.union_empty]

theorem discardedFramedCritical_support (stage : Nat) :
    PresentedCell.support (discardedFramedCritical stage) = {stage, stage + 1, stage + 2} := by
  simp only [discardedFramedCritical, PresentedCell.whisker_support, framedCritical_support,
    Placement.needs, Circuit.needs, Finset.union_empty]

theorem copiedFramedCritical_constructorCount (stage : Nat) :
    PresentedCell.constructorCount (copiedFramedCritical stage) = 12 := by
  rw [copiedFramedCritical, PresentedCell.whisker_constructorCount, framedCritical,
    contextualCritical_constructorCount]

theorem discardedFramedCritical_constructorCount (stage : Nat) :
    PresentedCell.constructorCount (discardedFramedCritical stage) = 12 := by
  rw [discardedFramedCritical, PresentedCell.whisker_constructorCount, framedCritical,
    contextualCritical_constructorCount]

/-- Reuse remains sound in any updated old-catalogue interpretation; prior
records may be correlated with the full input bundle. -/
theorem contextualCritical_repaired_joint {old updated : Nat → Prop} {Value : signature.PortAtom → Type}
    {Context : Type} (checked : CheckedModel (@rules false) updated Value) (stage : Nat) {target}
    (tail : Circuit signature finish target) {a b} (place : Placement (signature := signature) _ target a b)
    (changed : Finset Nat) (cached : Holds old (({stage, stage + 1} ∪ tail.needs) ∪ place.needs))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (({stage, stage + 1} ∪ tail.needs) ∪ place.needs) changed))
    (law : PMF (Context × Bundle Value a)) :
    ∃ left : Holds updated (place.apply (.seq (before stage) tail)).needs,
    ∃ right : Holds updated (place.apply (.seq (after stage) tail)).needs,
      law.bind (fun past => (evaluate checked.base (place.apply (.seq (before stage) tail)) left past.2).map (fun next => (past, next))) =
        law.bind (fun past => (evaluate checked.base (place.apply (.seq (after stage) tail)) right past.2).map (fun next => (past, next))) := by
  have cached' : Holds old (PresentedCell.support (contextualCritical stage tail place)) := by
    rw [contextualCritical_support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support (contextualCritical stage tail place)) changed) := by
    rw [contextualCritical_support]; exact rechecked
  exact (contextualCritical stage tail place).repaired_joint (extendModel checked) changed cached' unchanged rechecked' law

/-- info: (3, 12, 0) -/
#guard_msgs in
#eval ((PresentedCell.support (framedCritical 0)).card,
  PresentedCell.constructorCount (framedCritical 0),
  (fresh (PresentedCell.support (framedCritical 0)) {3}).card)

/-- info: (6, 0, 1) -/
#guard_msgs in
#eval ((LocalDiagram.seqWireLeft
    (Foundation.Logic.Polygraph.StructuralTransport.Rewrite.Step.root
      (.copySwap finish)) (.identity (.pair finish finish))).code.val,
  (PresentedCell.support (LocalDiagram.seqWireLeft
    (Foundation.Logic.Polygraph.StructuralTransport.Rewrite.Step.root
      (.copySwap finish)) (.identity (.pair finish finish))).cell).card,
  PresentedCell.constructorCount (LocalDiagram.seqWireLeft
    (Foundation.Logic.Polygraph.StructuralTransport.Rewrite.Step.root
      (.copySwap finish)) (.identity (.pair finish finish))).cell)

/-- info: (3, 3, 12, 12) -/
#guard_msgs in
#eval ((PresentedCell.support (copiedFramedCritical 0)).card,
  (PresentedCell.support (discardedFramedCritical 0)).card,
  PresentedCell.constructorCount (copiedFramedCritical 0),
  PresentedCell.constructorCount (discardedFramedCritical 0))

/-- info: (2, 2, 5, 0, 10, 2) -/
#guard_msgs in
#eval Id.run do
  let assocDiagram := LocalDiagram.assocLeft
    (Step.root (.rule (relators := @rules true) (Rule.crypto 0))) (.wire (.identity finish)) (.wire copy)
  let pentagonDiagram := LocalDiagram.pentagon (.wire (.identity finish)) (.wire (.identity finish))
    (.wire (.identity finish)) (.wire (.identity finish))
  let suffixDiagram := LocalDiagram.suffixTail 0
    (wireChange (Foundation.Logic.Polygraph.StructuralTransport.Rewrite.Step.root (.copySwap finish)))
  return (assocDiagram.code.val, (PresentedCell.support assocDiagram.cell).card,
    pentagonDiagram.code.val, (PresentedCell.support pentagonDiagram.cell).card,
    suffixDiagram.code.val, (PresentedCell.support suffixDiagram.cell).card)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
