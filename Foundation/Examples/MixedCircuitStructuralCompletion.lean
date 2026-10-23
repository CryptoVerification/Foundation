import Foundation.Examples.MixedCircuitStructuralFork
import Foundation.Crypto.Logic.Polygraph.MixedCircuitPresentedHigher

/-! The suffix completion is a derived equality-preserving proof rewrite.
Its expansion reverses association of proof syntax, never stochastic execution.
A single parameterized definition diagram fills the exhibited mixed peak;
no global confluence or completeness claim is made. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

def tailCrypto (completed : Bool) (stage : Nat) {target} (tail : Circuit signature finish target) :
    Step (@rules completed) (.seq (before stage) tail) (.seq (after stage) tail) :=
  .seqLeft (.root (.rule (relators := @rules completed) (Rule.crypto stage))) tail

def tailAssoc (completed : Bool) (stage : Nat) {target} (tail : Circuit signature finish target) :
    Step (@rules completed) (.seq (before stage) tail)
      (.seq (.box (MACNormalization.Atom.schedule stage))
        (.seq (.box (MACNormalization.Atom.eliminate stage)) tail)) :=
  .root (.rule (relators := @rules completed) (Rule.assoc _ _ _))

def tailSuffix (stage : Nat) {target} (tail : Circuit signature finish target) :
    Step (@rules true)
      (.seq (.box (MACNormalization.Atom.schedule stage))
        (.seq (.box (MACNormalization.Atom.eliminate stage)) tail)) (.seq (after stage) tail) :=
  .root (.rule (relators := @rules true) (Rule.suffix rfl stage tail))

/-- Eliminate every new root rule using only the uncompleted catalogue. -/
def expandPrimitive {a b} {p q : Circuit signature a b}
    (change : Primitive (@rules true) p q) : RewriteTrack (relators := @rules false) p q := by
  cases change with
  | rule label =>
      cases label with
      | crypto stage => exact .step (.root (.rule (Rule.crypto stage)))
      | assoc p q r => exact .step (.root (.rule (Rule.assoc p q r)))
      | wire change => exact .step (.root (.rule (Rule.wire change)))
      | fuseSeq p q => exact .step (.root (.rule (Rule.fuseSeq p q)))
      | fuseTensor p q => exact .step (.root (.rule (Rule.fuseTensor p q)))
      | suffix enabled stage tail =>
          exact .comp (.inv (.step (tailAssoc false stage tail))) (.step (tailCrypto false stage tail))

def expandStep : {a b : Port signature} → {p q : Circuit signature a b} →
    Step (@rules true) p q → RewriteTrack (relators := @rules false) p q
  | _, _, _, _, .root change => expandPrimitive change
  | _, _, _, _, .seqLeft change fixed => (Placement.seqLeft fixed).track (expandStep change)
  | _, _, _, _, .seqRight fixed change => (Placement.seqRight fixed).track (expandStep change)
  | _, _, _, _, .tensorLeft change fixed => (Placement.tensorLeft fixed).track (expandStep change)
  | _, _, _, _, .tensorRight fixed change => (Placement.tensorRight fixed).track (expandStep change)

def expandTrack {a b : Port signature} : {p q : Circuit signature a b} →
    RewriteTrack (relators := @rules true) p q → RewriteTrack (relators := @rules false) p q
  | _, _, .refl p => .refl p
  | _, _, .step change => expandStep change
  | _, _, .comp first second => .comp (expandTrack first) (expandTrack second)
  | _, _, .inv child => .inv (expandTrack child)

theorem expandPrimitive_support {a b} {p q : Circuit signature a b}
    (change : Primitive (@rules true) p q) :
    RewriteTrack.support (expandPrimitive change) = change.support := by
  cases change with
  | rule label =>
      cases label <;>
        simp [expandPrimitive, tailAssoc, tailCrypto, RewriteTrack.support, Step.support,
          Primitive.support, Relator.support, rules, MAC.relators, before, after,
          Circuit.needs, signature, MACNormalization.layout, Finset.union_assoc,
          Finset.union_comm, Finset.insert_comm]

theorem expandStep_support {a b} {p q : Circuit signature a b}
    (change : Step (@rules true) p q) :
    RewriteTrack.support (expandStep change) = change.support := by
  induction change with
  | root change => exact expandPrimitive_support change
  | seqLeft change fixed ih | seqRight fixed change ih | tensorLeft change fixed ih | tensorRight fixed change ih =>
      simp only [expandStep, Placement.track_support, ih, Placement.needs, Step.support] <;>
        exact Finset.union_comm _ _

theorem expandTrack_support {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := @rules true) p q) :
    RewriteTrack.support (expandTrack path) = RewriteTrack.support path := by
  induction path with
  | refl => rfl
  | step change => exact expandStep_support change
  | comp first second one two => simp only [expandTrack, RewriteTrack.support, one, two]
  | inv child ih => exact ih

/-- Any checked interpretation of the old catalogue extends to the completed
catalogue. Thus the completion adds no independent semantic assumption. -/
noncomputable def extendModel {condition : Nat → Prop} {Value : signature.PortAtom → Type}
    (checked : CheckedModel (@rules false) condition Value) : CheckedModel (@rules true) condition Value where
  base := checked.base
  localSound := by
    intro label valid input
    let change := Primitive.rule (relators := @rules true) label
    have expanded : Holds condition (RewriteTrack.support (expandPrimitive change)) := by
      rw [expandPrimitive_support]
      exact valid
    exact RewriteTrack.sound checked (expandPrimitive change) expanded _ _ input

/-- One definition schema, parameterized by the actual typed continuation.
It is not a generator for arbitrary parallel proof paths. -/
inductive Definition : {a b : Port signature} → {p q : Circuit signature a b} →
    RewriteTrack (relators := @rules true) p q → RewriteTrack (relators := @rules true) p q → Type where
  | suffix (stage : Nat) {target} (tail : Circuit signature finish target) :
      Definition (.step (tailSuffix stage tail))
        (.comp (.inv (.step (tailAssoc true stage tail))) (.step (tailCrypto true stage tail)))

theorem definition_expands {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := @rules true) p q} (generator : Definition first second) :
    expandTrack first = expandTrack second := by
  cases generator
  rfl

def completionBasis : HigherBasis (@rules true) where
  Generator := Definition
  requirements := fun generator => match generator with
    | .suffix stage tail => (tailSuffix stage tail).support
  covered := by
    intro a b p q first second generator
    cases generator with
    | suffix stage tail =>
        simp [tailSuffix, tailAssoc, tailCrypto, RewriteTrack.support, Step.support,
          Primitive.support, Relator.support, rules, MAC.relators, before, after,
          Circuit.needs, signature, MACNormalization.layout, Finset.mem_insert]

abbrev CompletionCell {a b} {p q : Circuit signature a b}
    (first second : RewriteTrack (relators := @rules true) p q) := PresentedCell completionBasis first second

/-- The real association/MAC critical square is derived from the definition
schema and the proof-groupoid laws, with no normalization oracle. -/
def criticalCell (stage : Nat) {target} (tail : Circuit signature finish target) :
    CompletionCell (.comp (.step (tailAssoc true stage tail)) (.step (tailSuffix stage tail)))
      (.step (tailCrypto true stage tail)) :=
  (Four.comp (.refl _) (.generator (Definition.suffix stage tail))).trans
    ((Four.assoc _ _ _).symm.trans
      ((Four.comp (Four.rightInv _) (.refl _)).trans (Four.leftUnit _)))

theorem criticalCell_constructorCount (stage : Nat) {target} (tail : Circuit signature finish target) :
    PresentedCell.constructorCount (criticalCell stage tail) = 12 := by
  rfl

/-- The completion square retains precisely the two local MAC conditions
and all conditions of the actual continuation, including proof-internal uses. -/
theorem criticalCell_support (stage : Nat) {target} (tail : Circuit signature finish target) :
    PresentedCell.support (criticalCell stage tail) = {stage, stage + 1} ∪ tail.needs := by
  simp [criticalCell, PresentedCell.support, completionBasis, tailAssoc, tailSuffix, tailCrypto,
    RewriteTrack.support, Step.support, Primitive.support, Relator.support, rules, MAC.relators,
    before, after, Circuit.needs, signature, MACNormalization.layout,
    Finset.union_comm, Finset.insert_comm]

theorem criticalCell_fresh (stage : Nat) {target} (tail : Circuit signature finish target)
    (changed : Finset Nat) :
    fresh (PresentedCell.support (criticalCell stage tail)) changed =
      fresh {stage, stage + 1} changed ∪ fresh tail.needs changed := by
  rw [criticalCell_support]
  exact Finset.union_inter_distrib_right _ _ _

/-- Repair needs only changed conditions in the explicitly recorded footprint.
The updated old-catalogue model suffices, by conservative extension above. -/
theorem criticalCell_repaired {old updated : Nat → Prop} {Value : signature.PortAtom → Type}
    (checked : CheckedModel (@rules false) updated Value) (stage : Nat) {target}
    (tail : Circuit signature finish target) (changed : Finset Nat)
    (cached : Holds old ({stage, stage + 1} ∪ tail.needs))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh ({stage, stage + 1} ∪ tail.needs) changed)) :
    ∃ left : Holds updated (Circuit.seq (before stage) tail).needs,
    ∃ right : Holds updated (Circuit.seq (after stage) tail).needs,
      ∀ input, evaluate checked.base (.seq (before stage) tail) left input =
        evaluate checked.base (.seq (after stage) tail) right input := by
  have cached' : Holds old (PresentedCell.support (criticalCell stage tail)) := by
    rw [criticalCell_support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support (criticalCell stage tail)) changed) := by
    rw [criticalCell_support]; exact rechecked
  exact ((criticalCell stage tail).repaired (extendModel checked) changed cached' unchanged rechecked').2.2

theorem copy_naive_unjoinable (stage : Nat) :
    ¬ Nonempty (Σ destination, Path (relators := @rules false) (forkDirect stage copy) destination ×
      Path (relators := @rules false) (forkAssociated stage copy) destination) :=
  naive_unjoinable stage copy rfl

theorem discard_naive_unjoinable (stage : Nat) :
    ¬ Nonempty (Σ destination, Path (relators := @rules false) (forkDirect stage drop) destination ×
      Path (relators := @rules false) (forkAssociated stage drop) destination) :=
  naive_unjoinable stage drop rfl

/-- info: (2, 2) -/
#guard_msgs in
#eval ((PresentedCell.support (criticalCell 0 (.wire copy))).card,
  (PresentedCell.support (criticalCell 0 (.wire (.discard finish)))).card)

/-- info: true -/
#guard_msgs in
#eval decide (RewriteTrack.support (expandStep (tailSuffix 0 (.wire copy))) =
  (tailSuffix 0 (.wire copy)).support)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
