import Foundation.Examples.MixedCircuitStructuralBranching
import Foundation.Logic.Polygraph.HigherRotation

/-! Derive the association/nested-suffix critical cell from the existing
completion definition, association naturality and pentagon. No new higher
generator is added. Formal rotations concern rewrite proofs only. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

def suffixFirst (stage : Nat) {a b} (tail : Circuit signature finish a) (rest : Circuit signature a b) :=
  two (.seqLeft (tailSuffix stage tail) rest) (associate (after stage) tail rest)

def associateFirst (stage : Nat) {a b} (tail : Circuit signature finish a) (rest : Circuit signature a b) :=
  Track.comp (.step (associate (.box (MACNormalization.Atom.schedule stage))
      (.seq (.box (MACNormalization.Atom.eliminate stage)) tail) rest))
    (two (.seqRight (.box _) (associate (.box (MACNormalization.Atom.eliminate stage)) tail rest))
      (tailSuffix stage (.seq tail rest)))

def suffixAssocCell (stage : Nat) {a b} (tail : Circuit signature finish a) (rest : Circuit signature a b) :
    MixedCell (suffixFirst stage tail rest) (associateFirst stage tail rest) := by
  let s := Circuit.box (signature := signature) (MACNormalization.Atom.schedule stage)
  let e := Circuit.box (signature := signature) (MACNormalization.Atom.eliminate stage)
  let p := Track.step (associate (before stage) tail rest)
  let q := Track.step (tailAssoc true stage (.seq tail rest))
  let r := Track.step (Step.seqLeft (tailAssoc true stage tail) rest)
  let t := Track.comp (.step (associate s (.seq e tail) rest))
    (.step (.seqRight s (associate e tail rest)))
  let contracted := Track.step (tailCrypto true stage (.seq tail rest))
  let leftContracted := Track.step (Step.seqLeft (tailCrypto true stage tail) rest)
  let last := Track.step (associate (after stage) tail rest)
  let definition := (LocalDiagram.definition (Definition.suffix stage tail)).cell.whisker (Placement.seqLeft rest)
  let naturality := (LocalDiagram.assocLeft (Step.root (.rule (Rule.crypto stage))) tail rest).cell
  let pentagon := (LocalDiagram.pentagon s e tail rest).cell
  let rotated : MixedCell (.comp (.inv r) p) (.comp t (.inv q)) := Four.rotate p q r t pentagon
  exact (Four.comp definition (.refl last)).trans
    ((Four.assoc (.inv r) leftContracted last).trans
      ((Four.comp (.refl (.inv r)) naturality).trans
        ((Four.assoc (.inv r) p contracted).symm.trans
          ((Four.comp rotated (.refl contracted)).trans
            ((Four.assoc t (.inv q) contracted).trans
              ((Four.comp (.refl t) (LocalDiagram.definition (Definition.suffix stage (.seq tail rest))).cell.symm).trans
                (Four.assoc _ _ _)))))))

set_option maxHeartbeats 2000000 in
theorem suffixAssocCell_support (stage : Nat) {a b} (tail : Circuit signature finish a) (rest : Circuit signature a b) :
    PresentedCell.support (suffixAssocCell stage tail rest) = ({stage, stage + 1} ∪ tail.needs) ∪ rest.needs := by
  simp [suffixAssocCell, Four.rotate, Four.divideRight, Four.stripLeft, PresentedCell.support,
    PresentedCell.whisker, LocalDiagram.cell, mixedBasis, contextualBasis, ContextualGenerator.support,
    localBasis, two, RewriteTrack.support, Placement.needs,
    associate, tailAssoc, tailSuffix, tailCrypto, Step.support, Primitive.support, Relator.support,
    rules, MAC.relators, before, after, Circuit.needs, signature, MACNormalization.layout,
    Finset.union_assoc, Finset.union_left_comm, Finset.union_comm, Finset.union_left_idem, Finset.insert_comm]

set_option maxHeartbeats 5000000 in
theorem suffixAssocCell_constructorCount (stage : Nat) {a b} (tail : Circuit signature finish a) (rest : Circuit signature a b) :
    PresentedCell.constructorCount (suffixAssocCell stage tail rest) = 51 := by
  rfl

theorem suffixAssocCell_fresh (stage : Nat) {a b} (tail : Circuit signature finish a) (rest : Circuit signature a b)
    (changed : Finset Nat) :
    fresh (PresentedCell.support (suffixAssocCell stage tail rest)) changed =
      (fresh {stage, stage + 1} changed ∪ fresh tail.needs changed) ∪ fresh rest.needs changed := by
  rw [suffixAssocCell_support]
  simp only [fresh, Finset.union_inter_distrib_right]

theorem suffixAssoc_repaired_joint {old updated : Nat → Prop} {Value : signature.PortAtom → Type} {Context : Type}
    (checked : CheckedModel (@rules false) updated Value) (stage : Nat) {a b}
    (tail : Circuit signature finish a) (rest : Circuit signature a b) (changed : Finset Nat)
    (cached : Holds old (({stage, stage + 1} ∪ tail.needs) ∪ rest.needs))
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh (({stage, stage + 1} ∪ tail.needs) ∪ rest.needs) changed))
    (law : PMF (Context × Bundle Value (source (stage + 1)))) :
    ∃ left : Holds updated (Circuit.seq (.seq (.box (MACNormalization.Atom.schedule stage))
      (.seq (.box (MACNormalization.Atom.eliminate stage)) tail)) rest).needs,
    ∃ right : Holds updated (Circuit.seq (after stage) (.seq tail rest)).needs,
      law.bind (fun past => (evaluate checked.base (.seq (.seq (.box (MACNormalization.Atom.schedule stage))
        (.seq (.box (MACNormalization.Atom.eliminate stage)) tail)) rest) left past.2).map (fun next => (past, next))) =
      law.bind (fun past => (evaluate checked.base (.seq (after stage) (.seq tail rest)) right past.2).map (fun next => (past, next))) := by
  have cached' : Holds old (PresentedCell.support (suffixAssocCell stage tail rest)) := by
    rw [suffixAssocCell_support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support (suffixAssocCell stage tail rest)) changed) := by
    rw [suffixAssocCell_support]; exact rechecked
  exact (suffixAssocCell stage tail rest).repaired_joint (extendModel checked) changed cached' unchanged rechecked' law

/-- info: (2, 51) -/
#guard_msgs in
#eval ((PresentedCell.support (suffixAssocCell 0 (.wire (.identity finish)) (.wire copy))).card,
  PresentedCell.constructorCount (suffixAssocCell 0 (.wire (.identity finish)) (.wire copy)))

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
