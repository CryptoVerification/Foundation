import Foundation.Examples.MixedCircuitUnifiedAssociationBasis

/-! Actual contraction and suffix/association squares in the unified basis.
The wire-suffix square is derived from its existing defining square,
association naturality and pentagon; no wire-suffix/association root is added. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Association
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Overlap
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def cryptoCritical (stage : Nat) {target} (tail : Circuit signature finish target) :
    Cell (two (associate (.box (MACNormalization.Atom.schedule stage)) (.box (MACNormalization.Atom.eliminate stage)) tail) (cryptoSuffix stage tail)) (.step (.seqLeft (crypto stage) tail)) :=
  fromStructural (Structural.reuseCompletion (Structural.criticalCell stage tail))

def fusionCritical {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    Cell (two (associate (.wire p) (.wire q) tail) (suffixStep p q tail)) (.step (.seqLeft (seqFusion p q) tail)) :=
  fromFusion (Structural.Fusion.criticalCell p q tail)

def pentagon {a b c d e} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d) (s : Circuit signature d e) :
    Cell (two (associate (.seq p q) r s) (associate p q (.seq r s)))
      (.comp (.step (.seqLeft (associate p q r) s)) (two (associate p (.seq q r) s) (.seqRight p (associate q r s)))) :=
  fromStructural (Structural.LocalDiagram.pentagon p q r s).cell

def cryptoSuffixAssoc (stage : Nat) {a b} (tail : Circuit signature finish a) (rest : Circuit signature a b) :
    Cell (two (.seqLeft (cryptoSuffix stage tail) rest) (associate (after stage) tail rest))
      (.comp (.step (associate (.box (MACNormalization.Atom.schedule stage)) (.seq (.box (MACNormalization.Atom.eliminate stage)) tail) rest))
        (two (.seqRight (.box (MACNormalization.Atom.schedule stage)) (associate (.box (MACNormalization.Atom.eliminate stage)) tail rest)) (cryptoSuffix stage (.seq tail rest)))) :=
  fromStructural (Structural.suffixAssocCell stage tail rest)

def fusionDefinition {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    Cell (.step (suffixStep p q tail))
      (.comp (.inv (.step (associate (.wire p) (.wire q) tail))) (.step (.seqLeft (seqFusion p q) tail))) :=
  fromFusion (.generator (.root (.definition p q tail)))

theorem fusionDefinition_support {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    PresentedCell.support (fusionDefinition p q tail) = tail.needs := by
  rw [fusionDefinition, fromFusion_support]
  rfl

def wireSuffixAssoc {a b c d e} (p : Wiring signature a b) (q : Wiring signature b c)
    (tail : Circuit signature c d) (rest : Circuit signature d e) :
    Cell (two (.seqLeft (suffixStep p q tail) rest) (associate (.wire (.seq p q)) tail rest))
      (.comp (.step (associate (.wire p) (.seq (.wire q) tail) rest))
        (two (.seqRight (.wire p) (associate (.wire q) tail rest)) (suffixStep p q (.seq tail rest)))) := by
  let s := Circuit.wire p
  let t := Circuit.wire q
  let first := Track.step (associate (.seq s t) tail rest)
  let second := Track.step (associate s t (.seq tail rest))
  let leftAssocPath := Track.step (Step.seqLeft (associate s t tail) rest)
  let other := Track.comp (.step (associate s (.seq t tail) rest)) (.step (.seqRight s (associate t tail rest)))
  let contracted := Track.step (Step.seqLeft (seqFusion p q) (.seq tail rest))
  let leftContracted := Track.step (Step.seqLeft (Step.seqLeft (seqFusion p q) tail) rest)
  let last := Track.step (associate (.wire (.seq p q)) tail rest)
  let definition := (fusionDefinition p q tail).whisker (Placement.seqLeft rest)
  let naturality := fromStructural (Structural.LocalDiagram.assocLeft (Structural.seqFusion p q) tail rest).cell
  let square := pentagon s t tail rest
  let rotated : Cell (.comp (.inv leftAssocPath) first) (.comp other (.inv second)) := Four.rotate first second leftAssocPath other square
  exact (Four.comp definition (.refl last)).trans
    ((Four.assoc (.inv leftAssocPath) leftContracted last).trans
      ((Four.comp (.refl (.inv leftAssocPath)) naturality).trans
        ((Four.assoc (.inv leftAssocPath) first contracted).symm.trans
          ((Four.comp rotated (.refl contracted)).trans
            ((Four.assoc other (.inv second) contracted).trans
              ((Four.comp (.refl other) (fusionDefinition p q (.seq tail rest)).symm).trans (Four.assoc _ _ _)))))))

theorem fusionDefinition_count {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    PresentedCell.constructorCount (fusionDefinition p q tail) = 1 := by
  rw [fusionDefinition, fromFusion_count]
  rfl

theorem pentagon_count {a b c d e} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d) (s : Circuit signature d e) :
    PresentedCell.constructorCount (pentagon p q r s) = 1 := by
  rw [pentagon, fromStructural_count]
  rfl

theorem cryptoCritical_support (stage : Nat) {target} (tail : Circuit signature finish target) :
    PresentedCell.support (cryptoCritical stage tail) = {stage, stage + 1} ∪ tail.needs := by
  rw [cryptoCritical, fromStructural_support, Structural.reuseCompletion_support, Structural.criticalCell_support]

theorem fusionCritical_support {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    PresentedCell.support (fusionCritical p q tail) = tail.needs := by
  rw [fusionCritical, fromFusion_support, Structural.Fusion.criticalCell_support]

theorem pentagon_support {a b c d e} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d) (s : Circuit signature d e) :
    PresentedCell.support (pentagon p q r s) = p.needs ∪ q.needs ∪ r.needs ∪ s.needs := by
  rw [pentagon, fromStructural_support, Structural.pentagon_support]

theorem cryptoSuffixAssoc_support (stage : Nat) {a b} (tail : Circuit signature finish a) (rest : Circuit signature a b) :
    PresentedCell.support (cryptoSuffixAssoc stage tail rest) = ({stage, stage + 1} ∪ tail.needs) ∪ rest.needs := by
  rw [cryptoSuffixAssoc, fromStructural_support, Structural.suffixAssocCell_support]

theorem seqFusion_support {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    (seqFusion p q).support = ∅ := by
  simp [seqFusion, Stateful.WiringUnion.embedStep, Step.support, Primitive.support, Relator.support,
    UnionRules, Stateful.WiringUnion.rules, Structural.Fusion.rules, Structural.rules, Circuit.needs]

theorem suffixStep_support {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    (suffixStep p q tail).support = tail.needs := by
  simp [suffixStep, suffixPrimitive, Step.support, Primitive.support, Relator.support,
    UnionRules, Stateful.WiringUnion.rules, Structural.Fusion.rules, Circuit.needs]

theorem structuralSeqFusion_support {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    (Structural.seqFusion p q).support = ∅ := by
  simp [Structural.seqFusion, Step.support, Primitive.support, Relator.support, Structural.rules, Circuit.needs]

theorem wireSuffixAssoc_support {a b c d e} (p : Wiring signature a b) (q : Wiring signature b c)
    (tail : Circuit signature c d) (rest : Circuit signature d e) :
    PresentedCell.support (wireSuffixAssoc p q tail rest) = tail.needs ∪ rest.needs := by
  simp only [wireSuffixAssoc, Four.rotate, Four.divideRight, Four.stripLeft, PresentedCell.support,
    PresentedCell.whisker_support, fusionDefinition_support, fromStructural_support, Structural.assocLeft_support,
    structuralSeqFusion_support, pentagon_support, two, RewriteTrack.support, Placement.needs,
    associate_support, seqFusion_support, suffixStep_support, Step.support, Circuit.needs,
    Finset.empty_union, Finset.union_empty]
  ext label
  simp only [Finset.mem_union]
  tauto

theorem cryptoCritical_count (stage : Nat) {target} (tail : Circuit signature finish target) :
    PresentedCell.constructorCount (cryptoCritical stage tail) = 12 := by
  rw [cryptoCritical, fromStructural_count, Structural.reuseCompletion_constructorCount, Structural.criticalCell_constructorCount]

theorem fusionCritical_count {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    PresentedCell.constructorCount (fusionCritical p q tail) = 12 := by
  rw [fusionCritical, fromFusion_count, Structural.Fusion.criticalCell_constructorCount]

theorem cryptoSuffixAssoc_count (stage : Nat) {a b} (tail : Circuit signature finish a) (rest : Circuit signature a b) :
    PresentedCell.constructorCount (cryptoSuffixAssoc stage tail rest) = 51 := by
  rw [cryptoSuffixAssoc, fromStructural_count, Structural.suffixAssocCell_constructorCount]

theorem wireSuffixAssoc_count {a b c d e} (p : Wiring signature a b) (q : Wiring signature b c)
    (tail : Circuit signature c d) (rest : Circuit signature d e) :
    PresentedCell.constructorCount (wireSuffixAssoc p q tail rest) = 51 := by
  simp only [wireSuffixAssoc, Four.rotate, Four.divideRight, Four.stripLeft,
    PresentedCell.constructorCount, PresentedCell.whisker_constructorCount,
    fromStructural_count, fusionDefinition_count, pentagon_count, Structural.LocalDiagram.cell]

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Association
