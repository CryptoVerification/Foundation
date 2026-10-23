import Foundation.Examples.MixedCircuitStructuralCompletion
import Foundation.Crypto.Logic.Polygraph.MixedCircuitContextualHigher

/-! Explicit mixed local diagrams: separated exchange, completion definition,
association naturality and pentagon, pure-wire fusion naturality, suffix
naturality. Eleven parameterized forms, not a complete critical basis. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

def two {a b} {p q r : Circuit signature a b} (first : Step (@rules true) p q) (second : Step (@rules true) q r) :
    RewriteTrack (relators := @rules true) p r := .comp (.step first) (.step second)

def associate {a b c d} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d) :
    Step (@rules true) (.seq (.seq p q) r) (.seq p (.seq q r)) := .root (.rule (Rule.assoc p q r))

def wireChange {a b} {p q : Wiring signature a b} (change : WireEdit p q) :
    Step (@rules true) (.wire p) (.wire q) := .root (.rule (Rule.wire change))

def seqFusion {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    Step (@rules true) (.seq (.wire p) (.wire q)) (.wire (.seq p q)) := .root (.rule (Rule.fuseSeq p q))

def tensorFusion {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) :
    Step (@rules true) (.tensor (.wire p) (.wire q)) (.wire (.tensor p q)) := .root (.rule (Rule.fuseTensor p q))

inductive LocalDiagram : {n m : Port signature} → {a b : Circuit signature n m} →
    RewriteTrack (relators := @rules true) a b → RewriteTrack (relators := @rules true) a b → Type where
  | exchange {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := @rules true) a b}
      (witness : Exchange p q) : LocalDiagram p q
  | definition {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := @rules true) a b}
      (witness : Definition p q) : LocalDiagram p q
  | assocLeft {a b c d} {p p' : Circuit signature a b} (change : Step (@rules true) p p')
      (q : Circuit signature b c) (r : Circuit signature c d) :
      LocalDiagram (two (.seqLeft (.seqLeft change q) r) (associate p' q r))
        (two (associate p q r) (.seqLeft change (.seq q r)))
  | assocMiddle {a b c d} (p : Circuit signature a b) {q q' : Circuit signature b c}
      (change : Step (@rules true) q q') (r : Circuit signature c d) :
      LocalDiagram (two (.seqLeft (.seqRight p change) r) (associate p q' r))
        (two (associate p q r) (.seqRight p (.seqLeft change r)))
  | assocRight {a b c d} (p : Circuit signature a b) (q : Circuit signature b c)
      {r r' : Circuit signature c d} (change : Step (@rules true) r r') :
      LocalDiagram (two (.seqRight (.seq p q) change) (associate p q r'))
        (two (associate p q r) (.seqRight p (.seqRight q change)))
  | pentagon {a b c d e} (p : Circuit signature a b) (q : Circuit signature b c)
      (r : Circuit signature c d) (s : Circuit signature d e) :
      LocalDiagram (two (associate (.seq p q) r s) (associate p q (.seq r s)))
        (.comp (.step (.seqLeft (associate p q r) s))
          (two (associate p (.seq q r) s) (.seqRight p (associate q r s))))
  | seqWireLeft {a b c} {p p' : Wiring signature a b} (change : WireEdit p p') (q : Wiring signature b c) :
      LocalDiagram (two (.seqLeft (wireChange change) (.wire q)) (seqFusion p' q))
        (two (seqFusion p q) (wireChange (.seqLeft change q)))
  | seqWireRight {a b c} (p : Wiring signature a b) {q q' : Wiring signature b c} (change : WireEdit q q') :
      LocalDiagram (two (.seqRight (.wire p) (wireChange change)) (seqFusion p q'))
        (two (seqFusion p q) (wireChange (.seqRight p change)))
  | tensorWireLeft {a b c d} {p p' : Wiring signature a b} (change : WireEdit p p') (q : Wiring signature c d) :
      LocalDiagram (two (.tensorLeft (wireChange change) (.wire q)) (tensorFusion p' q))
        (two (tensorFusion p q) (wireChange (.tensorLeft change q)))
  | tensorWireRight {a b c d} (p : Wiring signature a b) {q q' : Wiring signature c d} (change : WireEdit q q') :
      LocalDiagram (two (.tensorRight (.wire p) (wireChange change)) (tensorFusion p q'))
        (two (tensorFusion p q) (wireChange (.tensorRight p change)))
  | suffixTail (stage : Nat) {target} {tail tail' : Circuit signature finish target}
      (change : Step (@rules true) tail tail') :
      LocalDiagram
        (two (.seqRight (.box _) (.seqRight (.box _) change)) (tailSuffix stage tail'))
        (two (tailSuffix stage tail) (.seqRight (after stage) change))

/-- A tag for the eleven displayed forms, not a coverage classifier for all
critical overlaps or a bound on the number of concrete typed instances. -/
def LocalDiagram.code {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := @rules true) a b}
    (diagram : LocalDiagram p q) : Fin 11 := by
  cases diagram with
  | exchange => exact 0
  | definition => exact 1
  | assocLeft => exact 2
  | assocMiddle => exact 3
  | assocRight => exact 4
  | pentagon => exact 5
  | seqWireLeft => exact 6
  | seqWireRight => exact 7
  | tensorWireLeft => exact 8
  | tensorWireRight => exact 9
  | suffixTail => exact 10

def localBasis : HigherBasis (@rules true) where
  Generator := LocalDiagram
  requirements := fun {_ _ _ _ p q} _ => RewriteTrack.support p ∪ RewriteTrack.support q
  covered := fun _ => ⟨Finset.subset_union_left, Finset.subset_union_right⟩

def mixedBasis : HigherBasis (@rules true) := contextualBasis localBasis

abbrev MixedCell {n m} {a b : Circuit signature n m} (p q : RewriteTrack (relators := @rules true) a b) :=
  PresentedCell mixedBasis p q

def LocalDiagram.cell {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := @rules true) a b}
    (diagram : LocalDiagram p q) : MixedCell p q := .generator (.root diagram)

theorem LocalDiagram.cell_support {n m} {a b : Circuit signature n m} {p q : RewriteTrack (relators := @rules true) a b}
    (diagram : LocalDiagram p q) : PresentedCell.support diagram.cell = RewriteTrack.support p ∪ RewriteTrack.support q := rfl

theorem associate_support {a b c d} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d) :
    (associate p q r).support = p.needs ∪ q.needs ∪ r.needs := by
  simp [associate, Step.support, Primitive.support, Relator.support, rules, Circuit.needs,
    Finset.union_assoc, Finset.union_comm]

set_option maxHeartbeats 1000000 in
theorem assocLeft_support {a b c d} {p p' : Circuit signature a b} (change : Step (@rules true) p p')
    (q : Circuit signature b c) (r : Circuit signature c d) :
    PresentedCell.support (LocalDiagram.assocLeft change q r).cell = change.support ∪ q.needs ∪ r.needs := by
  simp only [LocalDiagram.cell_support, two, RewriteTrack.support, Step.support, associate_support, Circuit.needs]
  ext label
  have one : label ∈ p.needs → label ∈ change.support := fun member => change.boundaries.1 member
  have two : label ∈ p'.needs → label ∈ change.support := fun member => change.boundaries.2 member
  simp only [Finset.mem_union]
  tauto

set_option maxHeartbeats 1000000 in
theorem assocMiddle_support {a b c d} (p : Circuit signature a b) {q q' : Circuit signature b c}
    (change : Step (@rules true) q q') (r : Circuit signature c d) :
    PresentedCell.support (LocalDiagram.assocMiddle p change r).cell = p.needs ∪ change.support ∪ r.needs := by
  simp only [LocalDiagram.cell_support, two, RewriteTrack.support, Step.support, associate_support]
  ext label
  have one : label ∈ q.needs → label ∈ change.support := fun member => change.boundaries.1 member
  have two : label ∈ q'.needs → label ∈ change.support := fun member => change.boundaries.2 member
  simp only [Finset.mem_union]
  tauto

theorem assocRight_support {a b c d} (p : Circuit signature a b) (q : Circuit signature b c)
    {r r' : Circuit signature c d} (change : Step (@rules true) r r') :
    PresentedCell.support (LocalDiagram.assocRight p q change).cell = p.needs ∪ q.needs ∪ change.support := by
  simp only [LocalDiagram.cell_support, two, RewriteTrack.support, Step.support, associate_support, Circuit.needs]
  ext label
  have one : label ∈ r.needs → label ∈ change.support := fun member => change.boundaries.1 member
  have two : label ∈ r'.needs → label ∈ change.support := fun member => change.boundaries.2 member
  simp only [Finset.mem_union]
  tauto

theorem pentagon_support {a b c d e} (p : Circuit signature a b) (q : Circuit signature b c)
    (r : Circuit signature c d) (s : Circuit signature d e) :
    PresentedCell.support (LocalDiagram.pentagon p q r s).cell = p.needs ∪ q.needs ∪ r.needs ∪ s.needs := by
  simp only [LocalDiagram.cell_support, two, RewriteTrack.support, Step.support, associate_support, Circuit.needs]
  ext label
  simp only [Finset.mem_union]
  tauto

theorem seqWireLeft_support {a b c} {p p' : Wiring signature a b} (change : WireEdit p p') (q : Wiring signature b c) :
    PresentedCell.support (LocalDiagram.seqWireLeft change q).cell = ∅ := by
  simp [LocalDiagram.cell_support, two, RewriteTrack.support, Step.support,
    wireChange, seqFusion, Primitive.support, Relator.support, rules, Circuit.needs]

theorem seqWireRight_support {a b c} (p : Wiring signature a b) {q q' : Wiring signature b c} (change : WireEdit q q') :
    PresentedCell.support (LocalDiagram.seqWireRight p change).cell = ∅ := by
  simp [LocalDiagram.cell_support, two, RewriteTrack.support, Step.support,
    wireChange, seqFusion, Primitive.support, Relator.support, rules, Circuit.needs]

theorem tensorWireLeft_support {a b c d} {p p' : Wiring signature a b} (change : WireEdit p p') (q : Wiring signature c d) :
    PresentedCell.support (LocalDiagram.tensorWireLeft change q).cell = ∅ := by
  simp [LocalDiagram.cell_support, two, RewriteTrack.support, Step.support,
    wireChange, tensorFusion, Primitive.support, Relator.support, rules, Circuit.needs]

theorem tensorWireRight_support {a b c d} (p : Wiring signature a b) {q q' : Wiring signature c d} (change : WireEdit q q') :
    PresentedCell.support (LocalDiagram.tensorWireRight p change).cell = ∅ := by
  simp [LocalDiagram.cell_support, two, RewriteTrack.support, Step.support,
    wireChange, tensorFusion, Primitive.support, Relator.support, rules, Circuit.needs]

theorem suffixTail_support (stage : Nat) {target} {tail tail' : Circuit signature finish target}
    (change : Step (@rules true) tail tail') :
    PresentedCell.support (LocalDiagram.suffixTail stage change).cell = {stage, stage + 1} ∪ change.support := by
  simp only [LocalDiagram.cell_support, two, RewriteTrack.support, Step.support]
  simp only [tailSuffix, Step.support, Primitive.support, Relator.support, rules, after,
    Circuit.needs, signature, CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACNormalization.layout]
  ext label
  have one : label ∈ tail.needs → label ∈ change.support := fun member => change.boundaries.1 member
  have two : label ∈ tail'.needs → label ∈ change.support := fun member => change.boundaries.2 member
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false, false_or]
  tauto

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
