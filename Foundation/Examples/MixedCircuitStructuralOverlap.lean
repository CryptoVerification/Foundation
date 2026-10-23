import Foundation.Examples.MixedCircuitStructuralContext

/-! Exhaustive typed views for primitives and competitors of mixed
association. This classifies real rewrite data, not only diagram tags.
Resolution of all resulting cases and pure-wire coherence remain obligations. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

inductive RootView : {a b : Port signature} → {p q : Circuit signature a b} →
    Primitive (@rules true) p q → Type where
  | crypto (stage : Nat) : RootView (.rule (Rule.crypto stage))
  | assoc {a b c d} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d) :
      RootView (.rule (Rule.assoc p q r))
  | wire {a b} {p q : Wiring signature a b} (change : WireEdit p q) : RootView (.rule (Rule.wire change))
  | fuseSeq {a b c} (p : Wiring signature a b) (q : Wiring signature b c) : RootView (.rule (Rule.fuseSeq p q))
  | fuseTensor {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) : RootView (.rule (Rule.fuseTensor p q))
  | suffix (stage : Nat) {target} (tail : Circuit signature finish target) : RootView (.rule (Rule.suffix rfl stage tail))

def rootView {a b} {p q : Circuit signature a b} (primitive : Primitive (@rules true) p q) : RootView primitive := by
  cases primitive with
  | rule label =>
      cases label with
      | crypto stage => exact .crypto stage
      | assoc p q r => exact .assoc p q r
      | wire change => exact .wire change
      | fuseSeq p q => exact .fuseSeq p q
      | fuseTensor p q => exact .fuseTensor p q
      | suffix enabled stage tail => exact .suffix stage tail

inductive AssocCase : {a b c d : Port signature} → (p : Circuit signature a b) →
    (q : Circuit signature b c) → (r : Circuit signature c d) → {target : Circuit signature a d} →
    Step (@rules true) (.seq (.seq p q) r) target → Type where
  | same {a b c d} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d) :
      AssocCase p q r (associate p q r)
  | leftCrypto (stage : Nat) {target} (r : Circuit signature finish target) :
      AssocCase (.box (MACNormalization.Atom.schedule stage)) (.box (MACNormalization.Atom.eliminate stage)) r
        (tailCrypto true stage r)
  | leftAssoc {a b c d e} (p : Circuit signature a b) (q : Circuit signature b c)
      (r : Circuit signature c d) (s : Circuit signature d e) :
      AssocCase (.seq p q) r s (.seqLeft (associate p q r) s)
  | leftFusion {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (r : Circuit signature c d) :
      AssocCase (.wire p) (.wire q) r (.seqLeft (seqFusion p q) r)
  | leftSuffix (stage : Nat) {target output} (tail : Circuit signature finish target) (r : Circuit signature target output) :
      AssocCase (.box (MACNormalization.Atom.schedule stage)) (.seq (.box (MACNormalization.Atom.eliminate stage)) tail) r
        (.seqLeft (tailSuffix stage tail) r)
  | first {a b c d} {p p' : Circuit signature a b} (change : Step (@rules true) p p')
      (q : Circuit signature b c) (r : Circuit signature c d) : AssocCase p q r (.seqLeft (.seqLeft change q) r)
  | middle {a b c d} (p : Circuit signature a b) {q q' : Circuit signature b c}
      (change : Step (@rules true) q q') (r : Circuit signature c d) : AssocCase p q r (.seqLeft (.seqRight p change) r)
  | last {a b c d} (p : Circuit signature a b) (q : Circuit signature b c)
      {r r' : Circuit signature c d} (change : Step (@rules true) r r') : AssocCase p q r (.seqRight (.seq p q) change)

def classifyAssoc {a b c d} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d)
    {target} (change : Step (@rules true) (.seq (.seq p q) r) target) : AssocCase p q r change := by
  cases change with
  | root primitive =>
      cases rootView primitive with
      | assoc p q r => exact .same p q r
  | seqLeft child fixed =>
      cases child with
      | root primitive =>
          cases rootView primitive with
          | crypto stage => exact .leftCrypto stage _
          | assoc p q r => exact .leftAssoc _ _ _ _
          | fuseSeq p q => exact .leftFusion p q _
          | suffix stage tail => exact .leftSuffix stage tail _
      | seqLeft child fixed => exact .first child _ _
      | seqRight fixed child => exact .middle _ child _
  | seqRight fixed child => exact .last _ _ child

theorem noMixedBoxStep (label : MACNormalization.Atom) {target}
    (change : Step (@rules true) (.box label) target) : False := by
  cases label <;> cases change with
  | root primitive => cases rootView primitive

inductive WireCase : {a b : Port signature} → (p : Wiring signature a b) → {target : Circuit signature a b} →
    Step (@rules true) (.wire p) target → Type where
  | wire {a b} {p q : Wiring signature a b} (change : WireEdit p q) : WireCase p (wireChange change)

def classifyWire {a b} (p : Wiring signature a b) {target} (change : Step (@rules true) (.wire p) target) : WireCase p change := by
  cases change with
  | root primitive =>
      cases rootView primitive with
      | wire change => exact .wire change

inductive CryptoCase (stage : Nat) : {target : Circuit signature (source (stage + 1)) finish} →
    Step (@rules true) (before stage) target → Type where
  | same : CryptoCase stage (.root (.rule (Rule.crypto stage)))

def classifyCrypto (stage : Nat) {target} (change : Step (@rules true) (before stage) target) : CryptoCase stage change := by
  cases change with
  | root primitive =>
      cases rootView primitive with
      | crypto stage => exact .same
  | seqLeft child fixed => exact False.elim (noMixedBoxStep _ child)
  | seqRight fixed child => exact False.elim (noMixedBoxStep _ child)

inductive SeqFusionCase : {a b c : Port signature} → (p : Wiring signature a b) → (q : Wiring signature b c) →
    {target : Circuit signature a c} → Step (@rules true) (.seq (.wire p) (.wire q)) target → Type where
  | same {a b c} (p : Wiring signature a b) (q : Wiring signature b c) : SeqFusionCase p q (seqFusion p q)
  | left {a b c} {p p' : Wiring signature a b} (change : WireEdit p p') (q : Wiring signature b c) :
      SeqFusionCase p q (.seqLeft (wireChange change) (.wire q))
  | right {a b c} (p : Wiring signature a b) {q q' : Wiring signature b c} (change : WireEdit q q') :
      SeqFusionCase p q (.seqRight (.wire p) (wireChange change))

def classifySeqFusion {a b c} (p : Wiring signature a b) (q : Wiring signature b c) {target}
    (change : Step (@rules true) (.seq (.wire p) (.wire q)) target) : SeqFusionCase p q change := by
  cases change with
  | root primitive =>
      cases rootView primitive with
      | fuseSeq p q => exact .same p q
  | seqLeft child fixed =>
      cases classifyWire p child with
      | wire change => exact .left change q
  | seqRight fixed child =>
      cases classifyWire q child with
      | wire change => exact .right p change

inductive TensorFusionCase : {a b c d : Port signature} → (p : Wiring signature a b) → (q : Wiring signature c d) →
    {target : Circuit signature (.pair a c) (.pair b d)} → Step (@rules true) (.tensor (.wire p) (.wire q)) target → Type where
  | same {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) : TensorFusionCase p q (tensorFusion p q)
  | left {a b c d} {p p' : Wiring signature a b} (change : WireEdit p p') (q : Wiring signature c d) :
      TensorFusionCase p q (.tensorLeft (wireChange change) (.wire q))
  | right {a b c d} (p : Wiring signature a b) {q q' : Wiring signature c d} (change : WireEdit q q') :
      TensorFusionCase p q (.tensorRight (.wire p) (wireChange change))

def classifyTensorFusion {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) {target}
    (change : Step (@rules true) (.tensor (.wire p) (.wire q)) target) : TensorFusionCase p q change := by
  cases change with
  | root primitive =>
      cases rootView primitive with
      | fuseTensor p q => exact .same p q
  | tensorLeft child fixed =>
      cases classifyWire p child with
      | wire change => exact .left change q
  | tensorRight fixed child =>
      cases classifyWire q child with
      | wire change => exact .right p change

inductive SuffixCase (stage : Nat) : {a : Port signature} → (tail : Circuit signature finish a) →
    {target : Circuit signature (source (stage + 1)) a} →
    Step (@rules true) (.seq (.box (MACNormalization.Atom.schedule stage))
      (.seq (.box (MACNormalization.Atom.eliminate stage)) tail)) target → Type where
  | same {a} (tail : Circuit signature finish a) : SuffixCase stage tail (tailSuffix stage tail)
  | tail {a} {tail tail' : Circuit signature finish a} (change : Step (@rules true) tail tail') :
      SuffixCase stage tail (.seqRight (.box _) (.seqRight (.box _) change))

def classifySuffix (stage : Nat) {a} (tail : Circuit signature finish a) {target}
    (change : Step (@rules true) (.seq (.box (MACNormalization.Atom.schedule stage))
      (.seq (.box (MACNormalization.Atom.eliminate stage)) tail)) target) : SuffixCase stage tail change := by
  cases change with
  | root primitive =>
      cases rootView primitive with
      | suffix stage tail => exact .same tail
  | seqLeft child fixed => exact False.elim (noMixedBoxStep _ child)
  | seqRight fixed child =>
      cases child with
      | root primitive => cases rootView primitive
      | seqLeft child fixed => exact False.elim (noMixedBoxStep _ child)
      | seqRight fixed child => exact .tail child

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
