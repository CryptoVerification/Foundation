import Foundation.Examples.MixedCircuitStatefulWiringHigher

/-! Typed exhaustive views for the actual unified root catalogue and the
competitors of wire fusion. Old eleven-law and added eighteen-law wire edits
are separate cases, with their original rewrite data retained. Classification
alone is not a resolution or a complete higher critical basis. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Overlap
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

abbrev SRule := Structural.Rule true

def oldPrimitive (label : SRule) : Primitive UnionRules (Structural.rules label).left (Structural.rules label).right :=
  .rule (relators := UnionRules) (Sum.inl (Structural.Fusion.Rule.existing label))

def oldStep (label : SRule) : Step UnionRules (Structural.rules label).left (Structural.rules label).right :=
  .root (oldPrimitive label)

def oldEdit {a b} {p q : Wiring signature a b} (change : Structural.WireEdit p q) :
    Step UnionRules (.wire p) (.wire q) := oldStep (Structural.Rule.wire change)

def suffixPrimitive {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    Primitive UnionRules (.seq (.wire p) (.seq (.wire q) tail)) (.seq (.wire (.seq p q)) tail) :=
  .rule (relators := UnionRules) (Sum.inl (Structural.Fusion.Rule.suffix p q tail))

def suffixStep {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    Step UnionRules (.seq (.wire p) (.seq (.wire q) tail)) (.seq (.wire (.seq p q)) tail) :=
  .root (suffixPrimitive p q tail)

inductive RootView : {a b : Port signature} → {p q : Circuit signature a b} → Primitive UnionRules p q → Type where
  | crypto (stage : Nat) : RootView (oldPrimitive (Structural.Rule.crypto stage))
  | assoc {a b c d} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d) :
      RootView (oldPrimitive (Structural.Rule.assoc p q r))
  | oldWire {a b} {p q : Wiring signature a b} (change : Structural.WireEdit p q) :
      RootView (oldPrimitive (Structural.Rule.wire change))
  | seqFusion {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
      RootView (oldPrimitive (Structural.Rule.fuseSeq p q))
  | tensorFusion {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) :
      RootView (oldPrimitive (Structural.Rule.fuseTensor p q))
  | cryptoSuffix (stage : Nat) {target} (tail : Circuit signature finish target) :
      RootView (oldPrimitive (Structural.Rule.suffix rfl stage tail))
  | wireSuffix {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
      RootView (suffixPrimitive p q tail)
  | cartesian {a b} {p q : Wiring signature a b} (change : Cartesian.Step p q) :
      RootView (Primitive.rule (relators := UnionRules) (Sum.inr (CartesianWiring.Rule.wire change)))

def rootView {a b} {p q : Circuit signature a b} (primitive : Primitive UnionRules p q) : RootView primitive := by
  cases primitive with
  | rule label => cases label with
    | inl label => cases label with
      | existing label => cases label with
        | crypto stage => exact .crypto stage
        | assoc p q r => exact .assoc p q r
        | wire change => exact .oldWire change
        | fuseSeq p q => exact .seqFusion p q
        | fuseTensor p q => exact .tensorFusion p q
        | suffix enabled stage tail => exact .cryptoSuffix stage tail
      | suffix p q tail => exact .wireSuffix p q tail
    | inr label => cases label with
      | wire change => exact .cartesian change

theorem noBoxStep (label : MACNormalization.Atom) {target} (change : Step UnionRules (.box label) target) : False := by
  cases label <;> cases change with
  | root primitive => cases rootView primitive

inductive WireCase : {a b : Port signature} → (p : Wiring signature a b) → {target : Circuit signature a b} →
    Step UnionRules (.wire p) target → Type where
  | old {a b} {p q : Wiring signature a b} (change : Structural.WireEdit p q) : WireCase p (oldEdit change)
  | cartesian {a b} {p q : Wiring signature a b} (change : Cartesian.Step p q) : WireCase p (edit change)

def classifyWire {a b} (p : Wiring signature a b) {target} (change : Step UnionRules (.wire p) target) :
    WireCase p change := by
  cases change with
  | root primitive => cases rootView primitive with
    | oldWire change => exact .old change
    | cartesian change => exact .cartesian change

inductive SeqFusionCase : {a b c : Port signature} → (p : Wiring signature a b) → (q : Wiring signature b c) →
    {target : Circuit signature a c} → Step UnionRules (.seq (.wire p) (.wire q)) target → Type where
  | same {a b c} (p : Wiring signature a b) (q : Wiring signature b c) : SeqFusionCase p q (seqFusion p q)
  | oldLeft {a b c} {p p' : Wiring signature a b} (change : Structural.WireEdit p p') (q : Wiring signature b c) :
      SeqFusionCase p q (.seqLeft (oldEdit change) (.wire q))
  | oldRight {a b c} (p : Wiring signature a b) {q q' : Wiring signature b c} (change : Structural.WireEdit q q') :
      SeqFusionCase p q (.seqRight (.wire p) (oldEdit change))
  | cartesianLeft {a b c} {p p' : Wiring signature a b} (change : Cartesian.Step p p') (q : Wiring signature b c) :
      SeqFusionCase p q (.seqLeft (edit change) (.wire q))
  | cartesianRight {a b c} (p : Wiring signature a b) {q q' : Wiring signature b c} (change : Cartesian.Step q q') :
      SeqFusionCase p q (.seqRight (.wire p) (edit change))

def classifySeqFusion {a b c} (p : Wiring signature a b) (q : Wiring signature b c) {target}
    (change : Step UnionRules (.seq (.wire p) (.wire q)) target) : SeqFusionCase p q change := by
  cases change with
  | root primitive => cases rootView primitive with
    | seqFusion p q => exact .same p q
  | seqLeft child fixed => cases classifyWire p child with
    | old change => exact .oldLeft change q
    | cartesian change => exact .cartesianLeft change q
  | seqRight fixed child => cases classifyWire q child with
    | old change => exact .oldRight p change
    | cartesian change => exact .cartesianRight p change

inductive TensorFusionCase : {a b c d : Port signature} → (p : Wiring signature a b) → (q : Wiring signature c d) →
    {target : Circuit signature (.pair a c) (.pair b d)} → Step UnionRules (.tensor (.wire p) (.wire q)) target → Type where
  | same {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) : TensorFusionCase p q (tensorFusion p q)
  | oldLeft {a b c d} {p p' : Wiring signature a b} (change : Structural.WireEdit p p') (q : Wiring signature c d) :
      TensorFusionCase p q (.tensorLeft (oldEdit change) (.wire q))
  | oldRight {a b c d} (p : Wiring signature a b) {q q' : Wiring signature c d} (change : Structural.WireEdit q q') :
      TensorFusionCase p q (.tensorRight (.wire p) (oldEdit change))
  | cartesianLeft {a b c d} {p p' : Wiring signature a b} (change : Cartesian.Step p p') (q : Wiring signature c d) :
      TensorFusionCase p q (.tensorLeft (edit change) (.wire q))
  | cartesianRight {a b c d} (p : Wiring signature a b) {q q' : Wiring signature c d} (change : Cartesian.Step q q') :
      TensorFusionCase p q (.tensorRight (.wire p) (edit change))

def classifyTensorFusion {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) {target}
    (change : Step UnionRules (.tensor (.wire p) (.wire q)) target) : TensorFusionCase p q change := by
  cases change with
  | root primitive => cases rootView primitive with
    | tensorFusion p q => exact .same p q
  | tensorLeft child fixed => cases classifyWire p child with
    | old change => exact .oldLeft change q
    | cartesian change => exact .cartesianLeft change q
  | tensorRight fixed child => cases classifyWire q child with
    | old change => exact .oldRight p change
    | cartesian change => exact .cartesianRight p change

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Overlap
