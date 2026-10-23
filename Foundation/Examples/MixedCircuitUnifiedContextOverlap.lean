import Foundation.Examples.MixedCircuitUnifiedOverlap

/-! Exhaustive competitors of association, MAC contraction, crypto suffix and
wire suffix in the unified catalogue. Wire-internal edits remain typed data;
this does not classify all internal eighteen-law critical pairs. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Overlap
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

def associate {a b c d} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d) :
    Step UnionRules (.seq (.seq p q) r) (.seq p (.seq q r)) := oldStep (Structural.Rule.assoc p q r)

def crypto (stage : Nat) : Step UnionRules (before stage) (after stage) := oldStep (Structural.Rule.crypto stage)

def cryptoSuffix (stage : Nat) {target} (tail : Circuit signature finish target) :
    Step UnionRules (.seq (.box (MACNormalization.Atom.schedule stage))
      (.seq (.box (MACNormalization.Atom.eliminate stage)) tail)) (.seq (after stage) tail) :=
  oldStep (Structural.Rule.suffix rfl stage tail)

inductive AssocCase : {a b c d : Port signature} → (p : Circuit signature a b) → (q : Circuit signature b c) →
    (r : Circuit signature c d) → {target : Circuit signature a d} → Step UnionRules (.seq (.seq p q) r) target → Type where
  | same {a b c d} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d) :
      AssocCase p q r (associate p q r)
  | leftCrypto (stage : Nat) {target} (r : Circuit signature finish target) :
      AssocCase (.box (MACNormalization.Atom.schedule stage)) (.box (MACNormalization.Atom.eliminate stage)) r
        (.seqLeft (crypto stage) r)
  | leftAssoc {a b c d e} (p : Circuit signature a b) (q : Circuit signature b c)
      (r : Circuit signature c d) (s : Circuit signature d e) :
      AssocCase (.seq p q) r s (.seqLeft (associate p q r) s)
  | leftFusion {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (r : Circuit signature c d) :
      AssocCase (.wire p) (.wire q) r (.seqLeft (seqFusion p q) r)
  | leftCryptoSuffix (stage : Nat) {target output} (tail : Circuit signature finish target) (r : Circuit signature target output) :
      AssocCase (.box (MACNormalization.Atom.schedule stage)) (.seq (.box (MACNormalization.Atom.eliminate stage)) tail) r
        (.seqLeft (cryptoSuffix stage tail) r)
  | leftWireSuffix {a b c d e} (p : Wiring signature a b) (q : Wiring signature b c)
      (tail : Circuit signature c d) (r : Circuit signature d e) :
      AssocCase (.wire p) (.seq (.wire q) tail) r (.seqLeft (suffixStep p q tail) r)
  | first {a b c d} {p p' : Circuit signature a b} (change : Step UnionRules p p')
      (q : Circuit signature b c) (r : Circuit signature c d) : AssocCase p q r (.seqLeft (.seqLeft change q) r)
  | middle {a b c d} (p : Circuit signature a b) {q q' : Circuit signature b c}
      (change : Step UnionRules q q') (r : Circuit signature c d) : AssocCase p q r (.seqLeft (.seqRight p change) r)
  | last {a b c d} (p : Circuit signature a b) (q : Circuit signature b c) {r r' : Circuit signature c d}
      (change : Step UnionRules r r') : AssocCase p q r (.seqRight (.seq p q) change)

def classifyAssoc {a b c d} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d)
    {target} (change : Step UnionRules (.seq (.seq p q) r) target) : AssocCase p q r change := by
  cases change with
  | root primitive => cases rootView primitive with
    | assoc p q r => exact .same p q r
  | seqLeft child fixed => cases child with
    | root primitive => cases rootView primitive with
      | crypto stage => exact .leftCrypto stage _
      | assoc p q r => exact .leftAssoc _ _ _ _
      | seqFusion p q => exact .leftFusion p q _
      | cryptoSuffix stage tail => exact .leftCryptoSuffix stage tail _
      | wireSuffix p q tail => exact .leftWireSuffix p q tail _
    | seqLeft child fixed => exact .first child _ _
    | seqRight fixed child => exact .middle _ child _
  | seqRight fixed child => exact .last _ _ child

inductive CryptoCase (stage : Nat) : {target : Circuit signature (source (stage + 1)) finish} →
    Step UnionRules (before stage) target → Type where
  | same : CryptoCase stage (crypto stage)

def classifyCrypto (stage : Nat) {target} (change : Step UnionRules (before stage) target) : CryptoCase stage change := by
  cases change with
  | root primitive => cases rootView primitive with
    | crypto stage => exact .same
  | seqLeft child fixed => exact False.elim (noBoxStep _ child)
  | seqRight fixed child => exact False.elim (noBoxStep _ child)

inductive CryptoSuffixCase (stage : Nat) : {a : Port signature} → (tail : Circuit signature finish a) →
    {target : Circuit signature (source (stage + 1)) a} →
    Step UnionRules (.seq (.box (MACNormalization.Atom.schedule stage))
      (.seq (.box (MACNormalization.Atom.eliminate stage)) tail)) target → Type where
  | same {a} (tail : Circuit signature finish a) : CryptoSuffixCase stage tail (cryptoSuffix stage tail)
  | tail {a} {tail tail' : Circuit signature finish a} (change : Step UnionRules tail tail') :
      CryptoSuffixCase stage tail (.seqRight (.box _) (.seqRight (.box _) change))

def classifyCryptoSuffix (stage : Nat) {a} (tail : Circuit signature finish a) {target}
    (change : Step UnionRules (.seq (.box (MACNormalization.Atom.schedule stage))
      (.seq (.box (MACNormalization.Atom.eliminate stage)) tail)) target) : CryptoSuffixCase stage tail change := by
  cases change with
  | root primitive => cases rootView primitive with
    | cryptoSuffix stage tail => exact .same tail
  | seqLeft child fixed => exact False.elim (noBoxStep _ child)
  | seqRight fixed child => cases child with
    | root primitive => cases rootView primitive
    | seqLeft child fixed => exact False.elim (noBoxStep _ child)
    | seqRight fixed child => exact .tail child

inductive WireSuffixCase : {a b c d : Port signature} → (p : Wiring signature a b) →
    (q : Wiring signature b c) → (tail : Circuit signature c d) → {target : Circuit signature a d} →
    Step UnionRules (.seq (.wire p) (.seq (.wire q) tail)) target → Type where
  | same {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
      WireSuffixCase p q tail (suffixStep p q tail)
  | oldFirst {a b c d} {p p' : Wiring signature a b} (change : Structural.WireEdit p p')
      (q : Wiring signature b c) (tail : Circuit signature c d) :
      WireSuffixCase p q tail (.seqLeft (oldEdit change) (.seq (.wire q) tail))
  | cartesianFirst {a b c d} {p p' : Wiring signature a b} (change : Cartesian.Step p p')
      (q : Wiring signature b c) (tail : Circuit signature c d) :
      WireSuffixCase p q tail (.seqLeft (edit change) (.seq (.wire q) tail))
  | rightFusion {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (r : Wiring signature c d) :
      WireSuffixCase p q (.wire r) (.seqRight (.wire p) (seqFusion q r))
  | rightSuffix {a b c d e} (p : Wiring signature a b) (q : Wiring signature b c)
      (r : Wiring signature c d) (tail : Circuit signature d e) :
      WireSuffixCase p q (.seq (.wire r) tail) (.seqRight (.wire p) (suffixStep q r tail))
  | oldMiddle {a b c d} (p : Wiring signature a b) {q q' : Wiring signature b c}
      (change : Structural.WireEdit q q') (tail : Circuit signature c d) :
      WireSuffixCase p q tail (.seqRight (.wire p) (.seqLeft (oldEdit change) tail))
  | cartesianMiddle {a b c d} (p : Wiring signature a b) {q q' : Wiring signature b c}
      (change : Cartesian.Step q q') (tail : Circuit signature c d) :
      WireSuffixCase p q tail (.seqRight (.wire p) (.seqLeft (edit change) tail))
  | tail {a b c d} (p : Wiring signature a b) (q : Wiring signature b c)
      {tail tail' : Circuit signature c d} (change : Step UnionRules tail tail') :
      WireSuffixCase p q tail (.seqRight (.wire p) (.seqRight (.wire q) change))

def classifyWireSuffix {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d)
    {target} (change : Step UnionRules (.seq (.wire p) (.seq (.wire q) tail)) target) : WireSuffixCase p q tail change := by
  cases change with
  | root primitive => cases rootView primitive with
    | wireSuffix p q tail => exact .same p q tail
  | seqLeft child fixed => cases classifyWire p child with
    | old change => exact .oldFirst change q tail
    | cartesian change => exact .cartesianFirst change q tail
  | seqRight fixed child => cases child with
    | root primitive => cases rootView primitive with
      | seqFusion q r => exact .rightFusion p q r
      | wireSuffix q r tail => exact .rightSuffix p q r tail
    | seqLeft child fixed => cases classifyWire q child with
      | old change => exact .oldMiddle p change tail
      | cartesian change => exact .cartesianMiddle p change tail
    | seqRight fixed child => exact .tail p q child

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Overlap
