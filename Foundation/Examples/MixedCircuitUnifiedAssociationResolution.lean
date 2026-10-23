import Foundation.Examples.MixedCircuitUnifiedAssociationDiagrams

/-! Root-specific exhaustive resolution of the nine typed association
competitor forms in the actual unified catalogue. Both residuals are forward
and have at most two steps. Other catalogue roots/outer overlaps remain open. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Association
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Overlap
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

inductive TwoForward {a b : Port signature} : Circuit signature a b → Circuit signature a b → Type where
  | refl (p) : TwoForward p p
  | one {p q} (change : Step UnionRules p q) : TwoForward p q
  | two {p q r} (first : Step UnionRules p q) (second : Step UnionRules q r) : TwoForward p r

def TwoForward.track {a b : Port signature} : {p q : Circuit signature a b} → TwoForward p q → RewriteTrack (relators := UnionRules) p q
  | _, _, .refl p => .refl p
  | _, _, .one change => .step change
  | _, _, .two first second => .comp (.step first) (.step second)

def TwoForward.path {a b : Port signature} : {p q : Circuit signature a b} → TwoForward p q → Path (relators := UnionRules) p q
  | _, _, .refl p => .refl p
  | _, _, .one change => RewritePath.single change
  | _, _, .two first second => .cons first (RewritePath.single second)

def TwoForward.steps {a b : Port signature} {p q : Circuit signature a b} : TwoForward p q → Nat
  | .refl _ => 0
  | .one _ => 1
  | .two _ _ => 2

theorem TwoForward.bounded {a b : Port signature} {p q : Circuit signature a b} (residual : TwoForward p q) :
    residual.steps ≤ 2 := by cases residual <;> simp only [TwoForward.steps] <;> omega

structure Resolution {a b : Port signature} {source left right : Circuit signature a b}
    (first : Step UnionRules source left) (second : Step UnionRules source right) where
  target : Circuit signature a b
  afterFirst : TwoForward left target
  afterSecond : TwoForward right target
  comparison : Cell (.comp (.step first) afterFirst.track) (.comp (.step second) afterSecond.track)

def resolveCase {a b c d : Port signature} : {p : Circuit signature a b} → {q : Circuit signature b c} →
    {r : Circuit signature c d} → {target : Circuit signature a d} →
    {change : Step UnionRules (.seq (.seq p q) r) target} → AssocCase p q r change → Resolution (associate p q r) change
  | _, _, _, _, _, .same p q r => ⟨_, .refl _, .refl _, .refl _⟩
  | _, _, _, _, _, .leftCrypto stage rest =>
      ⟨_, .one (cryptoSuffix stage rest), .refl _,
        (cryptoCritical stage rest).trans (Four.rightUnit (.step (Step.seqLeft (crypto stage) rest))).symm⟩
  | _, _, _, _, _, .leftAssoc p q r s =>
      ⟨_, .one (associate p q (.seq r s)), .two (associate p (.seq q r) s) (.seqRight p (associate q r s)), pentagon p q r s⟩
  | _, _, _, _, _, .leftFusion p q rest =>
      ⟨_, .one (suffixStep p q rest), .refl _,
        (fusionCritical p q rest).trans (Four.rightUnit (.step (Step.seqLeft (seqFusion p q) rest))).symm⟩
  | _, _, _, _, _, .leftCryptoSuffix stage tail rest =>
      ⟨_, .two (.seqRight (.box (MACNormalization.Atom.schedule stage))
        (associate (.box (MACNormalization.Atom.eliminate stage)) tail rest)) (cryptoSuffix stage (.seq tail rest)),
        .one (associate (after stage) tail rest), (cryptoSuffixAssoc stage tail rest).symm⟩
  | _, _, _, _, _, .leftWireSuffix p q tail rest =>
      ⟨_, .two (.seqRight (.wire p) (associate (.wire q) tail rest)) (suffixStep p q (.seq tail rest)),
        .one (associate (.wire (.seq p q)) tail rest), (wireSuffixAssoc p q tail rest).symm⟩
  | _, _, _, _, _, .first (p' := p') change q r =>
      ⟨_, .one (.seqLeft change (.seq q r)), .one (associate p' q r), (firstNaturality change q r).symm⟩
  | _, _, _, _, _, .middle (q' := q') p change r =>
      ⟨_, .one (.seqRight p (.seqLeft change r)), .one (associate p q' r), (middleNaturality p change r).symm⟩
  | _, _, _, _, _, .last (r' := r') p q change =>
      ⟨_, .one (.seqRight p (.seqRight q change)), .one (associate p q r'), (lastNaturality p q change).symm⟩

def resolve {a b c d} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d) {target}
    (change : Step UnionRules (.seq (.seq p q) r) target) : Resolution (associate p q r) change :=
  resolveCase (classifyAssoc p q r change)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Association
