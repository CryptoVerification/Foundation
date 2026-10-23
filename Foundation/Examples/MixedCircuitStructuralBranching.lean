import Foundation.Examples.MixedCircuitStructuralOverlap

/-! Total classification of mixed circuit-level local branchings. Recursive
placements and separated changes reduce to eighteen rooted forms. The wire
form explicitly retains a pair of pure-wire changes as a remaining problem;
classification is not a filling or coherence theorem. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

def RootView.Competitor {a b} {p q : Circuit signature a b} {primitive : Primitive (@rules true) p q}
    (view : RootView primitive) {target} (other : Step (@rules true) p target) : Type :=
  match view with
  | .crypto stage => CryptoCase stage other
  | .assoc p q r => AssocCase p q r other
  | .wire (p := p) _ => WireCase p other
  | .fuseSeq p q => SeqFusionCase p q other
  | .fuseTensor p q => TensorFusionCase p q other
  | .suffix stage tail => SuffixCase stage tail other

def RootView.classify {a b} {p q : Circuit signature a b} {primitive : Primitive (@rules true) p q}
    (view : RootView primitive) {target} (other : Step (@rules true) p target) : view.Competitor other := by
  cases view with
  | crypto stage => exact classifyCrypto stage other
  | assoc p q r => exact classifyAssoc p q r other
  | wire change => exact classifyWire _ other
  | fuseSeq p q => exact classifySeqFusion p q other
  | fuseTensor p q => exact classifyTensorFusion p q other
  | suffix stage tail => exact classifySuffix stage tail other

def RootView.Competitor.code {a b} {p q : Circuit signature a b} {primitive : Primitive (@rules true) p q}
    {view : RootView primitive} {target} {other : Step (@rules true) p target} (result : view.Competitor other) : Fin 18 := by
  cases view with
  | crypto stage => exact 0
  | assoc p q r =>
      cases result with
      | same => exact 1
      | leftCrypto => exact 2
      | leftAssoc => exact 3
      | leftFusion => exact 4
      | leftSuffix => exact 5
      | first => exact 6
      | middle => exact 7
      | last => exact 8
  | wire change => exact 9
  | fuseSeq p q =>
      cases result with
      | same => exact 10
      | left => exact 11
      | right => exact 12
  | fuseTensor p q =>
      cases result with
      | same => exact 13
      | left => exact 14
      | right => exact 15
  | suffix stage tail =>
      cases result with
      | same => exact 16
      | tail => exact 17

structure RootBranch {a b} {p q r : Circuit signature a b}
    (primitive : Primitive (@rules true) p q) (other : Step (@rules true) p r) where
  view : RootView primitive
  competitor : view.Competitor other

def rootBranch {a b} {p q r : Circuit signature a b}
    (primitive : Primitive (@rules true) p q) (other : Step (@rules true) p r) : RootBranch primitive other :=
  ⟨rootView primitive, (rootView primitive).classify other⟩

inductive BranchView : {a b : Port signature} → {p q r : Circuit signature a b} →
    Step (@rules true) p q → Step (@rules true) p r → Type where
  | rootLeft {a b} {p q r : Circuit signature a b} (primitive : Primitive (@rules true) p q)
      (other : Step (@rules true) p r) (result : RootBranch primitive other) : BranchView (.root primitive) other
  | rootRight {a b} {p q r : Circuit signature a b} (other : Step (@rules true) p q)
      (primitive : Primitive (@rules true) p r) (result : RootBranch primitive other) : BranchView other (.root primitive)
  | separated {a b} {p q r : Circuit signature a b} {first : Step (@rules true) p q} {second : Step (@rules true) p r}
      (apart : Separated first second) : BranchView first second
  | seqLeft {a b c} {p q r : Circuit signature a b} {first : Step (@rules true) p q} {second : Step (@rules true) p r}
      (inner : BranchView first second) (fixed : Circuit signature b c) : BranchView (.seqLeft first fixed) (.seqLeft second fixed)
  | seqRight {a b c} (fixed : Circuit signature a b) {p q r : Circuit signature b c}
      {first : Step (@rules true) p q} {second : Step (@rules true) p r} (inner : BranchView first second) :
      BranchView (.seqRight fixed first) (.seqRight fixed second)
  | tensorLeft {a b c d} {p q r : Circuit signature a b} {first : Step (@rules true) p q} {second : Step (@rules true) p r}
      (inner : BranchView first second) (fixed : Circuit signature c d) : BranchView (.tensorLeft first fixed) (.tensorLeft second fixed)
  | tensorRight {a b c d} (fixed : Circuit signature a b) {p q r : Circuit signature c d}
      {first : Step (@rules true) p q} {second : Step (@rules true) p r} (inner : BranchView first second) :
      BranchView (.tensorRight fixed first) (.tensorRight fixed second)

def classifyBranch : {a b : Port signature} → {p q r : Circuit signature a b} →
    (first : Step (@rules true) p q) → (second : Step (@rules true) p r) → BranchView first second
  | _, _, _, _, _, .root primitive, other => .rootLeft primitive other (rootBranch primitive other)
  | _, _, _, _, _, other, .root primitive => .rootRight other primitive (rootBranch primitive other)
  | _, _, _, _, _, .seqLeft first fixed, .seqLeft second _ => .seqLeft (classifyBranch first second) fixed
  | _, _, _, _, _, .seqLeft first _, .seqRight _ second => .separated (.seqLR first second)
  | _, _, _, _, _, .seqRight _ first, .seqLeft second _ => .separated (.seqRL second first)
  | _, _, _, _, _, .seqRight fixed first, .seqRight _ second => .seqRight fixed (classifyBranch first second)
  | _, _, _, _, _, .tensorLeft first fixed, .tensorLeft second _ => .tensorLeft (classifyBranch first second) fixed
  | _, _, _, _, _, .tensorLeft first _, .tensorRight _ second => .separated (.tensorLR first second)
  | _, _, _, _, _, .tensorRight _ first, .tensorLeft second _ => .separated (.tensorRL second first)
  | _, _, _, _, _, .tensorRight fixed first, .tensorRight _ second => .tensorRight fixed (classifyBranch first second)

theorem classification_total {a b} {p q r : Circuit signature a b}
    (first : Step (@rules true) p q) (second : Step (@rules true) p r) : Nonempty (BranchView first second) :=
  ⟨classifyBranch first second⟩

/-- Context recursion reaches one classified root or one separated pair.
This counts mixed placement nodes only, not pure-wire tree depth or time. -/
def BranchView.depth : {a b : Port signature} → {p q r : Circuit signature a b} →
    {first : Step (@rules true) p q} → {second : Step (@rules true) p r} → BranchView first second → Nat
  | _, _, _, _, _, _, _, .rootLeft _ _ _ | _, _, _, _, _, _, _, .rootRight _ _ _ | _, _, _, _, _, _, _, .separated _ => 0
  | _, _, _, _, _, _, _, .seqLeft inner _ | _, _, _, _, _, _, _, .seqRight _ inner |
    _, _, _, _, _, _, _, .tensorLeft inner _ | _, _, _, _, _, _, _, .tensorRight _ inner => 1 + inner.depth

def rootBranchCode {a b} {p q r : Circuit signature a b}
    (primitive : Primitive (@rules true) p q) (other : Step (@rules true) p r) : Fin 18 :=
  (rootBranch primitive other).competitor.code

def BranchView.rootCode : {a b : Port signature} → {p q r : Circuit signature a b} →
    {first : Step (@rules true) p q} → {second : Step (@rules true) p r} → BranchView first second → Option (Fin 18)
  | _, _, _, _, _, _, _, .rootLeft _ _ result | _, _, _, _, _, _, _, .rootRight _ _ result => some result.competitor.code
  | _, _, _, _, _, _, _, .separated _ => none
  | _, _, _, _, _, _, _, .seqLeft inner _ | _, _, _, _, _, _, _, .seqRight _ inner |
    _, _, _, _, _, _, _, .tensorLeft inner _ | _, _, _, _, _, _, _, .tensorRight _ inner => inner.rootCode

theorem BranchView.depth_le_first {a b} {p q r : Circuit signature a b}
    {first : Step (@rules true) p q} {second : Step (@rules true) p r} (view : BranchView first second) :
    view.depth ≤ first.position.length := by
  induction view <;> simp_all only [depth, Step.position, List.length_cons, List.length_nil] <;> omega

theorem BranchView.depth_le_second {a b} {p q r : Circuit signature a b}
    {first : Step (@rules true) p q} {second : Step (@rules true) p r} (view : BranchView first second) :
    view.depth ≤ second.position.length := by
  induction view <;> simp_all only [depth, Step.position, List.length_cons, List.length_nil] <;> omega

/-- info: (2, 4, 5) -/
#guard_msgs in
#eval (rootBranchCode (.rule (Rule.assoc (.box (MACNormalization.Atom.schedule 0))
    (.box (MACNormalization.Atom.eliminate 0)) (.wire copy))) (tailCrypto true 0 (.wire copy)),
  rootBranchCode (.rule (Rule.assoc (.wire (.identity finish)) (.wire (.identity finish)) (.wire copy)))
    (.seqLeft (seqFusion (.identity finish) (.identity finish)) (.wire copy)),
  rootBranchCode (.rule (Rule.assoc (.box (MACNormalization.Atom.schedule 0))
    (.seq (.box (MACNormalization.Atom.eliminate 0)) (.wire (.identity finish))) (.wire copy)))
    (.seqLeft (tailSuffix 0 (.wire (.identity finish))) (.wire copy)))

/-- info: (2, some 2) -/
#guard_msgs in
#eval Id.run do
  let first := Step.seqLeft (Step.tensorRight (before 4) (assocFirst true 0 copy)) (.wire (.discard _))
  let second := Step.seqLeft (Step.tensorRight (before 4) (cryptoFirst true 0 copy)) (.wire (.discard _))
  let classified := classifyBranch first second
  return (classified.depth, classified.rootCode)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
