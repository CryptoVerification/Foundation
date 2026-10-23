import Foundation.Examples.MixedCircuitUnifiedContextOverlap

/-! Exhaustive resolution of all competitors of the actual sequential and
tensor pure-wire fusion roots in the unified catalogue. Old and added wire
edits use their existing local squares; no arbitrary parallel-cell root is
introduced. Root-root pure-wire internal and other catalogue rows remain open. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Overlap
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

/-- Residuals are forward and contain at most one actual rewrite. -/
inductive ShortForward {a b : Port signature} : Circuit signature a b → Circuit signature a b → Type where
  | refl (p) : ShortForward p p
  | step {p q} (change : Step UnionRules p q) : ShortForward p q

def ShortForward.track {a b : Port signature} : {p q : Circuit signature a b} → ShortForward p q →
    RewriteTrack (relators := UnionRules) p q
  | _, _, .refl p => .refl p
  | _, _, .step change => .step change

def ShortForward.path {a b : Port signature} : {p q : Circuit signature a b} → ShortForward p q →
    Path (relators := UnionRules) p q
  | _, _, .refl p => .refl p
  | _, _, .step change => RewritePath.single change

def ShortForward.steps {a b : Port signature} {p q : Circuit signature a b} : ShortForward p q → Nat
  | .refl _ => 0
  | .step _ => 1

theorem ShortForward.bounded {a b : Port signature} {p q : Circuit signature a b} (residual : ShortForward p q) :
    residual.steps ≤ 1 := by cases residual <;> simp only [ShortForward.steps] <;> omega

structure Resolution {a b : Port signature} {source left right : Circuit signature a b}
    (first : Step UnionRules source left) (second : Step UnionRules source right) where
  target : Circuit signature a b
  afterFirst : ShortForward left target
  afterSecond : ShortForward right target
  comparison : Cell (.comp (.step first) afterFirst.track) (.comp (.step second) afterSecond.track)

def oldSeqLeft {a b c} {p p' : Wiring signature a b} (change : Structural.WireEdit p p') (q : Wiring signature b c) :
    Cell (two (.seqLeft (oldEdit change) (.wire q)) (seqFusion p' q))
      (two (seqFusion p q) (oldEdit (.seqLeft change q))) :=
  embedOld (Stateful.WiringUnion.embedCell (Structural.Fusion.embedCell (Structural.LocalDiagram.seqWireLeft change q).cell))

def oldSeqRight {a b c} (p : Wiring signature a b) {q q' : Wiring signature b c} (change : Structural.WireEdit q q') :
    Cell (two (.seqRight (.wire p) (oldEdit change)) (seqFusion p q'))
      (two (seqFusion p q) (oldEdit (.seqRight p change))) :=
  embedOld (Stateful.WiringUnion.embedCell (Structural.Fusion.embedCell (Structural.LocalDiagram.seqWireRight p change).cell))

def oldTensorLeft {a b c d} {p p' : Wiring signature a b} (change : Structural.WireEdit p p') (q : Wiring signature c d) :
    Cell (two (.tensorLeft (oldEdit change) (.wire q)) (tensorFusion p' q))
      (two (tensorFusion p q) (oldEdit (.tensorLeft change q))) :=
  embedOld (Stateful.WiringUnion.embedCell (Structural.Fusion.embedCell (Structural.LocalDiagram.tensorWireLeft change q).cell))

def oldTensorRight {a b c d} (p : Wiring signature a b) {q q' : Wiring signature c d} (change : Structural.WireEdit q q') :
    Cell (two (.tensorRight (.wire p) (oldEdit change)) (tensorFusion p q'))
      (two (tensorFusion p q) (oldEdit (.tensorRight p change))) :=
  embedOld (Stateful.WiringUnion.embedCell (Structural.Fusion.embedCell (Structural.LocalDiagram.tensorWireRight p change).cell))

theorem oldSeqLeft_support {a b c} {p p' : Wiring signature a b} (change : Structural.WireEdit p p') (q : Wiring signature b c) :
    PresentedCell.support (oldSeqLeft change q) = ∅ := by
  rw [oldSeqLeft, embedOld_support, Stateful.WiringUnion.embedCell_support, Structural.Fusion.embedCell_support, Structural.seqWireLeft_support]

theorem oldSeqRight_support {a b c} (p : Wiring signature a b) {q q' : Wiring signature b c} (change : Structural.WireEdit q q') :
    PresentedCell.support (oldSeqRight p change) = ∅ := by
  rw [oldSeqRight, embedOld_support, Stateful.WiringUnion.embedCell_support, Structural.Fusion.embedCell_support, Structural.seqWireRight_support]

theorem oldTensorLeft_support {a b c d} {p p' : Wiring signature a b} (change : Structural.WireEdit p p') (q : Wiring signature c d) :
    PresentedCell.support (oldTensorLeft change q) = ∅ := by
  rw [oldTensorLeft, embedOld_support, Stateful.WiringUnion.embedCell_support, Structural.Fusion.embedCell_support, Structural.tensorWireLeft_support]

theorem oldTensorRight_support {a b c d} (p : Wiring signature a b) {q q' : Wiring signature c d} (change : Structural.WireEdit q q') :
    PresentedCell.support (oldTensorRight p change) = ∅ := by
  rw [oldTensorRight, embedOld_support, Stateful.WiringUnion.embedCell_support, Structural.Fusion.embedCell_support, Structural.tensorWireRight_support]

def resolveSeqCase {a b c} : {p : Wiring signature a b} → {q : Wiring signature b c} → {target : Circuit signature a c} →
    {change : Step UnionRules (.seq (.wire p) (.wire q)) target} → SeqFusionCase p q change → Resolution (seqFusion p q) change
  | _, _, _, _, .same p q => ⟨_, .refl _, .refl _, .refl _⟩
  | _, _, _, _, .oldLeft (p' := p') change q =>
      ⟨_, .step (oldEdit (.seqLeft change q)), .step (seqFusion p' q), (oldSeqLeft change q).symm⟩
  | _, _, _, _, .oldRight (q' := q') p change =>
      ⟨_, .step (oldEdit (.seqRight p change)), .step (seqFusion p q'), (oldSeqRight p change).symm⟩
  | _, _, _, _, .cartesianLeft (p' := p') change q =>
      ⟨_, .step (edit (.seqLeft change q)), .step (seqFusion p' q), (LocalDiagram.seqLeft change q).cell.symm⟩
  | _, _, _, _, .cartesianRight (q' := q') p change =>
      ⟨_, .step (edit (.seqRight p change)), .step (seqFusion p q'), (LocalDiagram.seqRight p change).cell.symm⟩

def resolveTensorCase {a b c d} : {p : Wiring signature a b} → {q : Wiring signature c d} → {target : Circuit signature (.pair a c) (.pair b d)} →
    {change : Step UnionRules (.tensor (.wire p) (.wire q)) target} → TensorFusionCase p q change → Resolution (tensorFusion p q) change
  | _, _, _, _, .same p q => ⟨_, .refl _, .refl _, .refl _⟩
  | _, _, _, _, .oldLeft (p' := p') change q =>
      ⟨_, .step (oldEdit (.tensorLeft change q)), .step (tensorFusion p' q), (oldTensorLeft change q).symm⟩
  | _, _, _, _, .oldRight (q' := q') p change =>
      ⟨_, .step (oldEdit (.tensorRight p change)), .step (tensorFusion p q'), (oldTensorRight p change).symm⟩
  | _, _, _, _, .cartesianLeft (p' := p') change q =>
      ⟨_, .step (edit (.tensorLeft change q)), .step (tensorFusion p' q), (LocalDiagram.tensorLeft change q).cell.symm⟩
  | _, _, _, _, .cartesianRight (q' := q') p change =>
      ⟨_, .step (edit (.tensorRight p change)), .step (tensorFusion p q'), (LocalDiagram.tensorRight p change).cell.symm⟩

def resolveSeq {a b c} (p : Wiring signature a b) (q : Wiring signature b c) {target}
    (change : Step UnionRules (.seq (.wire p) (.wire q)) target) : Resolution (seqFusion p q) change :=
  resolveSeqCase (classifySeqFusion p q change)

def resolveTensor {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) {target}
    (change : Step UnionRules (.tensor (.wire p) (.wire q)) target) : Resolution (tensorFusion p q) change :=
  resolveTensorCase (classifyTensorFusion p q change)

theorem resolveSeqCase_support {a b c} {p : Wiring signature a b} {q : Wiring signature b c} {target}
    {change : Step UnionRules (.seq (.wire p) (.wire q)) target} (view : SeqFusionCase p q change) :
    PresentedCell.support (resolveSeqCase view).comparison = ∅ := by
  cases view with
  | same =>
      simp [resolveSeqCase, ShortForward.track, PresentedCell.support, RewriteTrack.support, seqFusion, Step.support,
        Stateful.WiringUnion.embedStep, Primitive.support, Relator.support, UnionRules,
        Stateful.WiringUnion.rules, Structural.Fusion.rules, Structural.rules, Circuit.needs]
  | oldLeft change q => exact oldSeqLeft_support change q
  | oldRight change => exact oldSeqRight_support p change
  | cartesianLeft change q => exact local_cell_support (LocalDiagram.seqLeft change q)
  | cartesianRight change => exact local_cell_support (LocalDiagram.seqRight p change)

theorem resolveTensorCase_support {a b c d} {p : Wiring signature a b} {q : Wiring signature c d} {target}
    {change : Step UnionRules (.tensor (.wire p) (.wire q)) target} (view : TensorFusionCase p q change) :
    PresentedCell.support (resolveTensorCase view).comparison = ∅ := by
  cases view with
  | same =>
      simp [resolveTensorCase, ShortForward.track, PresentedCell.support, RewriteTrack.support, tensorFusion, Step.support,
        Stateful.WiringUnion.embedStep, Primitive.support, Relator.support, UnionRules,
        Stateful.WiringUnion.rules, Structural.Fusion.rules, Structural.rules, Circuit.needs]
  | oldLeft change q => exact oldTensorLeft_support change q
  | oldRight change => exact oldTensorRight_support p change
  | cartesianLeft change q => exact local_cell_support (LocalDiagram.tensorLeft change q)
  | cartesianRight change => exact local_cell_support (LocalDiagram.tensorRight p change)

theorem resolveSeqCase_count {a b c} {p : Wiring signature a b} {q : Wiring signature b c} {target}
    {change : Step UnionRules (.seq (.wire p) (.wire q)) target} (view : SeqFusionCase p q change) :
    PresentedCell.constructorCount (resolveSeqCase view).comparison ≤ 2 := by
  cases view <;> first | exact Nat.le_refl 2 | exact Nat.le_succ 1

theorem resolveTensorCase_count {a b c d} {p : Wiring signature a b} {q : Wiring signature c d} {target}
    {change : Step UnionRules (.tensor (.wire p) (.wire q)) target} (view : TensorFusionCase p q change) :
    PresentedCell.constructorCount (resolveTensorCase view).comparison ≤ 2 := by
  cases view <;> first | exact Nat.le_refl 2 | exact Nat.le_succ 1

theorem resolveSeq_support {a b c} (p : Wiring signature a b) (q : Wiring signature b c) {target}
    (change : Step UnionRules (.seq (.wire p) (.wire q)) target) :
    PresentedCell.support (resolveSeq p q change).comparison = ∅ := resolveSeqCase_support _

theorem resolveTensor_support {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) {target}
    (change : Step UnionRules (.tensor (.wire p) (.wire q)) target) :
    PresentedCell.support (resolveTensor p q change).comparison = ∅ := resolveTensorCase_support _

theorem resolveSeq_context_support {a b c x y} (p : Wiring signature a b) (q : Wiring signature b c) {target}
    (change : Step UnionRules (.seq (.wire p) (.wire q)) target)
    (place : Placement (signature := signature) a c x y) :
    PresentedCell.support ((resolveSeq p q change).comparison.whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, resolveSeq_support, Finset.empty_union]

theorem resolveTensor_context_support {a b c d x y} (p : Wiring signature a b) (q : Wiring signature c d) {target}
    (change : Step UnionRules (.tensor (.wire p) (.wire q)) target)
    (place : Placement (signature := signature) (.pair a c) (.pair b d) x y) :
    PresentedCell.support ((resolveTensor p q change).comparison.whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, resolveTensor_support, Finset.empty_union]

theorem resolveSeq_context_count {a b c x y} (p : Wiring signature a b) (q : Wiring signature b c) {target}
    (change : Step UnionRules (.seq (.wire p) (.wire q)) target)
    (place : Placement (signature := signature) a c x y) :
    PresentedCell.constructorCount ((resolveSeq p q change).comparison.whisker place) ≤ 2 := by
  rw [PresentedCell.whisker_constructorCount]
  exact resolveSeqCase_count _

theorem resolveTensor_context_count {a b c d x y} (p : Wiring signature a b) (q : Wiring signature c d) {target}
    (change : Step UnionRules (.tensor (.wire p) (.wire q)) target)
    (place : Placement (signature := signature) (.pair a c) (.pair b d) x y) :
    PresentedCell.constructorCount ((resolveTensor p q change).comparison.whisker place) ≤ 2 := by
  rw [PresentedCell.whisker_constructorCount]
  exact resolveTensorCase_count _

/-- Applies in particular to both generated fusion resolvers. The endpoint
kernel equality does not claim equality of extracted native compilers. -/
theorem Resolution.repaired_joint {State Context : Type} {old updated : Nat → Prop} {Value : signature.PortAtom → Type}
    (model : Stateful.CheckedModel MAC.relators updated Value State) {a b c d}
    {source left right : Circuit signature a b} {first : Step UnionRules source left} {second : Step UnionRules source right}
    (resolution : Resolution first second) (empty : PresentedCell.support resolution.comparison = ∅)
    (place : Placement (signature := signature) a b c d) (changed : Finset Nat) (cached : Holds old place.needs)
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh place.needs changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value c))) :
    ∃ before : Holds updated (place.apply source).needs,
    ∃ after : Holds updated (place.apply resolution.target).needs,
      law.bind (fun past => (Stateful.evaluate model.base (place.apply source) before past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (Stateful.evaluate model.base (place.apply resolution.target) after past.2.1 past.2.2).map (fun next => (past, next))) := by
  have support : PresentedCell.support (resolution.comparison.whisker place) = place.needs := by
    rw [PresentedCell.whisker_support, empty, Finset.empty_union]
  have cached' : Holds old (PresentedCell.support (resolution.comparison.whisker place)) := by rw [support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support (resolution.comparison.whisker place)) changed) := by
    rw [support]; exact rechecked
  exact Stateful.cell_repaired_joint (StatefulWiring.checked model) (resolution.comparison.whisker place)
    changed cached' unchanged rechecked' law

/-- info: (1, 1, 2, 0) -/
#guard_msgs in
#eval Id.run do
  let p := Wire.leftUnitInv finish
  let q := Wire.leftUnit finish
  let change := Step.seqLeft (edit (Cartesian.Step.root (Cartesian.Root.leftUnitInvExpand finish))) (Circuit.wire q)
  let result := resolveSeq p q change
  return (result.afterFirst.steps, result.afterSecond.steps,
    PresentedCell.constructorCount result.comparison, (PresentedCell.support result.comparison).card)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring.Overlap
