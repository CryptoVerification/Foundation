import Foundation.Examples.MixedCircuitStatefulStructural
import Foundation.Crypto.Logic.Polygraph.MixedCircuitStatefulWiringUnion
import Foundation.Examples.MixedCircuitFusionHigher

/-! Four explicit local squares exchange an 18-law wire edit with actual
sequential/tensor wire fusion in the unified MAC catalogue. Old generators,
pure local generators and separated cross squares remain available. This is
an extension of a partial basis, not a complete cross-critical classification. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring
open Foundation.Probability
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false
abbrev UnionRules := Stateful.WiringUnion.rules Structural.Fusion.rules
abbrev OldBasis := Stateful.WiringUnion.basis Structural.Fusion.basis

def seqFusion {a b c} (p : Wiring signature a b) (q : Wiring signature b c) :
    Step UnionRules (.seq (.wire p) (.wire q)) (.wire (.seq p q)) :=
  Stateful.WiringUnion.embedStep (.root (.rule (relators := Structural.Fusion.rules)
    (Structural.Fusion.Rule.existing (Structural.Rule.fuseSeq p q))))

def tensorFusion {a b c d} (p : Wiring signature a b) (q : Wiring signature c d) :
    Step UnionRules (.tensor (.wire p) (.wire q)) (.wire (.tensor p q)) :=
  Stateful.WiringUnion.embedStep (.root (.rule (relators := Structural.Fusion.rules)
    (Structural.Fusion.Rule.existing (Structural.Rule.fuseTensor p q))))

def edit {a b} {p q : Wiring signature a b} (change : Cartesian.Step p q) :
    Step UnionRules (.wire p) (.wire q) := Stateful.WiringUnion.wireStep change

def two {a b} {p q r : Circuit signature a b} (first : Step UnionRules p q) (second : Step UnionRules q r) :
    RewriteTrack (relators := UnionRules) p r := .comp (.step first) (.step second)

inductive LocalDiagram : {a b : Port signature} → {p q : Circuit signature a b} →
    RewriteTrack (relators := UnionRules) p q → RewriteTrack (relators := UnionRules) p q → Type where
  | seqLeft {a b c} {p p' : Wiring signature a b} (change : Cartesian.Step p p') (q : Wiring signature b c) :
      LocalDiagram (two (.seqLeft (edit change) (.wire q)) (seqFusion p' q))
        (two (seqFusion p q) (edit (.seqLeft change q)))
  | seqRight {a b c} (p : Wiring signature a b) {q q' : Wiring signature b c} (change : Cartesian.Step q q') :
      LocalDiagram (two (.seqRight (.wire p) (edit change)) (seqFusion p q'))
        (two (seqFusion p q) (edit (.seqRight p change)))
  | tensorLeft {a b c d} {p p' : Wiring signature a b} (change : Cartesian.Step p p') (q : Wiring signature c d) :
      LocalDiagram (two (.tensorLeft (edit change) (.wire q)) (tensorFusion p' q))
        (two (tensorFusion p q) (edit (.tensorLeft change q)))
  | tensorRight {a b c d} (p : Wiring signature a b) {q q' : Wiring signature c d} (change : Cartesian.Step q q') :
      LocalDiagram (two (.tensorRight (.wire p) (edit change)) (tensorFusion p q'))
        (two (tensorFusion p q) (edit (.tensorRight p change)))

theorem local_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (generator : LocalDiagram first second) : RewriteTrack.support first = ∅ ∧ RewriteTrack.support second = ∅ := by
  cases generator <;> simp [two, RewriteTrack.support, Step.support, seqFusion, tensorFusion,
    edit, Stateful.WiringUnion.wireStep, Stateful.WiringUnion.embedStep, Primitive.support, Relator.support,
    UnionRules, Stateful.WiringUnion.rules, Structural.Fusion.rules, Structural.rules, CartesianWiring.relators,
    Circuit.needs]

inductive Generator : {a b : Port signature} → {p q : Circuit signature a b} →
    RewriteTrack (relators := UnionRules) p q → RewriteTrack (relators := UnionRules) p q → Type where
  | existing {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
      (generator : OldBasis.Generator first second) : Generator first second
  | localSquare {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
      (generator : LocalDiagram first second) : Generator first second

def baseBasis : HigherBasis UnionRules where
  Generator := Generator
  requirements := fun generator => match generator with
    | .existing generator => OldBasis.requirements generator
    | .localSquare _ => ∅
  covered := by
    intro a b p q first second generator
    cases generator with
    | existing generator => exact OldBasis.covered generator
    | localSquare generator =>
        rcases local_support generator with ⟨one, two⟩
        rw [one, two]
        exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

def basis : HigherBasis UnionRules := contextualBasis baseBasis

abbrev Cell {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := UnionRules) p q) :=
  PresentedCell basis first second

def LocalDiagram.cell {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (generator : LocalDiagram first second) : Cell first second := .generator (.root (.localSquare generator))

theorem local_cell_support {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := UnionRules) p q}
    (generator : LocalDiagram first second) : PresentedCell.support generator.cell = ∅ := rfl

theorem local_context_support {a b c d} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q}
    (place : Placement (signature := signature) a b c d) (generator : LocalDiagram first second) :
    PresentedCell.support (generator.cell.whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, local_cell_support, Finset.empty_union]

theorem local_context_count {a b c d} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q}
    (place : Placement (signature := signature) a b c d) (generator : LocalDiagram first second) :
    PresentedCell.constructorCount (generator.cell.whisker place) = 1 := by
  rw [PresentedCell.whisker_constructorCount]
  rfl

noncomputable def checked {State : Type} {condition : Nat → Prop} {Value : signature.PortAtom → Type}
    (model : Stateful.CheckedModel MAC.relators condition Value State) :
    Stateful.CheckedModel UnionRules condition Value State :=
  Stateful.WiringUnion.checked (StatefulStructural.allRules model)

/-- The original MAC interpretation is concrete. Its added state is retained
as context; proof transformations do not rerun the native caller. -/
noncomputable def original {State : Type} (orders : Nat → Foundation.Logic.Polygraph.ScheduleCertificate.Schedule 8) :
    Stateful.CheckedModel UnionRules
      (CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.MACNormalization.condition orders)
      (family orders) State :=
  checked (Stateful.liftChecked (MAC.model orders))

theorem local_repaired_joint {State Context : Type} {old updated : Nat → Prop} {Value : signature.PortAtom → Type}
    (model : Stateful.CheckedModel MAC.relators updated Value State) {a b c d} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q}
    (place : Placement (signature := signature) a b c d) (generator : LocalDiagram first second)
    (changed : Finset Nat) (cached : Holds old place.needs)
    (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh place.needs changed))
    (law : PMF (Context × (State × Bundle Value c))) :
    ∃ left : Holds updated (place.apply p).needs, ∃ right : Holds updated (place.apply q).needs,
      law.bind (fun past => (Stateful.evaluate model.base (place.apply p) left past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (Stateful.evaluate model.base (place.apply q) right past.2.1 past.2.2).map (fun next => (past, next))) := by
  have cached' : Holds old (PresentedCell.support (generator.cell.whisker place)) := by
    rw [local_context_support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support (generator.cell.whisker place)) changed) := by
    rw [local_context_support]; exact rechecked
  exact Stateful.cell_repaired_joint (checked model) (generator.cell.whisker place) changed cached' unchanged rechecked' law

/-- Reuse every existing higher proof composition, without turning it into
an extra root generator. -/
def embedOld {a b : Port signature} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := UnionRules) p q} → PresentedCell OldBasis first second → Cell first second
  | _, _, _, _, .refl p => .refl p
  | _, _, _, _, .generator generator => .generator (.root (.existing generator))
  | _, _, _, _, .symm child => (embedOld child).symm
  | _, _, _, _, .trans first second => (embedOld first).trans (embedOld second)
  | _, _, _, _, .comp first second => .comp (embedOld first) (embedOld second)
  | _, _, _, _, .inverse child => .inverse (embedOld child)
  | _, _, _, _, .assoc p q r => .assoc p q r
  | _, _, _, _, .leftUnit p => .leftUnit p
  | _, _, _, _, .rightUnit p => .rightUnit p
  | _, _, _, _, .leftInv p => .leftInv p
  | _, _, _, _, .rightInv p => .rightInv p

theorem embedOld_support {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q} (cell : PresentedCell OldBasis first second) :
    PresentedCell.support (embedOld cell) = PresentedCell.support cell := by
  induction cell <;> simp_all only [embedOld, PresentedCell.support, basis, contextualBasis, ContextualGenerator.support, baseBasis]

theorem embedOld_count {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := UnionRules) p q} (cell : PresentedCell OldBasis first second) :
    PresentedCell.constructorCount (embedOld cell) = PresentedCell.constructorCount cell := by
  induction cell <;> simp_all only [embedOld, PresentedCell.constructorCount]

/-- This instance uses an actual added cartesian root, beyond the old eleven
pure-wire roots, inside the sequential-fusion critical square. -/
def addedWireSquare := LocalDiagram.seqLeft
  (Cartesian.Step.root (Cartesian.Root.leftUnitInvExpand finish)) (Wire.leftUnit finish)

theorem added_step_not_old :
    ¬ Nonempty (Track (fun p q => Structural.WireEdit p q)
      (Wire.leftUnitInv finish) (Cartesian.fork (Wire.discard finish) (Wire.identity finish))) := by
  rintro ⟨path⟩
  have count := Cartesian.oldTrack_count path
  change 1 = 0 + (0 + 0) at count
  omega

/-- info: (1, 0) -/
#guard_msgs in
#eval (PresentedCell.constructorCount addedWireSquare.cell, (PresentedCell.support addedWireSquare.cell).card)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.StatefulWiring
