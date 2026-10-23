import Foundation.Crypto.Logic.Polygraph.MixedCircuitStatefulWiringUnion
import Foundation.Logic.Polygraph.StructuralCartesianUnitCritical

/-! Retain the existing mixed higher presentation and add the explicit pure
unit-critical presentation. First-level rules and checked models are unchanged.
This is a partial extension, not a full mixed critical-basis theorem. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion.CartesianUnitCritical
open Foundation.Probability
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {original : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false

inductive Generator (old : HigherBasis original) : {a b : Port signature} → {p q : Circuit signature a b} →
    RewriteTrack (relators := rules original) p q → RewriteTrack (relators := rules original) p q → Type where
  | existing {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := rules original) p q}
      (generator : (WiringUnion.basis old).Generator first second) : Generator old first second
  | pure {a b} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
      (generator : Cartesian.Higher.UnitCritical.Generator first second) :
      Generator old (wireTrack first) (wireTrack second)

def baseBasis (old : HigherBasis original) : HigherBasis (rules original) where
  Generator := Generator old
  requirements := fun generator => match generator with
    | .existing generator => (WiringUnion.basis old).requirements generator
    | .pure _ => ∅
  covered := by
    intro a b p q first second generator
    cases generator with
    | existing generator => exact (WiringUnion.basis old).covered generator
    | pure generator =>
        simp only [wireTrack_support]
        exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

def basis (old : HigherBasis original) : HigherBasis (rules original) := contextualBasis (baseBasis old)

def embedOld (old : HigherBasis original) {a b : Port signature} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := rules original) p q} →
    PresentedCell (WiringUnion.basis old) first second → PresentedCell (basis old) first second
  | _, _, _, _, .refl path => .refl path
  | _, _, _, _, .generator generator => .generator (.root (.existing generator))
  | _, _, _, _, .symm child => (embedOld old child).symm
  | _, _, _, _, .trans first second => (embedOld old first).trans (embedOld old second)
  | _, _, _, _, .comp first second => .comp (embedOld old first) (embedOld old second)
  | _, _, _, _, .inverse child => .inverse (embedOld old child)
  | _, _, _, _, .assoc p q r => .assoc p q r
  | _, _, _, _, .leftUnit path => .leftUnit path
  | _, _, _, _, .rightUnit path => .rightUnit path
  | _, _, _, _, .leftInv path => .leftInv path
  | _, _, _, _, .rightInv path => .rightInv path

theorem embedOld_support (old : HigherBasis original) {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := rules original) p q}
    (cell : PresentedCell (WiringUnion.basis old) first second) :
    PresentedCell.support (embedOld old cell) = PresentedCell.support cell := by
  induction cell <;> simp_all only [embedOld, PresentedCell.support, basis, contextualBasis,
    ContextualGenerator.support, baseBasis]

def embedPure (old : HigherBasis original) {a b : Port signature} : {p q : Wiring signature a b} →
    {first second : Cartesian.ProofTrack p q} → Cartesian.Higher.UnitCritical.Cell first second →
    PresentedCell (basis old) (wireTrack first) (wireTrack second)
  | _, _, _, _, .refl path => .refl (wireTrack path)
  | _, _, _, _, .generator generator => .generator (.root (.pure generator))
  | _, _, _, _, .symm child => (embedPure old child).symm
  | _, _, _, _, .trans first second => (embedPure old first).trans (embedPure old second)
  | _, _, _, _, .comp first second => .comp (embedPure old first) (embedPure old second)
  | _, _, _, _, .inverse child => .inverse (embedPure old child)
  | _, _, _, _, .assoc p q r => .assoc (wireTrack p) (wireTrack q) (wireTrack r)
  | _, _, _, _, .leftUnit path => .leftUnit (wireTrack path)
  | _, _, _, _, .rightUnit path => .rightUnit (wireTrack path)
  | _, _, _, _, .leftInv path => .leftInv (wireTrack path)
  | _, _, _, _, .rightInv path => .rightInv (wireTrack path)

theorem embedPure_support (old : HigherBasis original) {a b} {p q : Wiring signature a b}
    {first second : Cartesian.ProofTrack p q} (cell : Cartesian.Higher.UnitCritical.Cell first second) :
    PresentedCell.support (embedPure old cell) = ∅ := by
  induction cell <;> simp_all only [embedPure, PresentedCell.support, basis, contextualBasis,
    ContextualGenerator.support, baseBasis, wireTrack_support, Finset.union_empty]

def unitCell (old : HigherBasis original) (a : Port signature) :=
  embedPure old (Cartesian.Higher.UnitCritical.unitCell a)

theorem unitCell_support (old : HigherBasis original) (a : Port signature) :
    PresentedCell.support (unitCell old a) = ∅ := embedPure_support _ _

theorem pure_context_support (old : HigherBasis original) {a b c d} {p q : Wiring signature a b}
    {first second : Cartesian.ProofTrack p q} (cell : Cartesian.Higher.UnitCritical.Cell first second)
    (place : Placement (signature := signature) a b c d) :
    PresentedCell.support ((embedPure old cell).whisker place) = place.needs := by
  rw [PresentedCell.whisker_support, embedPure_support, Finset.empty_union]

theorem pure_repaired_joint (oldBasis : HigherBasis original)
    {State Context : Type} {old updated : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : CheckedModel original updated Value State) {a b c d} {p q : Wiring signature a b}
    {first second : Cartesian.ProofTrack p q} (cell : Cartesian.Higher.UnitCritical.Cell first second)
    (place : Placement (signature := signature) a b c d) (changed : Finset Requirement)
    (cached : Holds old place.needs) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh place.needs changed))
    (law : PMF (Context × (State × Bundle Value c))) :
    ∃ left : Holds updated (place.apply (.wire p)).needs,
    ∃ right : Holds updated (place.apply (.wire q)).needs,
      law.bind (fun past => (evaluate model.base (place.apply (.wire p)) left past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (evaluate model.base (place.apply (.wire q)) right past.2.1 past.2.2).map (fun next => (past, next))) := by
  have cached' : Holds old (PresentedCell.support ((embedPure oldBasis cell).whisker place)) := by
    rw [pure_context_support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support ((embedPure oldBasis cell).whisker place)) changed) := by
    rw [pure_context_support]; exact rechecked
  exact cell_repaired_joint (checked model) ((embedPure oldBasis cell).whisker place)
    changed cached' unchanged rechecked' law

end CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion.CartesianUnitCritical
