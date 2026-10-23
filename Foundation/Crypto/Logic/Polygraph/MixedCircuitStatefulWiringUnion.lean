import Foundation.Crypto.Logic.Polygraph.MixedCircuitStatefulHigher
import Foundation.Crypto.Logic.Polygraph.MixedCartesianLocalHigher

/-! A common rule catalogue for checked stateful roots and the complete
first-level 18-law cartesian wiring presentation. Existing local higher roots,
pure local roots and separated cross exchanges are retained explicitly.
Nested cross critical overlaps are not assumed covered by this partial basis. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion
open Foundation.Probability
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false
variable {Box Requirement Budget Rule State : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget}

abbrev Label (signature : Signature Box Requirement Budget) (Rule : Type) := Rule ⊕ CartesianWiring.Rule signature

def rules (original : Rule → Relator signature) : Label signature Rule → Relator signature
  | .inl label => original label
  | .inr label => CartesianWiring.relators label

noncomputable def checked {condition : Requirement → Prop} {Value : signature.PortAtom → Type}
    {original : Rule → Relator signature} (model : CheckedModel original condition Value State) :
    CheckedModel (rules original) condition Value State where
  base := model.base
  localSound := by
    intro label valid state input
    cases label with
    | inl label => exact model.localSound label valid state input
    | inr label => cases label with
      | wire change => exact congrArg (fun value => PMF.pure (state, value)) (change.sound Value input)

variable {original : Rule → Relator signature}

def embedStep : {a b : Port signature} → {p q : Circuit signature a b} → Step original p q → Step (rules original) p q
  | _, _, _, _, .root (.rule label) => .root (.rule (relators := rules original) (Sum.inl label))
  | _, _, _, _, .seqLeft change fixed => .seqLeft (embedStep change) fixed
  | _, _, _, _, .seqRight fixed change => .seqRight fixed (embedStep change)
  | _, _, _, _, .tensorLeft change fixed => .tensorLeft (embedStep change) fixed
  | _, _, _, _, .tensorRight fixed change => .tensorRight fixed (embedStep change)

def embedTrack {a b : Port signature} : {p q : Circuit signature a b} →
    RewriteTrack (relators := original) p q → RewriteTrack (relators := rules original) p q
  | _, _, .refl p => .refl p
  | _, _, .step change => .step (embedStep change)
  | _, _, .comp first second => .comp (embedTrack first) (embedTrack second)
  | _, _, .inv child => .inv (embedTrack child)

theorem embedStep_support {a b} {p q : Circuit signature a b} (change : Step original p q) :
    (embedStep change).support = change.support := by
  induction change with
  | root primitive => cases primitive; rfl
  | seqLeft change fixed ih | seqRight fixed change ih | tensorLeft change fixed ih | tensorRight fixed change ih =>
      simp only [embedStep, Step.support, ih]

theorem embedTrack_support {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := original) p q) :
    RewriteTrack.support (embedTrack path) = RewriteTrack.support path := by
  induction path <;> simp_all only [embedTrack, RewriteTrack.support, embedStep_support]

def wireStep {a b} {p q : Wiring signature a b} (change : Cartesian.Step p q) :
    Step (rules original) (.wire p) (.wire q) := .root (.rule (relators := rules original) (Sum.inr (CartesianWiring.Rule.wire change)))

def wireTrack {a b} {p q : Wiring signature a b} (path : Cartesian.ProofTrack p q) :
    RewriteTrack (relators := rules original) (.wire p) (.wire q) :=
  path.map Circuit.wire (fun change => wireStep change)

theorem wireTrack_support {a b} {p q : Wiring signature a b} (path : Cartesian.ProofTrack p q) :
    RewriteTrack.support (wireTrack (original := original) path) = ∅ := by
  induction path <;> simp_all only [wireTrack, Track.map, RewriteTrack.support,
    wireStep, Step.support, Primitive.support, Relator.support, rules, CartesianWiring.relators,
    Circuit.needs, Finset.union_empty]

def normalize {a b} (wire : Wiring signature a b) :
    RewriteTrack (relators := rules original) (.wire wire) (.wire (Cartesian.reify (TypedRouting.normal wire))) :=
  wireTrack (Cartesian.normalizeCell wire).toTrack

theorem normalize_support {a b} (wire : Wiring signature a b) :
    RewriteTrack.support (normalize (original := original) wire) = ∅ := wireTrack_support _

/-- Generator inputs are existing generators, single pure local generators,
or separated two-step squares. Arbitrary parallel higher cells are not roots. -/
inductive Generator (basis : HigherBasis original) : {a b : Port signature} → {p q : Circuit signature a b} →
    RewriteTrack (relators := rules original) p q → RewriteTrack (relators := rules original) p q → Type where
  | existing {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := original) p q}
      (generator : basis.Generator first second) : Generator basis (embedTrack first) (embedTrack second)
  | pure {a b} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
      (generator : Cartesian.Higher.Generator first second) : Generator basis (wireTrack first) (wireTrack second)
  | separated {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := rules original) p q}
      (generator : Exchange first second) : Generator basis first second

def baseBasis (basis : HigherBasis original) : HigherBasis (rules original) where
  Generator := Generator basis
  requirements := fun generator => match generator with
    | .existing generator => basis.requirements generator
    | .pure _ => ∅
    | .separated generator => generator.support
  covered := by
    intro a b p q first second generator
    cases generator with
    | existing generator => simpa only [embedTrack_support] using basis.covered generator
    | pure generator => simp only [wireTrack_support]; exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
    | separated generator => exact generator.boundaries

def basis (old : HigherBasis original) : HigherBasis (rules original) := contextualBasis (baseBasis old)

def embedCell {old : HigherBasis original} {a b} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := original) p q} → PresentedCell old first second →
      PresentedCell (basis old) (embedTrack first) (embedTrack second)
  | _, _, _, _, .refl path => .refl (embedTrack path)
  | _, _, _, _, .generator generator => .generator (.root (.existing generator))
  | _, _, _, _, .symm child => (embedCell child).symm
  | _, _, _, _, .trans first second => (embedCell first).trans (embedCell second)
  | _, _, _, _, .comp first second => .comp (embedCell first) (embedCell second)
  | _, _, _, _, .inverse child => .inverse (embedCell child)
  | _, _, _, _, .assoc p q r => .assoc (embedTrack p) (embedTrack q) (embedTrack r)
  | _, _, _, _, .leftUnit p => .leftUnit (embedTrack p)
  | _, _, _, _, .rightUnit p => .rightUnit (embedTrack p)
  | _, _, _, _, .leftInv p => .leftInv (embedTrack p)
  | _, _, _, _, .rightInv p => .rightInv (embedTrack p)

theorem embedCell_support {old : HigherBasis original} {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := original) p q} (cell : PresentedCell old first second) :
    PresentedCell.support (embedCell cell) = PresentedCell.support cell := by
  induction cell <;> simp_all only [embedCell, PresentedCell.support, basis, contextualBasis,
    ContextualGenerator.support, baseBasis, embedTrack_support]

theorem embedCell_count {old : HigherBasis original} {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := original) p q} (cell : PresentedCell old first second) :
    PresentedCell.constructorCount (embedCell cell) = PresentedCell.constructorCount cell := by
  induction cell <;> simp_all only [embedCell, PresentedCell.constructorCount]

def embedPure {old : HigherBasis original} {a b : Port signature} : {p q : Wiring signature a b} →
    {first second : Cartesian.ProofTrack p q} → Cartesian.Higher.Homotopy first second →
      PresentedCell (basis old) (wireTrack first) (wireTrack second)
  | _, _, _, _, .refl path => .refl (wireTrack path)
  | _, _, _, _, .generator generator => .generator (.root (.pure generator))
  | _, _, _, _, .symm child => (embedPure child).symm
  | _, _, _, _, .trans first second => (embedPure first).trans (embedPure second)
  | _, _, _, _, .comp first second => .comp (embedPure first) (embedPure second)
  | _, _, _, _, .inverse child => .inverse (embedPure child)
  | _, _, _, _, .assoc p q r => .assoc (wireTrack p) (wireTrack q) (wireTrack r)
  | _, _, _, _, .leftUnit p => .leftUnit (wireTrack p)
  | _, _, _, _, .rightUnit p => .rightUnit (wireTrack p)
  | _, _, _, _, .leftInv p => .leftInv (wireTrack p)
  | _, _, _, _, .rightInv p => .rightInv (wireTrack p)

theorem embedPure_support {old : HigherBasis original} {a b : Port signature} {p q : Wiring signature a b}
    {first second : Cartesian.ProofTrack p q} (cell : Cartesian.Higher.Homotopy first second) :
    PresentedCell.support (embedPure (old := old) cell) = ∅ := by
  induction cell <;> simp_all only [embedPure, PresentedCell.support, basis, contextualBasis,
    ContextualGenerator.support, baseBasis, wireTrack_support, Finset.union_empty]

theorem embedPure_count {old : HigherBasis original} {a b : Port signature} {p q : Wiring signature a b}
    {first second : Cartesian.ProofTrack p q} (cell : Cartesian.Higher.Homotopy first second) :
    PresentedCell.constructorCount (embedPure (old := old) cell) = Cartesian.Higher.Homotopy.constructorCount cell := by
  induction cell <;> simp_all only [embedPure, PresentedCell.constructorCount, Cartesian.Higher.Homotopy.constructorCount]

theorem normalization_context_support {a b c d} (wire : Wiring signature a b)
    (place : Placement (signature := signature) a b c d) :
    RewriteTrack.support (place.track (normalize (original := original) wire)) = place.needs := by
  rw [Placement.track_support, normalize_support, Finset.empty_union]

theorem normalization_repaired_joint {old updated : Requirement → Prop} {Value : signature.PortAtom → Type} {Context : Type}
    (model : CheckedModel original updated Value State) {a b c d} (wire : Wiring signature a b)
    (place : Placement (signature := signature) a b c d) (changed : Finset Requirement)
    (cached : Holds old place.needs) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh place.needs changed))
    (law : PMF (Context × (State × Bundle Value c))) :
    ∃ left : Holds updated (place.apply (.wire wire)).needs,
    ∃ right : Holds updated (place.apply (.wire (Cartesian.reify (TypedRouting.normal wire)))).needs,
      law.bind (fun past => (evaluate model.base (place.apply (.wire wire)) left past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (evaluate model.base (place.apply (.wire (Cartesian.reify (TypedRouting.normal wire)))) right past.2.1 past.2.2).map (fun next => (past, next))) := by
  let path := place.track (normalize (original := original) wire)
  have valid : Holds updated (RewriteTrack.support path) := by
    rw [normalization_context_support]
    exact repair cached unchanged rechecked
  refine ⟨valid.restrict path.boundaries.1, valid.restrict path.boundaries.2, ?_⟩
  exact track_joint (checked model) path valid _ _ law

/- Adding the full wire catalogue retains its unrestricted expansion loop.
The recursive normalizer does not imply termination of all forward rewrites. -/
omit [DecidableEq Requirement] in
theorem unrestricted_not_terminating (shape : Port signature) :
    ¬ WellFounded (fun q p : Circuit signature shape (.pair shape shape) =>
      Nonempty (Step (rules original) p q)) := by
  intro wellFounded
  have impossible : ∀ (p : Circuit signature shape (.pair shape shape)),
      Acc (fun q p => Nonempty (Step (rules original) p q)) p →
        ∀ n, p = .wire (Cartesian.copyChain shape n) → False := by
    intro p accessible
    induction accessible with
    | intro p predecessors ih =>
        intro n same
        subst p
        exact ih _ ⟨wireStep (Cartesian.copyChainStep shape n)⟩ (n + 1) rfl
  exact impossible _ (wellFounded.apply _) 0 rfl

end CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion
