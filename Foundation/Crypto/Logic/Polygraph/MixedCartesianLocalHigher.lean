import Foundation.Logic.Polygraph.StructuralCartesianLocalHigher
import Foundation.Crypto.Logic.Polygraph.MixedCartesianWiring

/-! Local pure cartesian higher diagrams in probabilistic-box contexts.
Only explicit pure generators are imported, never arbitrary whole higher cells.
Their guard support is empty; surrounding mixed contexts retain their guards.
No global higher completeness or resource-preserving duplication is claimed. -/
namespace CryptoLogic.Polygraph.MixedCircuit.CartesianWiring.Higher
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
variable {Box Requirement Budget : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget}
set_option backward.isDefEq.respectTransparency false

inductive Generator : {a b : Port signature} → {p q : Circuit signature a b} →
    RewriteTrack (relators := relators) p q → RewriteTrack (relators := relators) p q → Type where
  | structural {a b} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
      (generator : Cartesian.Higher.Generator first second) : Generator (liftTrack first) (liftTrack second)

def baseBasis : HigherBasis (relators (signature := signature)) where
  Generator := Generator
  requirements := fun _ => ∅
  covered := by
    intro a b p q first second generator
    cases generator
    simp only [liftTrack_support]
    exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

def basis : HigherBasis (relators (signature := signature)) := contextualBasis baseBasis
abbrev Cell {a b} {p q : Circuit signature a b} (first second : RewriteTrack (relators := relators) p q) :=
  PresentedCell basis first second

def embedPure {a b : Port signature} : {p q : Wiring signature a b} → {first second : Cartesian.ProofTrack p q} →
    Cartesian.Higher.Homotopy first second → Cell (liftTrack first) (liftTrack second)
  | _, _, _, _, .refl path => .refl (liftTrack path)
  | _, _, _, _, .generator generator => .generator (.root (.structural generator))
  | _, _, _, _, .symm child => (embedPure child).symm
  | _, _, _, _, .trans first second => (embedPure first).trans (embedPure second)
  | _, _, _, _, .comp first second => .comp (embedPure first) (embedPure second)
  | _, _, _, _, .inverse child => .inverse (embedPure child)
  | _, _, _, _, .assoc p q r => .assoc (liftTrack p) (liftTrack q) (liftTrack r)
  | _, _, _, _, .leftUnit p => .leftUnit (liftTrack p)
  | _, _, _, _, .rightUnit p => .rightUnit (liftTrack p)
  | _, _, _, _, .leftInv p => .leftInv (liftTrack p)
  | _, _, _, _, .rightInv p => .rightInv (liftTrack p)

theorem embedPure_support {a b : Port signature} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (cell : Cartesian.Higher.Homotopy first second) : PresentedCell.support (embedPure cell) = ∅ := by
  induction cell <;> simp_all only [embedPure, PresentedCell.support, basis, contextualBasis,
    ContextualGenerator.support, baseBasis, liftTrack_support, Finset.union_empty]

theorem embedPure_constructorCount {a b : Port signature} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (cell : Cartesian.Higher.Homotopy first second) :
    PresentedCell.constructorCount (embedPure cell) = Cartesian.Higher.Homotopy.constructorCount cell := by
  induction cell <;> simp_all only [embedPure, PresentedCell.constructorCount, Cartesian.Higher.Homotopy.constructorCount]

def inContext {a b c d : Port signature} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (place : Placement (signature := signature) a b c d) (cell : Cartesian.Higher.Homotopy first second) :=
  (embedPure cell).whisker place

theorem inContext_support {a b c d : Port signature} {p q : Wiring signature a b} {first second : Cartesian.ProofTrack p q}
    (place : Placement (signature := signature) a b c d) (cell : Cartesian.Higher.Homotopy first second) :
    PresentedCell.support (inContext place cell) = place.needs := by
  rw [inContext, PresentedCell.whisker_support, embedPure_support, Finset.empty_union]

theorem inContext_repaired_joint {old updated : Requirement → Prop} {Value : signature.PortAtom → Type} {Context : Type}
    (base : Model signature updated Value) {a b c d : Port signature} {p q : Wiring signature a b}
    {first second : Cartesian.ProofTrack p q} (place : Placement (signature := signature) a b c d)
    (cell : Cartesian.Higher.Homotopy first second) (changed : Finset Requirement)
    (cached : Holds old place.needs) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh place.needs changed)) (law : PMF (Context × Bundle Value c)) :
    ∃ left : Holds updated (place.apply (.wire p)).needs, ∃ right : Holds updated (place.apply (.wire q)).needs,
      law.bind (fun past => (evaluate base (place.apply (.wire p)) left past.2).map (fun next => (past, next))) =
        law.bind (fun past => (evaluate base (place.apply (.wire q)) right past.2).map (fun next => (past, next))) := by
  have cached' : Holds old (PresentedCell.support (inContext place cell)) := by rw [inContext_support]; exact cached
  have rechecked' : Holds updated (fresh (PresentedCell.support (inContext place cell)) changed) := by rw [inContext_support]; exact rechecked
  exact (inContext place cell).repaired_joint (checkedModel base) changed cached' unchanged rechecked' law

theorem discardedInContext_constructorBound {u v c d : Port signature} {p q : Wiring signature u v}
    (place : Placement (signature := signature) u .unit c d) (first second : Cartesian.ProofTrack p q) :
    PresentedCell.constructorCount (inContext place (Cartesian.Higher.Homotopy.discardedParallel first second)) ≤
      23 + 12 * (Cartesian.Higher.trackConstructorCount first + Cartesian.Higher.trackConstructorCount second) := by
  rw [inContext, PresentedCell.whisker_constructorCount, embedPure_constructorCount]
  exact Cartesian.Higher.Homotopy.discardedParallel_constructorBound first second

end CryptoLogic.Polygraph.MixedCircuit.CartesianWiring.Higher
