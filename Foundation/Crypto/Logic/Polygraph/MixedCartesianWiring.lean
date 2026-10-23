import Foundation.Logic.Polygraph.StructuralCartesianRewriting
import Foundation.Crypto.Logic.Polygraph.MixedCircuitContextualHigher

/-! The complete first-level typed cartesian wiring presentation inside opaque
probabilistic-box contexts. Structural roots add no guards. This standalone
pure-rewrite catalogue is not a completed union with all cryptographic rules. -/
namespace CryptoLogic.Polygraph.MixedCircuit.CartesianWiring
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
variable {Box Requirement Budget : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget}
set_option backward.isDefEq.respectTransparency false

inductive Rule (signature : Signature Box Requirement Budget) where
  | wire {a b : Port signature} {p q : Wiring signature a b} (change : Cartesian.Step p q)

def relators : Rule signature → Relator signature
  | .wire (p := p) (q := q) _ => ⟨_, _, .wire p, .wire q, ∅, rfl⟩

noncomputable def checkedModel {condition : Requirement → Prop} {Value : signature.PortAtom → Type}
    (base : Model signature condition Value) : CheckedModel relators condition Value where
  base := base
  localSound := by
    intro label valid input
    cases label with
    | wire change => exact congrArg PMF.pure (change.sound Value input)

def liftStep {a b} {p q : Wiring signature a b} (change : Cartesian.Step p q) :
    Step relators (.wire p) (.wire q) := .root (.rule (relators := relators) (Rule.wire change))

def liftTrack {a b} {p q : Wiring signature a b} (path : Cartesian.ProofTrack p q) :
    RewriteTrack (relators := relators) (.wire p) (.wire q) :=
  path.map Circuit.wire (fun change => liftStep change)

theorem liftTrack_support {a b} {p q : Wiring signature a b} (path : Cartesian.ProofTrack p q) :
    RewriteTrack.support (liftTrack path) = ∅ := by
  induction path <;> simp_all only [liftTrack, Track.map, RewriteTrack.support,
    liftStep, Step.support, Primitive.support, Relator.support, relators, Circuit.needs, Finset.union_empty]

def certificate {a b} {p q : Wiring signature a b} (proof : Cartesian.Cell p q) :
    RewriteTrack (relators := relators) (.wire p) (.wire q) := liftTrack proof.toTrack

def normalization {a b} (wire : Wiring signature a b) :
    RewriteTrack (relators := relators) (.wire wire) (.wire (Cartesian.reify (TypedRouting.normal wire))) :=
  certificate (Cartesian.normalizeCell wire)

theorem normalization_support {a b} (wire : Wiring signature a b) :
    RewriteTrack.support (normalization wire) = ∅ := liftTrack_support _

theorem contextual_support {a b c d} (wire : Wiring signature a b) (place : Placement (signature := signature) a b c d) :
    RewriteTrack.support (place.track (normalization wire)) = place.needs := by
  rw [Placement.track_support, normalization_support, Finset.empty_union]

theorem normalized_repaired_joint {old updated : Requirement → Prop} {Value : signature.PortAtom → Type} {Context : Type}
    (base : Model signature updated Value) {a b c d} (wire : Wiring signature a b)
    (place : Placement (signature := signature) a b c d) (changed : Finset Requirement)
    (cached : Holds old place.needs) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh place.needs changed)) (law : PMF (Context × Bundle Value c)) :
    ∃ left : Holds updated (place.apply (.wire wire)).needs,
    ∃ right : Holds updated (place.apply (.wire (Cartesian.reify (TypedRouting.normal wire)))).needs,
      law.bind (fun past => (evaluate base (place.apply (.wire wire)) left past.2).map (fun next => (past, next))) =
        law.bind (fun past => (evaluate base (place.apply (.wire (Cartesian.reify (TypedRouting.normal wire)))) right past.2).map (fun next => (past, next))) := by
  let path := place.track (normalization wire)
  have valid : Holds updated (RewriteTrack.support path) := by
    rw [contextual_support]
    exact repair cached unchanged rechecked
  let left := valid.restrict path.boundaries.1
  let right := valid.restrict path.boundaries.2
  refine ⟨left, right, ?_⟩
  apply congrArg (fun continuation => law.bind continuation)
  funext past
  exact congrArg (PMF.map (fun next => (past, next))) (path.sound (checkedModel base) valid left right past.2)

end CryptoLogic.Polygraph.MixedCircuit.CartesianWiring
