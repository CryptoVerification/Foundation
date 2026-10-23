import Foundation.Examples.MixedCircuitSuffixOverlap

/-! MAC suffix completion alone does not restore global forward confluence.
The association/sequential-wire-fusion peak reaches two distinct irreducible
circuits even in the completed catalogue. This is not semantic inequality. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
open Foundation.Logic.Polygraph
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

def fusionSource (stage : Nat) := Circuit.seq
  (.seq (.wire (.identity (source (stage + 1)))) (.wire (.identity (source (stage + 1))))) (after stage)
def fusionDirect (stage : Nat) := Circuit.seq (.wire (.identity (source (stage + 1)))) (after stage)
def fusionAssociated (stage : Nat) := Circuit.seq (.wire (.identity (source (stage + 1))))
  (.seq (.wire (.identity (source (stage + 1)))) (after stage))

def fusionPath (stage : Nat) : Path (relators := @rules true) (fusionSource stage) (fusionDirect stage) :=
  .cons (.seqLeft (seqFusion _ _) _)
    (.cons (.seqLeft (wireChange (.root (.leftUnit _))) _) (.refl _))

def fusionAssocPath (stage : Nat) : Path (relators := @rules true) (fusionSource stage) (fusionAssociated stage) :=
  RewritePath.single (associate _ _ _)

theorem fusionDirect_stopped (stage : Nat) {target} (change : Step (@rules true) (fusionDirect stage) target) : False := by
  apply stopped_of_no_candidates (p := fusionDirect stage) (completed := true) (by
    simp [fusionDirect, after, candidates, profile, rootCandidate, StructuralTransport.Rewrite.composite]) change

theorem fusionAssociated_stopped (stage : Nat) {target} (change : Step (@rules true) (fusionAssociated stage) target) : False := by
  apply stopped_of_no_candidates (p := fusionAssociated stage) (completed := true) (by
    simp [fusionAssociated, after, candidates, profile, rootCandidate, StructuralTransport.Rewrite.composite]) change

theorem fusion_endpoints_distinct (stage : Nat) : fusionDirect stage ≠ fusionAssociated stage := by
  intro same
  have profiles := congrArg profile same
  cases profiles

theorem fusion_unjoinable (stage : Nat) :
    ¬ Nonempty (Σ destination,
      Path (relators := @rules true) (fusionDirect stage) destination ×
      Path (relators := @rules true) (fusionAssociated stage) destination) := by
  rintro ⟨⟨destination, first, second⟩⟩
  have one := first.terminal (fusionDirect_stopped stage)
  have two := second.terminal (fusionAssociated_stopped stage)
  exact fusion_endpoints_distinct stage (one.trans two.symm)

theorem fusion_kernel_equal {condition : Nat → Prop} {Value : signature.PortAtom → Type}
    (model : Model signature condition Value) (stage : Nat)
    (left : Holds condition (fusionDirect stage).needs) (right : Holds condition (fusionAssociated stage).needs)
    (input : Bundle Value (source (stage + 1))) :
    evaluate model (fusionDirect stage) left input = evaluate model (fusionAssociated stage) right input := by
  simp [fusionDirect, fusionAssociated, evaluate, StructuralTransport.Wire.eval, PMF.pure_bind]

def completedConfluent : Prop :=
  ∀ {a b} {p q r : Circuit signature a b}, Path (relators := @rules true) p q →
    Path (relators := @rules true) p r →
      Nonempty (Σ destination, Path (relators := @rules true) q destination × Path (relators := @rules true) r destination)

theorem completed_not_confluent : ¬ completedConfluent := by
  intro confluent
  exact fusion_unjoinable 0 (confluent (fusionPath 0) (fusionAssocPath 0))

/-- info: (2, 1, 0, 0) -/
#guard_msgs in
#eval ((fusionPath 0).length, (fusionAssocPath 0).length,
  candidates true (fusionDirect 0), candidates true (fusionAssociated 0))

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
