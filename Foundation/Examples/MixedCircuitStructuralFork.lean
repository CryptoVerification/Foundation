import Foundation.Examples.MixedCircuitStructuralRules

/-! A verified failure of naive directed confluence after adding association.
Both branches remain semantically sound. The local suffix completion joins
this peak, including post-copy and post-discard cases; global confluence of
the enlarged catalogue is not claimed. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

theorem direct_no_candidates (completed : Bool) (stage : Nat) {target} (wire : Wiring signature finish target)
    (leaf : Foundation.Logic.Polygraph.StructuralTransport.Rewrite.composite wire = false) :
    candidates completed (forkDirect stage wire) = 0 := by
  simp [forkDirect, after, candidates, profile, rootCandidate, leaf]

theorem associated_no_candidates (stage : Nat) {target} (wire : Wiring signature finish target)
    (leaf : Foundation.Logic.Polygraph.StructuralTransport.Rewrite.composite wire = false) :
    candidates false (forkAssociated stage wire) = 0 := by
  simp [forkAssociated, candidates, profile, rootCandidate, leaf]

theorem fork_distinct (stage : Nat) {target} (wire : Wiring signature finish target) :
    forkDirect stage wire ≠ forkAssociated stage wire := by
  intro same
  have shapes := congrArg profile same
  cases shapes

/-- Two irreducible descendants with different syntax cannot have a common
forward continuation, even with the eleven wire forms and fusion available. -/
theorem naive_unjoinable (stage : Nat) {target} (wire : Wiring signature finish target)
    (leaf : Foundation.Logic.Polygraph.StructuralTransport.Rewrite.composite wire = false) :
    ¬ Nonempty (Σ destination, Path (relators := @rules false) (forkDirect stage wire) destination ×
      Path (relators := @rules false) (forkAssociated stage wire) destination) := by
  rintro ⟨⟨destination, first, second⟩⟩
  have one := Path.terminal first (stopped_of_no_candidates (direct_no_candidates false stage wire leaf))
  have two := Path.terminal second (stopped_of_no_candidates (associated_no_candidates stage wire leaf))
  exact fork_distinct stage wire (one.trans two.symm)

theorem not_root_rigid : ¬ RootRigid (@rules false) := by
  intro rigid
  have result := rigid
    (Primitive.rule (Rule.assoc (completed := false)
      (.box (signature := signature) (MACNormalization.Atom.schedule 0))
      (.box (signature := signature) (MACNormalization.Atom.eliminate 0)) (.wire copy)))
    (cryptoFirst false 0 copy)
  exact fork_distinct 0 copy result.1

/-- A bounded joining diagram for this actual mixed critical peak. -/
def completedJoin (stage : Nat) {target} (wire : Wiring signature finish target) :
    LocalJoin (cryptoFirst true stage wire) (assocFirst true stage wire) where
  target := forkDirect stage wire
  afterFirst := .refl _
  afterSecond := RewritePath.single (completedResidual stage wire)
  covered := by
    constructor <;> intro label member
    all_goals
      simp [cryptoFirst, assocFirst, completedResidual, forkSource, forkDirect, forkAssociated,
        Path.support, RewritePath.single, Step.support, Primitive.support, Relator.support,
        rules, MAC.relators, before, after, Circuit.needs, signature, MACNormalization.layout] at member ⊢
      tauto

/-- info: (0, 0, 2, 2, 0, 1) -/
#guard_msgs in
#eval (candidates false (forkDirect 0 copy), candidates false (forkAssociated 0 copy),
  (cryptoFirst false 0 copy).support.card, (completedResidual 0 copy).support.card,
  (completedJoin 0 copy).afterFirst.length, (completedJoin 0 copy).afterSecond.length)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
