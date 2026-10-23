import Foundation.Crypto.Semantics.Oracle.Refresh

/-! Ordinary permutation induction for the same chosen-kernel and joint-law
goals. Imports neither the refresh Cell syntax nor its checker/game compiler.
The conditional sampling laws are shared freely by both approaches.
-/
namespace CryptoOracle.ProofEdits.Refresh.Baseline
open Foundation.Probability CryptoOracle.RandomOracle CryptoOracle.RandomOracle.Posterior
set_option backward.isDefEq.respectTransparency false
variable {Index Input Tag History : Type} [DecidableEq Input] [Fintype Tag] [Nonempty Tag]

theorem run_perm (coordinate : Index → History → Input) {first second : List Index}
    (permutation : first.Perm second) (state : History × (Input → Tag)) :
    run coordinate first state = run coordinate second state := by
  induction permutation generalizing state with
  | nil => rfl
  | cons index permutation ih =>
      exact congrArg (PMF.bind (step coordinate index state)) (funext ih)
  | swap first second tail =>
      change (step coordinate second state).bind (fun next =>
        (step coordinate first next).bind (run coordinate tail)) = _
      rw [← PMF.bind_bind, step_exchange]
      exact PMF.bind_bind _ _ _
  | trans first second ihFirst ihSecond => exact (ihFirst state).trans (ihSecond state)

theorem continuation {Result : Type} (coordinate : Index → History → Input) {first second : List Index}
    (permutation : first.Perm second) (next : (History × (Input → Tag)) → PMF Result)
    (state : History × (Input → Tag)) :
    (run coordinate first state).bind next = (run coordinate second state).bind next := by
  rw [run_perm coordinate permutation]

variable [Fintype Input]

theorem joint_eq (history : PMF History) (table : History → Table Input Tag)
    (coordinate : Index → History → Input) {first second : List Index} (permutation : first.Perm second) :
    joint history table coordinate first = joint history table coordinate second := by
  unfold joint
  simp_rw [run_perm coordinate permutation]

end CryptoOracle.ProofEdits.Refresh.Baseline
