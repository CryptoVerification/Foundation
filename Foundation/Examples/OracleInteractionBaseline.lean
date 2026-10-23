import Foundation.Crypto.Semantics.Oracle.InteractionRules

/-! Ordinary context congruence for mixed query/record/refresh interchange.
The local probability facts are shared. No Cell or certificate is imported.
-/
namespace CryptoOracle.ProofEdits.Interaction.Baseline
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Input Tag : Type} [DecidableEq Input] [Fintype Tag] [Nonempty Tag]

theorem exchange_context (front suffix : List (Action Input)) (first second : Action Input)
    (allowed : independent first second = true) (state : State Input Tag) :
    run (front ++ first :: second :: suffix) state = run (front ++ second :: first :: suffix) state := by
  rw [run_append, run_append]
  congr 1
  funext intermediate
  change (step first intermediate).bind (fun next => (step second next).bind (run suffix)) = _
  rw [← PMF.bind_bind, step_exchange first second allowed]
  exact PMF.bind_bind _ _ _

theorem mixed_block (message coordinate : Input) (different : message ≠ coordinate) (state : State Input Tag) :
    run [.refresh coordinate, .record message, .query message] state =
      run [.query message, .record message, .refresh coordinate] state := by
  calc
    _ = run [.record message, .refresh coordinate, .query message] state :=
      exchange_context [] [.query message] (.refresh coordinate) (.record message) rfl state
    _ = run [.record message, .query message, .refresh coordinate] state :=
      exchange_context [.record message] [] (.refresh coordinate) (.query message)
        (by simpa only [independent, decide_eq_true_eq] using different) state
    _ = _ := exchange_context [] [.refresh coordinate] (.record message) (.query message) rfl state

end CryptoOracle.ProofEdits.Interaction.Baseline
