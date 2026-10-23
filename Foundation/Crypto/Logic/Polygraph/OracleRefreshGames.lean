import Foundation.Crypto.Logic.Polygraph.OracleRefreshCells
import Foundation.Crypto.Logic.Polygraph.GameCoherence

/-! Interpret restricted refresh diagrams in the existing directed game
layer. The event here observes the retained past. A future verifier may
inspect the final function through Cell.continuation, without pretending
that an arbitrary event is pointwise unchanged by a refresh.
-/
namespace CryptoOracle.ProofEdits.Refresh.Games
open Foundation.Probability CryptoOracle.RandomOracle CryptoOracle.RandomOracle.Posterior
open CryptoLogic.Polygraph.Experiment CryptoLogic.Polygraph.Experiment.GameCoherence
set_option backward.isDefEq.respectTransparency false
variable {Index Input Tag History : Type} [DecidableEq Input]
  [Fintype Input] [Fintype Tag] [Nonempty Tag]

noncomputable def game (history : PMF History) (table : History → Table Input Tag)
    (event : History → Prop) : Observed :=
  ⟨History × (Input → Tag), .sample (retained history table), fun state => event state.1⟩

noncomputable def transition (history : PMF History) (table : History → Table Input Tag)
    (event : History → Prop) (coordinate : Index → History → Input) (index : Index)
    (fresh : ∀ past ∈ history.support, (table past).lookup (coordinate index past) = none) :
    Step (game history table event) (game history table event) where
  kernel := step coordinate index
  preserve := step_preserve history table coordinate index fresh
  bad _ := False
  agree state _ final selected _ := by
    rw [step, PMF.mem_support_map_iff] at selected
    obtain ⟨tag, _, rfl⟩ := selected
    exact Iff.rfl
  loss := 0
  bound := by simp [eventProb]

noncomputable def interpret (history : PMF History) (table : History → Table Input Tag)
    (event : History → Prop) (coordinate : Index → History → Input) :
    (word : List Index) →
    (∀ index ∈ word, ∀ past ∈ history.support, (table past).lookup (coordinate index past) = none) →
    Path (game history table event) (game history table event)
  | [], _ => .identity _
  | index :: tail, fresh => .seq (.step (transition history table event coordinate index (fresh index (by simp))))
      (interpret history table event coordinate tail (fun index member => fresh index (List.mem_cons_of_mem _ member)))

theorem interpret_kernel (history : PMF History) (table : History → Table Input Tag)
    (event : History → Prop) (coordinate : Index → History → Input) (word : List Index)
    (fresh : ∀ index ∈ word, ∀ past ∈ history.support, (table past).lookup (coordinate index past) = none)
    (state : History × (Input → Tag)) :
    (interpret history table event coordinate word fresh).kernel state = run coordinate word state := by
  induction word generalizing state with
  | nil => rfl
  | cons index tail ih =>
      simp only [interpret, Path.kernel, transition, run]
      congr 1
      funext next
      exact ih _ next

theorem interpret_loss (history : PMF History) (table : History → Table Input Tag)
    (event : History → Prop) (coordinate : Index → History → Input) (word : List Index)
    (fresh : ∀ index ∈ word, ∀ past ∈ history.support, (table past).lookup (coordinate index past) = none) :
    (interpret history table event coordinate word fresh).loss = 0 := by
  induction word with
  | nil => rfl
  | cons index tail ih => simpa only [interpret, Path.loss, transition, zero_add] using ih _

theorem interpret_joint (history : PMF History) (table : History → Table Input Tag)
    (event : History → Prop) (coordinate : Index → History → Input) (word : List Index)
    (fresh : ∀ index ∈ word, ∀ past ∈ history.support, (table past).lookup (coordinate index past) = none) :
    (interpret history table event coordinate word fresh).joint = joint history table coordinate word := by
  simp only [Path.joint, interpret_kernel, joint]
  rfl

/-- This compiler's only input comparison is a restricted syntactic Cell.
The broad semantic generator in the target library is not an input rule. -/
noncomputable def interpret_cell (history : PMF History) (table : History → Table Input Tag)
    (event : History → Prop) (coordinate : Index → History → Input) {first second : List Index}
    (cell : Cell first second)
    (firstFresh : ∀ index ∈ first, ∀ past ∈ history.support, (table past).lookup (coordinate index past) = none)
    (secondFresh : ∀ index ∈ second, ∀ past ∈ history.support, (table past).lookup (coordinate index past) = none) :
    Cell4 (interpret history table event coordinate first firstFresh)
      (interpret history table event coordinate second secondFresh) :=
  .generator ⟨fun state => by rw [interpret_kernel, interpret_kernel]; exact cell.sound coordinate state,
    by rw [interpret_loss, interpret_loss]⟩

end CryptoOracle.ProofEdits.Refresh.Games
