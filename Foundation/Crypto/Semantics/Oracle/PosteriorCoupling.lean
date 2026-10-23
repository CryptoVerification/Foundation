import Foundation.Crypto.Semantics.Oracle.RandomOracleFinite
import Foundation.Crypto.Semantics.Oracle.RandomOracleValues

/-! Keeping a sampled finite function and independently reconstructing one
from the same partial cache give equal one-sided laws but different joint
laws. These are proof couplings, not programming operations available to an
oracle adversary. The history type can include the full adaptive outcome.
-/
namespace CryptoOracle.RandomOracle.Posterior
open Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {Input Tag History : Type} [DecidableEq Input]
  [Fintype Input] [Fintype Tag] [Nonempty Tag]

noncomputable def reserve (table : Table Input Tag) : PMF (Input → Tag) :=
  (uniform (Input → Tag)).map (complete table)

noncomputable def retained (history : PMF History) (table : History → Table Input Tag) :=
  history.bind fun past => (reserve (table past)).map fun function => (past, function)

noncomputable def shared (history : PMF History) (table : History → Table Input Tag) :=
  (retained history table).map fun pair => (pair.1, pair.2, pair.2)

noncomputable def reconstructed (history : PMF History) (table : History → Table Input Tag) :=
  (retained history table).bind fun pair =>
    (reserve (table pair.1)).map fun function => (pair.1, pair.2, function)

theorem shared_left (history : PMF History) (table : History → Table Input Tag) :
    (shared history table).map (fun triple => (triple.1, triple.2.1)) = retained history table := by
  simp only [shared, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

theorem shared_right (history : PMF History) (table : History → Table Input Tag) :
    (shared history table).map (fun triple => (triple.1, triple.2.2)) = retained history table := by
  simp only [shared, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

theorem reconstructed_left (history : PMF History) (table : History → Table Input Tag) :
    (reconstructed history table).map (fun triple => (triple.1, triple.2.1)) = retained history table := by
  simp only [reconstructed, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change ((retained history table).bind fun pair =>
    (reserve (table pair.1)).map (Function.const _ pair)) = _
  simp only [PMF.map_const, PMF.bind_pure]

theorem reconstructed_right (history : PMF History) (table : History → Table Input Tag) :
    (reconstructed history table).map (fun triple => (triple.1, triple.2.2)) = retained history table := by
  simp [reconstructed, retained, PMF.map_bind, PMF.map_comp, PMF.bind_map, PMF.bind_bind,
    Function.comp_def, PMF.bind_const]

theorem reserve_fresh (table : Table Input Tag) (input : Input)
    (fresh : table.lookup input = none) :
    (reserve table).map (fun function => function input) = uniform Tag := by
  simp only [reserve, PMF.map_comp, Function.comp_def, complete, fresh, Option.getD_none]
  have split := uniform_function_fresh input
    (fun (value : Tag) (_ : Input → Tag) => PMF.pure value) (by intro function value; rfl)
  simpa only [PMF.bind_const, PMF.map, Function.comp_def, PMF.bind_pure] using split

theorem reserve_known (table : Table Input Tag) (input : Input) (tag : Tag)
    (known : table.lookup input = some tag) (function : Input → Tag)
    (supported : function ∈ (reserve table).support) : function input = tag := by
  rw [reserve, PMF.mem_support_map_iff] at supported
  obtain ⟨rest, _, rfl⟩ := supported
  simp [complete, known]

theorem event_bind_constant {A B : Type} (law : PMF A) (next : A → PMF B)
    (event : B → Prop) (value : ℝ≥0∞)
    (constant : ∀ a ∈ law.support, eventProb (next a) event = value) :
    eventProb (law.bind next) event = value := by
  rw [eventProb_bind_eq]
  calc
    _ = ∑' a, law a * value := by
      apply tsum_congr
      intro a
      by_cases zero : law a = 0
      · simp [zero]
      · rw [constant a ((PMF.mem_support_iff _ _).mpr zero)]
    _ = value := by rw [ENNReal.tsum_mul_right, law.tsum_coe, one_mul]

/-- Equality at an adaptively selected, unqueried coordinate survives
independent reconstruction with probability exactly one over the alphabet.
The old function is retained in the joint outcome, not discarded. -/
theorem reconstructed_agreement (history : PMF History) (table : History → Table Input Tag)
    (choose : History → Input)
    (fresh : ∀ past ∈ history.support, (table past).lookup (choose past) = none) :
    eventProb (reconstructed history table)
      (fun triple => triple.2.1 (choose triple.1) = triple.2.2 (choose triple.1)) =
      (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  apply event_bind_constant
  intro pair supported
  rw [retained, PMF.mem_support_bind_iff] at supported
  obtain ⟨past, reachable, supported⟩ := supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨function, _, rfl⟩ := supported
  rw [eventProb_map]
  have value := congrArg (fun law => eventProb law (· = function (choose past)))
    (reserve_fresh (table past) (choose past) (fresh past reachable))
  rw [eventProb_map, uniform_guess] at value
  simpa only [eq_comm] using value

theorem shared_agreement (history : PMF History) (table : History → Table Input Tag)
    (choose : History → Input) :
    eventProb (shared history table)
      (fun triple => triple.2.1 (choose triple.1) = triple.2.2 (choose triple.1)) = 1 := by
  rw [shared, eventProb_map]
  simp only [eventProb, Set.ofPred_true]
  rw [PMF.toOuterMeasure_apply]
  simp

/-- A marginally correct reconstruction is not a coherent identity on the
chosen joint witness when at least one fresh nontrivial coordinate remains. -/
theorem reconstructed_ne_shared (history : PMF History) (table : History → Table Input Tag)
    (choose : History → Input)
    (fresh : ∀ past ∈ history.support, (table past).lookup (choose past) = none)
    (nontrivial : (Fintype.card Tag : ℝ≥0∞)⁻¹ ≠ 1) :
    reconstructed history table ≠ shared history table := by
  intro same
  have agreement := reconstructed_agreement history table choose fresh
  rw [same, shared_agreement] at agreement
  exact nontrivial agreement.symm

/-- An arbitrary reconstruction procedure may inspect the full history and
use its own randomness, but receives no retained copy of the original reserve. -/
noncomputable def reconstructWith (history : PMF History) (table : History → Table Input Tag)
    (restore : History → PMF (Input → Tag)) :=
  history.bind fun past => (reserve (table past)).bind fun original =>
    (restore past).map fun replacement => (past, original, replacement)

theorem reconstructWith_agreement (history : PMF History) (table : History → Table Input Tag)
    (restore : History → PMF (Input → Tag)) (choose : History → Input)
    (fresh : ∀ past ∈ history.support, (table past).lookup (choose past) = none) :
    eventProb (reconstructWith history table restore)
      (fun triple => triple.2.1 (choose triple.1) = triple.2.2 (choose triple.1)) =
      (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  apply event_bind_constant
  intro past reachable
  simp only [PMF.map]
  rw [PMF.bind_comm]
  apply event_bind_constant
  intro replacement _
  change eventProb ((reserve (table past)).map (fun original => (past, original, replacement)))
    (fun triple => triple.2.1 (choose triple.1) = triple.2.2 (choose triple.1)) = _
  rw [eventProb_map]
  have value := congrArg (fun law => eventProb law (· = replacement (choose past)))
    (reserve_fresh (table past) (choose past) (fresh past reachable))
  simpa only [eventProb_map] using value.trans (uniform_guess _)

theorem reconstructWith_ne_shared (history : PMF History) (table : History → Table Input Tag)
    (restore : History → PMF (Input → Tag)) (choose : History → Input)
    (fresh : ∀ past ∈ history.support, (table past).lookup (choose past) = none)
    (nontrivial : (Fintype.card Tag : ℝ≥0∞)⁻¹ ≠ 1) :
    reconstructWith history table restore ≠ shared history table := by
  intro same
  have agreement := reconstructWith_agreement history table restore choose fresh
  rw [same, shared_agreement] at agreement
  exact nontrivial agreement.symm

/-- The retained function really is the original eager random function
conditioned on the complete adaptive outcome, including its actual cache. -/
theorem retained_eager {Result : Type} (program : Program Input Tag Result) :
    retained (program.run oracle []) Outcome.state =
      (uniform (Input → Tag)).bind (fun function =>
        (program.run (eager function) []).map (fun out => (out, function))) := by
  have empty (function : Input → Tag) : complete [] function = function := rfl
  simpa only [retained, reserve, PMF.map_comp, Function.comp_def, empty]
    using (eager_lazy_complete program []).symm

/-- The eager implementation's state is the whole function, whereas the
lazy implementation stores only its queried association list. -/
noncomputable def functionOracle : Oracle Input Tag (Input → Tag) :=
  fun function input => PMF.pure (function, function input)

def fullOutcome {Result : Type}
    (pair : Outcome Input Tag Result (Table Input Tag) × (Input → Tag)) :
    Outcome Input Tag Result (Input → Tag) :=
  ⟨pair.1.result, pair.2, pair.1.trace⟩

omit [Fintype Input] [Fintype Tag] [Nonempty Tag] in
theorem eager_full {Result : Type} (program : Program Input Tag Result)
    (function : Input → Tag) (table : Table Input Tag) (valid : TableValues function table) :
    (program.run (eager function) table).map (Program.mapState (fun _ => function)) =
      program.run functionOracle function := by
  apply Program.run_state_map_of_invariant (fun _ => function) (eager function) functionOracle
    (TableValues function)
    (fun table valid input answer supported => (eager_step_values function table valid input answer supported).1)
    _ program table valid
  intro cache coherent input
  cases known : cache.lookup input with
  | none => simp [eager, known, functionOracle, PMF.pure_map]
  | some tag => simp [eager, known, functionOracle, coherent.lookup known, PMF.pure_map]

noncomputable def completionJoint {Result : Type} (program : Program Input Tag Result) :=
  (retained (program.run oracle []) Outcome.state).map (fun pair => (fullOutcome pair, pair.1))

theorem completion_right {Result : Type} (program : Program Input Tag Result) :
    (completionJoint program).map Prod.snd = program.run oracle [] := by
  simp only [completionJoint, retained, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change ((program.run oracle []).bind fun out =>
    (reserve out.state).map (Function.const _ out)) = _
  simp only [PMF.map_const, PMF.bind_pure]

theorem completion_left {Result : Type} (program : Program Input Tag Result) :
    (completionJoint program).map Prod.fst =
      (uniform (Input → Tag)).bind (fun function => program.run functionOracle function) := by
  rw [completionJoint, retained_eager]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, fullOutcome]
  congr 1
  funext function
  exact eager_full program function [] (by intro entry member; cases member)

/-- The common realization preserves the complete public outcome and all
queried coordinates, despite the different hidden state types. -/
theorem completion_related {Result : Type} (program : Program Input Tag Result)
    (pair : Outcome Input Tag Result (Input → Tag) × Outcome Input Tag Result (Table Input Tag))
    (supported : pair ∈ (completionJoint program).support) :
    pair.1.result = pair.2.result ∧ pair.1.trace = pair.2.trace ∧
      ∀ input tag, pair.2.state.lookup input = some tag → pair.1.state input = tag := by
  rw [completionJoint, PMF.mem_support_map_iff] at supported
  obtain ⟨entry, reachable, rfl⟩ := supported
  rw [retained, PMF.mem_support_bind_iff] at reachable
  obtain ⟨out, _, reachable⟩ := reachable
  rw [PMF.mem_support_map_iff] at reachable
  obtain ⟨function, selected, rfl⟩ := reachable
  refine ⟨rfl, rfl, ?_⟩
  intro input tag known
  exact reserve_known out.state input tag known function selected

end CryptoOracle.RandomOracle.Posterior
