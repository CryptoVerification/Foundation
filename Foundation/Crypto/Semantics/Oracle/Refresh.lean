import Foundation.Crypto.Semantics.Oracle.PosteriorCoupling

/-! Conditional refresh kernels and their ordinary probability laws.
This module has no dependency on refresh diagrams or their certificate checker.
Refresh coordinates depend on the retained history, not on the current reserve.
These proof kernels do not grant a reprogramming interface to an adversary.
-/
namespace CryptoOracle.ProofEdits.Refresh
open Foundation.Probability CryptoOracle.RandomOracle CryptoOracle.RandomOracle.Posterior
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {Index Input Tag History : Type} [DecidableEq Input] [Fintype Tag] [Nonempty Tag]

noncomputable def step (coordinate : Index → History → Input) (index : Index)
    (state : History × (Input → Tag)) : PMF (History × (Input → Tag)) :=
  (uniform Tag).map fun tag => (state.1, Function.update state.2 (coordinate index state.1) tag)

noncomputable def run (coordinate : Index → History → Input) :
    List Index → (History × (Input → Tag)) → PMF (History × (Input → Tag))
  | [], state => PMF.pure state
  | index :: tail, state => (step coordinate index state).bind (run coordinate tail)

theorem run_append (coordinate : Index → History → Input) (first second : List Index)
    (state : History × (Input → Tag)) :
    run coordinate (first ++ second) state = (run coordinate first state).bind (run coordinate second) := by
  induction first generalizing state with
  | nil => simp [run]
  | cons index tail ih =>
      simp only [List.cons_append, run, PMF.bind_bind]
      exact congrArg (PMF.bind (step coordinate index state)) (funext ih)

theorem step_exchange (coordinate : Index → History → Input) (first second : Index)
    (state : History × (Input → Tag)) :
    (step coordinate first state).bind (step coordinate second) =
      (step coordinate second state).bind (step coordinate first) := by
  simp only [step, PMF.bind_map, Function.comp_def]
  by_cases same : coordinate first state.1 = coordinate second state.1
  · simp only [same, Function.update_idem]
  · simp only [PMF.map]
    rw [PMF.bind_comm]
    congr 1
    funext tag
    congr 1
    funext other
    apply congrArg PMF.pure
    exact Prod.ext rfl (Function.update_comm same _ _ _)

theorem step_duplicate (coordinate : Index → History → Input) (index : Index)
    (state : History × (Input → Tag)) :
    (step coordinate index state).bind (step coordinate index) = step coordinate index state := by
  simp [step, PMF.bind_map, Function.comp_def,
    Function.update_idem, PMF.bind_const]

variable [Fintype Input]

theorem reserve_preserve (table : Table Input Tag) (input : Input)
    (fresh : table.lookup input = none) :
    (reserve table).bind (fun function => (uniform Tag).map (fun tag => Function.update function input tag)) =
      reserve table := by
  have preserved := congrArg (PMF.map (complete table)) (uniform_function_resample (Range := Tag) input)
  simpa only [reserve, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
    complete_update_fresh table _ input _ fresh] using preserved

theorem step_preserve (history : PMF History) (table : History → Table Input Tag)
    (coordinate : Index → History → Input) (index : Index)
    (fresh : ∀ past ∈ history.support, (table past).lookup (coordinate index past) = none) :
    (retained history table).bind (step coordinate index) = retained history table := by
  simp only [retained, step, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply bind_congr_of_support
  intro past reachable
  have preserved := congrArg (PMF.map (fun function => (past, function)))
    (reserve_preserve (table past) (coordinate index past) (fresh past reachable))
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using preserved

theorem run_preserve (history : PMF History) (table : History → Table Input Tag)
    (coordinate : Index → History → Input) (word : List Index)
    (fresh : ∀ index ∈ word, ∀ past ∈ history.support,
      (table past).lookup (coordinate index past) = none) :
    (retained history table).bind (run coordinate word) = retained history table := by
  induction word with
  | nil => exact PMF.bind_pure _
  | cons index tail ih =>
      change (retained history table).bind (fun state =>
        (step coordinate index state).bind (run coordinate tail)) = _
      rw [← PMF.bind_bind, step_preserve history table coordinate index (fresh index (by simp))]
      exact ih (fun index member => fresh index (List.mem_cons_of_mem _ member))

/-- Keep the initial function as well as the final one. This retains the chosen joint coupling, not only the final eager marginal. -/
noncomputable def joint (history : PMF History) (table : History → Table Input Tag)
    (coordinate : Index → History → Input) (word : List Index) :=
  (retained history table).bind fun original =>
    (run coordinate word original).map (fun final => (original, final))

omit [Fintype Input] in
theorem run_history (coordinate : Index → History → Input) (word : List Index)
    (state final : History × (Input → Tag)) (supported : final ∈ (run coordinate word state).support) :
    final.1 = state.1 := by
  induction word generalizing state final with
  | nil =>
      rw [run, PMF.mem_support_pure_iff] at supported
      subst final
      rfl
  | cons index tail ih =>
      rw [run, PMF.mem_support_bind_iff] at supported
      obtain ⟨next, selected, supported⟩ := supported
      rw [step, PMF.mem_support_map_iff] at selected
      obtain ⟨tag, _, rfl⟩ := selected
      exact ih (state.1, Function.update state.2 (coordinate index state.1) tag) final supported

omit [Fintype Input] in
theorem run_untouched (coordinate : Index → History → Input) (word : List Index)
    (state final : History × (Input → Tag)) (supported : final ∈ (run coordinate word state).support)
    (input : Input) (untouched : ∀ index ∈ word, coordinate index state.1 ≠ input) :
    final.2 input = state.2 input := by
  induction word generalizing state final with
  | nil =>
      rw [run, PMF.mem_support_pure_iff] at supported
      subst final
      rfl
  | cons index tail ih =>
      rw [run, PMF.mem_support_bind_iff] at supported
      obtain ⟨next, selected, supported⟩ := supported
      rw [step, PMF.mem_support_map_iff] at selected
      obtain ⟨tag, _, rfl⟩ := selected
      rw [ih _ final supported (fun index member => untouched index (List.mem_cons_of_mem _ member))]
      exact Function.update_of_ne (Ne.symm (untouched index (by simp))) _ _

theorem joint_left (history : PMF History) (table : History → Table Input Tag)
    (coordinate : Index → History → Input) (word : List Index) :
    (joint history table coordinate word).map Prod.fst = retained history table := by
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change ((retained history table).bind fun original =>
    (run coordinate word original).map (Function.const _ original)) = _
  simp only [PMF.map_const, PMF.bind_pure]

theorem joint_right (history : PMF History) (table : History → Table Input Tag)
    (coordinate : Index → History → Input) (word : List Index)
    (fresh : ∀ index ∈ word, ∀ past ∈ history.support,
      (table past).lookup (coordinate index past) = none) :
    (joint history table coordinate word).map Prod.snd = retained history table := by
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change ((retained history table).bind fun original => (run coordinate word original).map id) = _
  simp only [PMF.map_id]
  exact run_preserve history table coordinate word fresh

theorem joint_last_agreement (history : PMF History) (table : History → Table Input Tag)
    (coordinate : Index → History → Input) (word : List Index) (index : Index) :
    eventProb (joint history table coordinate (word ++ [index]))
      (fun pair => pair.1.2 (coordinate index pair.1.1) = pair.2.2 (coordinate index pair.1.1)) =
      (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  apply event_bind_constant
  intro original _
  rw [run_append, PMF.map_bind]
  apply event_bind_constant
  intro intermediate supported
  have same := run_history coordinate word original intermediate supported
  simp only [run, PMF.bind_pure, step, PMF.map_comp, Function.comp_def]
  rw [eventProb_map]
  simp only [same, Function.update_self]
  simpa only [eq_comm] using uniform_guess (original.2 (coordinate index original.1))

theorem joint_untouched_agreement (history : PMF History) (table : History → Table Input Tag)
    (coordinate : Index → History → Input) (word : List Index) (choose : History → Input)
    (untouched : ∀ past, ∀ index ∈ word, coordinate index past ≠ choose past) :
    eventProb (joint history table coordinate word)
      (fun pair => pair.1.2 (choose pair.1.1) = pair.2.2 (choose pair.1.1)) = 1 := by
  have same : eventProb (joint history table coordinate word)
      (fun pair => pair.1.2 (choose pair.1.1) = pair.2.2 (choose pair.1.1)) =
      eventProb (joint history table coordinate word) (fun _ => True) := by
    apply eventProb_congr_of_support
    intro pair supported
    rw [joint, PMF.mem_support_bind_iff] at supported
    obtain ⟨original, _, supported⟩ := supported
    rw [PMF.mem_support_map_iff] at supported
    obtain ⟨final, selected, rfl⟩ := supported
    exact iff_true_intro (run_untouched coordinate word original final selected (choose original.1)
      (untouched original.1)).symm
  rw [same]
  simp [eventProb, PMF.toOuterMeasure_apply]

end CryptoOracle.ProofEdits.Refresh
