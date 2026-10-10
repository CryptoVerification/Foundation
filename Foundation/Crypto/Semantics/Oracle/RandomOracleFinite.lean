import Foundation.Crypto.Semantics.Oracle.RandomOracle
import Foundation.Crypto.Semantics.Probability.FiniteFunction

/-! Exact eager/lazy equivalence on finite input domains.
The eager oracle receives one function sampled before the interaction. Its cache
records only actually queried inputs, so the final cache and full public trace
have the same distribution as in the lazy experiment. The cache additionally
permits a fixed initial partial table. No uniform infinite function is used.
-/
namespace CryptoOracle.RandomOracle

open Foundation.Probability
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {Input Output Result : Type} [DecidableEq Input]
  [Fintype Output] [Nonempty Output]

/-- An eager function is evaluated only on inputs absent from the cache.
Starting with an empty cache, every response is exactly `function input`. -/
noncomputable def eager (function : Input → Output) : Oracle Input Output (Table Input Output) :=
  fun table input => match table.lookup input with
    | some output => PMF.pure (table, output)
    | none => PMF.pure ((input, function input) :: table, function input)

omit [Fintype Output] [Nonempty Output] in
/-- A value stored in the cache makes the corresponding function coordinate
irrelevant forever, including to adaptive future queries and public traces. -/
theorem eager_run_congr (program : Program Input Output Result) (table : Table Input Output)
    (left right : Input → Output)
    (h : ∀ input, table.lookup input = none → left input = right input) :
    program.run (eager left) table = program.run (eager right) table := by
  induction program generalizing table with
  | done result => rfl
  | query input next ih =>
      cases ht : table.lookup input with
      | some output =>
          simp only [Program.run, eager, ht, PMF.pure_bind]
          rw [ih output table h]
      | none =>
          have he := h input ht
          simp only [Program.run, eager, ht, PMF.pure_bind, he]
          rw [ih (right input) ((input, right input) :: table)]
          intro x hx
          have hxi : x ≠ input := by
            intro heq
            subst x
            simp at hx
          have hxt : table.lookup x = none := by
            simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr hxi] using hx
          exact h x hxt
  | coin next ih =>
      simp only [Program.run]
      congr 1
      funext bit
      exact ih bit table h

/-- Complete only unqueried coordinates. The cache, including any fixed
initial entries, takes precedence over the independent residual function. -/
def complete (table : Table Input Output) (function : Input → Output) : Input → Output :=
  fun input => (table.lookup input).getD (function input)

omit [Fintype Output] [Nonempty Output] in
theorem complete_cons_same (table : Table Input Output) (function : Input → Output)
    (input : Input) (fresh : table.lookup input = none) :
    complete ((input, function input) :: table) function = complete table function := by
  funext x
  by_cases hx : x = input
  · subst x
    simp [complete, fresh]
  · simp [complete, List.lookup_cons, beq_eq_false_iff_ne.mpr hx]

omit [Fintype Output] [Nonempty Output] in
theorem complete_update_cached (table : Table Input Output) (function : Input → Output)
    (input : Input) (output : Output) :
    complete ((input, output) :: table) (Function.update function input output) =
      complete ((input, output) :: table) function := by
  funext x
  by_cases hx : x = input
  · subst x
    simp [complete]
  · simp [complete, Function.update_of_ne hx]

/-- Exact posterior representation of an eager finite random function after
an arbitrary adaptive execution. The complete outcome (result, cache, trace)
is retained. Its unqueried coordinates can be generated independently after
the execution; queried coordinates are restored from the cache. This is a
joint-law identity, not permission for an adversary to reprogram the oracle. -/
theorem eager_lazy_complete [Fintype Input]
    (program : Program Input Output Result) (table : Table Input Output) :
    (uniform (Input → Output)).bind (fun function =>
      (program.run (eager function) table).map
        (fun out => (out, complete table function))) =
    (program.run oracle table).bind (fun out =>
      (uniform (Input → Output)).map (fun function => (out, complete out.state function))) := by
  induction program generalizing table with
  | done result =>
      simp only [Program.run, PMF.pure_map, PMF.pure_bind]
      rfl
  | coin next ih =>
      simp only [Program.run, PMF.map_bind]
      rw [PMF.bind_comm]
      simp only [PMF.bind_bind]
      congr 1
      funext bit
      exact ih bit table
  | query input next ih =>
      cases ht : table.lookup input with
      | some output =>
          simp only [Program.run, eager, oracle, ht, PMF.pure_bind, PMF.map_comp,
            PMF.bind_map, Function.comp_def]
          have h := congrArg (PMF.map (fun pair =>
            ({ pair.1 with trace := (input, output) :: pair.1.trace }, pair.2)))
            (ih output table)
          simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using h
      | none =>
          simp only [Program.run, eager, oracle, ht, PMF.pure_bind, PMF.map_comp,
            PMF.bind_map, PMF.bind_bind, Function.comp_def]
          simp_rw [← complete_cons_same table _ input ht]
          have hf := uniform_function_fresh input
            (fun output function =>
              ((next output).run (eager function) ((input, output) :: table)).map
                (fun out =>
                  ({ out with trace := (input, output) :: out.trace },
                    complete ((input, output) :: table) function)))
            (by
              intro function output
              have he : (next output).run (eager (Function.update function input output))
                  ((input, output) :: table) =
                  (next output).run (eager function) ((input, output) :: table) := by
                apply eager_run_congr
                intro x hx
                have hxi : x ≠ input := by
                  intro heq
                  subst x
                  simp at hx
                exact Function.update_of_ne hxi _ _
              rw [he, complete_update_cached])
          rw [hf]
          congr 1
          funext output
          have h := congrArg (PMF.map (fun pair =>
            ({ pair.1 with trace := (input, output) :: pair.1.trace }, pair.2)))
            (ih output ((input, output) :: table))
          simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using h


/-- Arbitrary adaptive programs have equal full outcome distributions under
eager and lazy sampling. Derived by forgetting the residual function from the
stronger joint-law theorem, so both equivalences use the same proof. -/
theorem eager_lazy [Fintype Input] (program : Program Input Output Result)
    (table : Table Input Output) :
    (uniform (Input → Output)).bind (fun function => program.run (eager function) table) =
      program.run oracle table := by
  have h := congrArg (PMF.map Prod.fst) (eager_lazy_complete program table)
  simpa [PMF.map, Function.comp_def] using h

/-- A coordinate selected from the full adaptive outcome is still independent
uniform randomness if it was not queried. The finite eager function is retained
on the left; the right is an independent draw after the observed execution. -/
theorem eager_unqueried_joint [Fintype Input]
    (program : Program Input Output Result)
    (choose : Outcome Input Output Result (Table Input Output) → Input)
    (fresh : ∀ out ∈ (program.run oracle []).support, out.state.lookup (choose out) = none) :
    (uniform (Input → Output)).bind (fun function =>
      (program.run (eager function) []).map (fun out => (out, function (choose out)))) =
    (program.run oracle []).bind (fun out =>
      (uniform Output).map (fun value => (out, value))) := by
  have h := congrArg (PMF.map (fun pair => (pair.1, pair.2 (choose pair.1))))
    (eager_lazy_complete program [])
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at h
  simp only [complete, List.lookup_nil, Option.getD_none] at h
  rw [h]
  apply bind_congr_of_support
  intro out ho
  simp only [fresh out ho, Option.getD_none]
  have he := uniform_function_fresh (choose out)
    (fun value (_ : Input → Output) => PMF.pure (out, value))
    (by intro function value; rfl)
  simpa only [PMF.bind_const, PMF.map, Function.comp_def, PMF.bind_pure] using he

/-- The adversary may choose both an unqueried coordinate and a list of guesses
from the complete prior outcome. A bound on the list length gives the usual
union bound without assuming that the choices were made nonadaptively. -/
theorem eager_unqueried_guess_list_bound [Fintype Input]
    (program : Program Input Output Result)
    (choose : Outcome Input Output Result (Table Input Output) → Input)
    (guesses : Outcome Input Output Result (Table Input Output) → List Output)
    (limit : Nat)
    (fresh : ∀ out ∈ (program.run oracle []).support, out.state.lookup (choose out) = none)
    (size : ∀ out ∈ (program.run oracle []).support, (guesses out).length ≤ limit) :
    eventProb ((uniform (Input → Output)).bind (fun function =>
      (program.run (eager function) []).map (fun out => (out, function (choose out)))))
      (fun pair => pair.2 ∈ guesses pair.1) ≤
      (limit : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  rw [eager_unqueried_joint program choose fresh]
  apply eventProb_bind_le_of_support
  intro out ho
  rw [eventProb_map]
  exact (uniform_mem_list (guesses out)).trans
    (mul_le_mul' (by exact_mod_cast size out ho) (le_refl _))


omit [Fintype Output] [Nonempty Output] in
theorem complete_update_fresh (table : Table Input Output) (function : Input → Output)
    (input : Input) (output : Output) (fresh : table.lookup input = none) :
    Function.update (complete table function) input output =
      complete table (Function.update function input output) := by
  funext x
  by_cases hx : x = input
  · subst x
    simp [complete, fresh]
  · simp [complete, Function.update_of_ne hx]

/-- Resampling an adaptively selected unqueried coordinate preserves the joint
law of the entire eager function and the prior outcome. The outcome is retained,
not rerun against the changed function. The excluded-query premise is essential. -/
theorem eager_resample_unqueried [Fintype Input]
    (program : Program Input Output Result)
    (choose : Outcome Input Output Result (Table Input Output) → Input)
    (fresh : ∀ out ∈ (program.run oracle []).support, out.state.lookup (choose out) = none) :
    (uniform (Input → Output)).bind (fun function =>
      (program.run (eager function) []).bind (fun out =>
        (uniform Output).map (fun value =>
          (out, Function.update function (choose out) value)))) =
    (uniform (Input → Output)).bind (fun function =>
      (program.run (eager function) []).map (fun out => (out, function))) := by
  have joint := eager_lazy_complete program []
  have empty (function : Input → Output) : complete [] function = function := rfl
  simp only [empty] at joint
  have changed := congrArg (fun law => law.bind (fun pair =>
    (uniform Output).map (fun value =>
      (pair.1, Function.update pair.2 (choose pair.1) value)))) joint
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at changed
  rw [changed, joint]
  apply bind_congr_of_support
  intro out ho
  simp_rw [complete_update_fresh out.state _ (choose out) _ (fresh out ho)]
  have h := congrArg (PMF.map (fun function => (out, complete out.state function)))
    (uniform_function_resample (choose out))
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using h


/-- Union bound for unqueried coordinates of a completed finite function.
The table and both lists can later be selected from any adaptive outcome. -/
theorem uniform_complete_many_guess_bound [Fintype Input]
    (table : Table Input Output) (inputs : List Input) (guesses : List Output)
    (hf : ∀ input ∈ inputs, table.lookup input = none) :
    eventProb (uniform (Input → Output))
      (fun function => ∃ input ∈ inputs, complete table function input ∈ guesses) ≤
    ((inputs.length * guesses.length : Nat) : ℝ≥0∞) *
      (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  induction inputs with
  | nil => simp [eventProb]
  | cons input inputs ih =>
      have he : (uniform (Input → Output)).map (fun function => function input) =
          uniform Output := by
        have h := uniform_function_fresh input
          (fun value (_ : Input → Output) => PMF.pure value)
          (by intro function value; rfl)
        simpa only [PMF.bind_const, PMF.map, Function.comp_def, PMF.bind_pure] using h
      have one : eventProb (uniform (Input → Output))
          (fun function => complete table function input ∈ guesses) ≤
          guesses.length * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
        simp only [complete, hf input (List.mem_cons_self ..), Option.getD_none]
        rw [← eventProb_map, he]
        exact uniform_mem_list guesses
      calc
        _ ≤ eventProb (uniform (Input → Output))
              (fun function => complete table function input ∈ guesses) +
            eventProb (uniform (Input → Output))
              (fun function => ∃ x ∈ inputs, complete table function x ∈ guesses) := by
          simpa only [List.mem_cons, exists_eq_or_imp] using
            eventProb_or_le (uniform (Input → Output))
              (fun function => complete table function input ∈ guesses)
              (fun function => ∃ x ∈ inputs, complete table function x ∈ guesses)
        _ ≤ _ := add_le_add one (ih (fun x hx => hf x (List.mem_cons_of_mem _ hx)))
        _ = _ := by simp [Nat.cast_add, Nat.cast_mul, add_mul, add_comm]

/-- Simultaneously test several adaptively selected unqueried coordinates
against a list of guesses. Repeated coordinates and guesses are allowed; no
independence between these tests is needed for the conservative union bound. -/
theorem eager_unqueried_many_guess_bound [Fintype Input]
    (program : Program Input Output Result)
    (choices : Outcome Input Output Result (Table Input Output) → List Input)
    (guesses : Outcome Input Output Result (Table Input Output) → List Output)
    (coordinateLimit guessLimit : Nat)
    (fresh : ∀ out ∈ (program.run oracle []).support,
      ∀ input ∈ choices out, out.state.lookup input = none)
    (coordinateSize : ∀ out ∈ (program.run oracle []).support,
      (choices out).length ≤ coordinateLimit)
    (guessSize : ∀ out ∈ (program.run oracle []).support,
      (guesses out).length ≤ guessLimit) :
    eventProb ((uniform (Input → Output)).bind (fun function =>
      (program.run (eager function) []).map (fun out => (out, function))))
      (fun pair => ∃ input ∈ choices pair.1, pair.2 input ∈ guesses pair.1) ≤
      ((coordinateLimit * guessLimit : Nat) : ℝ≥0∞) *
        (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  have joint := eager_lazy_complete program []
  have empty (function : Input → Output) : complete [] function = function := rfl
  simp only [empty] at joint
  rw [joint]
  apply eventProb_bind_le_of_support
  intro out ho
  rw [eventProb_map]
  exact (uniform_complete_many_guess_bound out.state (choices out) (guesses out) (fresh out ho)).trans
    (mul_le_mul' (by exact_mod_cast Nat.mul_le_mul (coordinateSize out ho) (guessSize out ho))
      (le_refl _))

end CryptoOracle.RandomOracle
