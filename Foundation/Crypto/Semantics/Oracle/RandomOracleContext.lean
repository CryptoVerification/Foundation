import Foundation.Crypto.Semantics.Oracle.RandomOracleFinite

/-! Finite-coordinate posterior laws in an independent, potentially infinite
oracle context. Only the coordinate alphabet is finite. The context's state and
request alphabet are unrestricted, but its kernel cannot inspect the sampled
coordinate function or coordinate cache. Both public windows may be adaptive.
This is needed for hidden hash vertices alongside an infinite-message hash RO. -/
namespace CryptoOracle.RandomOracle

open Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {Input Output Other Context Result : Type} [DecidableEq Input]
  [Fintype Output] [Nonempty Output]

/-- Independently stateful windows. Each kernel receives only its own state. -/
noncomputable def withContext (context : Oracle Other Output Context)
    (coordinates : Oracle Input Output (Table Input Output)) :
    Oracle (Other ⊕ Input) Output (Context × Table Input Output) :=
  fun (state, table) request => match request with
  | .inl other => (context state other).map (fun answer => ((answer.1, table), answer.2))
  | .inr input => (coordinates table input).map (fun answer => ((state, answer.1), answer.2))

omit [Fintype Output] [Nonempty Output] in
/-- Cached coordinates remain irrelevant to all future executions, even when
independent context calls are interleaved adaptively. -/
theorem eager_context_run_congr (context : Oracle Other Output Context)
    (program : Program (Other ⊕ Input) Output Result) (state : Context) (table : Table Input Output)
    (left right : Input → Output)
    (equal : ∀ input, table.lookup input = none → left input = right input) :
    program.run (withContext context (eager left)) (state, table) =
      program.run (withContext context (eager right)) (state, table) := by
  induction program generalizing state table with
  | done result => rfl
  | coin next ih =>
      simp only [Program.run]
      congr 1
      funext bit
      exact ih bit state table equal
  | query request next ih =>
      cases request with
      | inl other =>
          simp only [Program.run, withContext, PMF.bind_map]
          congr 1
          funext answer
          dsimp only [Function.comp_def]
          rw [ih answer.2 answer.1 table equal]
      | inr input =>
          cases cached : table.lookup input with
          | some output =>
              simp only [Program.run, withContext, eager, cached, PMF.pure_map, PMF.pure_bind]
              rw [ih output state table equal]
          | none =>
              have he := equal input cached
              simp only [Program.run, withContext, eager, cached, PMF.pure_map, PMF.pure_bind, he]
              rw [ih (right input) state ((input, right input) :: table)]
              intro x hx
              have different : x ≠ input := by
                intro eq
                subst x
                simp at hx
              have old : table.lookup x = none := by
                simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr different] using hx
              exact equal x old

/-- Complete posterior identity retains both oracle states, result, full
interleaved transcript, and the finite coordinate function. No uniform function
on the unrestricted context request alphabet is sampled or assumed. -/
theorem eager_lazy_complete_context [Fintype Input]
    (context : Oracle Other Output Context) (program : Program (Other ⊕ Input) Output Result)
    (state : Context) (table : Table Input Output) :
    (uniform (Input → Output)).bind (fun function =>
      (program.run (withContext context (eager function)) (state, table)).map
        (fun out => (out, complete table function))) =
    (program.run (withContext context oracle) (state, table)).bind (fun out =>
      (uniform (Input → Output)).map (fun function => (out, complete out.state.2 function))) := by
  induction program generalizing state table with
  | done result =>
      simp only [Program.run, PMF.pure_map, PMF.pure_bind]
      rfl
  | coin next ih =>
      simp only [Program.run, PMF.map_bind]
      rw [PMF.bind_comm]
      simp only [PMF.bind_bind]
      congr 1
      funext bit
      exact ih bit state table
  | query request next ih =>
      cases request with
      | inl other =>
          simp only [Program.run, withContext, PMF.bind_map, PMF.map_bind,
            PMF.map_comp, PMF.bind_bind, Function.comp_def]
          rw [PMF.bind_comm]
          congr 1
          funext answer
          have h := congrArg (PMF.map (fun pair =>
            ({ pair.1 with trace := ((Sum.inl other : Other ⊕ Input), answer.2) :: pair.1.trace }, pair.2)))
            (ih answer.2 answer.1 table)
          simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using h
      | inr input =>
          cases cached : table.lookup input with
          | some output =>
              simp only [Program.run, withContext, eager, oracle, cached, PMF.pure_bind,
                PMF.pure_map, PMF.map_comp, PMF.bind_map, Function.comp_def]
              have h := congrArg (PMF.map (fun pair =>
                ({ pair.1 with trace := ((Sum.inr input : Other ⊕ Input), output) :: pair.1.trace }, pair.2)))
                (ih output state table)
              simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using h
          | none =>
              simp only [Program.run, withContext, eager, oracle, cached, PMF.pure_bind,
                PMF.pure_map, PMF.map_comp, PMF.bind_map, PMF.bind_bind, Function.comp_def]
              simp_rw [← complete_cons_same table _ input cached]
              have hf := uniform_function_fresh input
                (fun output function =>
                  ((next output).run (withContext context (eager function))
                    (state, (input, output) :: table)).map (fun out =>
                      ({ out with trace := ((Sum.inr input : Other ⊕ Input), output) :: out.trace },
                        complete ((input, output) :: table) function)))
                (by
                  intro function output
                  have he : (next output).run (withContext context (eager (Function.update function input output)))
                      (state, (input, output) :: table) =
                      (next output).run (withContext context (eager function))
                        (state, (input, output) :: table) := by
                    apply eager_context_run_congr
                    intro x hx
                    have different : x ≠ input := by
                      intro eq
                      subst x
                      simp at hx
                    exact Function.update_of_ne different _ _
                  rw [he, complete_update_cached])
              rw [hf]
              congr 1
              funext output
              have h := congrArg (PMF.map (fun pair =>
                ({ pair.1 with trace := ((Sum.inr input : Other ⊕ Input), output) :: pair.1.trace }, pair.2)))
                (ih output state ((input, output) :: table))
              simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using h

/-- Forgetting the residual function gives exact full-outcome eager/lazy
equivalence for both interleaved windows. -/
theorem eager_lazy_context [Fintype Input] (context : Oracle Other Output Context)
    (program : Program (Other ⊕ Input) Output Result) (state : Context) (table : Table Input Output) :
    (uniform (Input → Output)).bind (fun function =>
      program.run (withContext context (eager function)) (state, table)) =
      program.run (withContext context oracle) (state, table) := by
  have h := congrArg (PMF.map Prod.fst) (eager_lazy_complete_context context program state table)
  simpa [PMF.map, Function.comp_def] using h

/-- An adaptively selected unqueried coordinate remains uniform even after
conditioning on the entire independent context and coordinate interaction. -/
theorem eager_unqueried_joint_context [Fintype Input]
    (context : Oracle Other Output Context) (program : Program (Other ⊕ Input) Output Result)
    (state : Context)
    (choose : Outcome (Other ⊕ Input) Output Result (Context × Table Input Output) → Input)
    (fresh : ∀ out ∈ (program.run (withContext context oracle) (state, [])).support,
      out.state.2.lookup (choose out) = none) :
    (uniform (Input → Output)).bind (fun function =>
      (program.run (withContext context (eager function)) (state, [])).map
        (fun out => (out, function (choose out)))) =
    (program.run (withContext context oracle) (state, [])).bind (fun out =>
      (uniform Output).map (fun value => (out, value))) := by
  have h := congrArg (PMF.map (fun pair => (pair.1, pair.2 (choose pair.1))))
    (eager_lazy_complete_context context program state [])
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

/-- Resampling an adaptively selected unqueried coordinate preserves the entire
joint law, including the already observed independent context. This operation
is a proof transformation and is not exposed to either client window. -/
theorem eager_resample_unqueried_context [Fintype Input]
    (context : Oracle Other Output Context) (program : Program (Other ⊕ Input) Output Result)
    (state : Context)
    (choose : Outcome (Other ⊕ Input) Output Result (Context × Table Input Output) → Input)
    (fresh : ∀ out ∈ (program.run (withContext context oracle) (state, [])).support,
      out.state.2.lookup (choose out) = none) :
    (uniform (Input → Output)).bind (fun function =>
      (program.run (withContext context (eager function)) (state, [])).bind (fun out =>
        (uniform Output).map (fun value => (out, Function.update function (choose out) value)))) =
    (uniform (Input → Output)).bind (fun function =>
      (program.run (withContext context (eager function)) (state, [])).map (fun out => (out, function))) := by
  have joint := eager_lazy_complete_context context program state []
  have empty (function : Input → Output) : complete [] function = function := rfl
  simp only [empty] at joint
  have changed := congrArg (fun law => law.bind (fun pair =>
    (uniform Output).map (fun value => (pair.1, Function.update pair.2 (choose pair.1) value)))) joint
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at changed
  rw [changed, joint]
  apply bind_congr_of_support
  intro out ho
  simp_rw [complete_update_fresh out.state.2 _ (choose out) _ (fresh out ho)]
  have h := congrArg (PMF.map (fun function => (out, complete out.state.2 function)))
    (uniform_function_resample (choose out))
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using h

/-- The same union bound survives arbitrary interleaving with the independent
context. Correlations among tested coordinates or guesses require no extra
independence assumption. -/
theorem eager_unqueried_many_guess_bound_context [Fintype Input]
    (context : Oracle Other Output Context) (program : Program (Other ⊕ Input) Output Result)
    (state : Context)
    (choices : Outcome (Other ⊕ Input) Output Result (Context × Table Input Output) → List Input)
    (guesses : Outcome (Other ⊕ Input) Output Result (Context × Table Input Output) → List Output)
    (coordinateLimit guessLimit : Nat)
    (fresh : ∀ out ∈ (program.run (withContext context oracle) (state, [])).support,
      ∀ input ∈ choices out, out.state.2.lookup input = none)
    (coordinateSize : ∀ out ∈ (program.run (withContext context oracle) (state, [])).support,
      (choices out).length ≤ coordinateLimit)
    (guessSize : ∀ out ∈ (program.run (withContext context oracle) (state, [])).support,
      (guesses out).length ≤ guessLimit) :
    eventProb ((uniform (Input → Output)).bind (fun function =>
      (program.run (withContext context (eager function)) (state, [])).map (fun out => (out, function))))
      (fun pair => ∃ input ∈ choices pair.1, pair.2 input ∈ guesses pair.1) ≤
      ((coordinateLimit * guessLimit : Nat) : ℝ≥0∞) *
        (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  have joint := eager_lazy_complete_context context program state []
  have empty (function : Input → Output) : complete [] function = function := rfl
  simp only [empty] at joint
  rw [joint]
  apply eventProb_bind_le_of_support
  intro out ho
  rw [eventProb_map]
  exact (uniform_complete_many_guess_bound out.state.2 (choices out) (guesses out) (fresh out ho)).trans
    (mul_le_mul' (by exact_mod_cast Nat.mul_le_mul (coordinateSize out ho) (guessSize out ho))
      (le_refl _))

end CryptoOracle.RandomOracle
