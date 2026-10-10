import Foundation.Crypto.Semantics.Oracle.RandomOracleContext
import Foundation.Crypto.Semantics.Oracle.StateMap

/-! Agreement between an eager oracle's actual cache and its fixed function.
This is distinct from TableConsistent, which relates entries only to lookup.
No finite input domain or randomness assumption is needed for these invariants. -/
namespace CryptoOracle.RandomOracle

open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Input Output Other Context Result : Type} [DecidableEq Input]

def TableValues (function : Input → Output) (table : Table Input Output) : Prop :=
  ∀ entry ∈ table, entry.2 = function entry.1

theorem TableValues.lookup {function : Input → Output} {table : Table Input Output}
    (valid : TableValues function table) {input : Input} {output : Output}
    (known : table.lookup input = some output) : output = function input := by
  obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp known
  exact valid (input, output) (by rw [same]; simp)

/-- Existing cached entries and newly read eager coordinates agree with the
same function. This holds for each fixed function and supported transition. -/
theorem eager_step_values (function : Input → Output) (table : Table Input Output)
    (valid : TableValues function table) (input : Input) (answer : Table Input Output × Output)
    (support : answer ∈ (eager function table input).support) :
    TableValues function answer.1 ∧ answer.2 = function input := by
  cases known : table.lookup input with
  | some output =>
      simp only [eager, known, PMF.mem_support_pure_iff] at support
      subst answer
      exact ⟨valid, valid.lookup known⟩
  | none =>
      simp only [eager, known, PMF.mem_support_pure_iff] at support
      subst answer
      refine ⟨?_, rfl⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · exact valid entry member

/-- Independent context calls cannot change the coordinate-value invariant. -/
theorem eager_context_step_values (function : Input → Output) (context : Oracle Other Output Context)
    (state : Context × Table Input Output) (valid : TableValues function state.2)
    (request : Other ⊕ Input) (answer : (Context × Table Input Output) × Output)
    (support : answer ∈ (withContext context (eager function) state request).support) :
    TableValues function answer.1.2 := by
  cases request with
  | inl other =>
      rw [withContext, PMF.mem_support_map_iff] at support
      obtain ⟨response, _, rfl⟩ := support
      exact valid
  | inr input =>
      rw [withContext, PMF.mem_support_map_iff] at support
      obtain ⟨response, reachable, rfl⟩ := support
      exact (eager_step_values function state.2 valid input response reachable).1

/-- Adaptive executions preserve agreement with the fixed coordinate function,
including their entire independent context and all local coin choices. -/
theorem eager_context_run_values (function : Input → Output) (context : Oracle Other Output Context)
    (program : Program (Other ⊕ Input) Output Result) (state : Context) (table : Table Input Output)
    (valid : TableValues function table)
    (out : Outcome (Other ⊕ Input) Output Result (Context × Table Input Output))
    (support : out ∈ (program.run (withContext context (eager function)) (state, table)).support) :
    TableValues function out.state.2 :=
  Program.run_preserves _ (fun state => TableValues function state.2)
    (eager_context_step_values function context) program (state, table) valid out support

/-- Each fixed eager transition is reachable in the lazy oracle, even with
an arbitrary existing cache. This is support inclusion, not equality of laws. -/
theorem eager_step_support [Fintype Output] [Nonempty Output]
    (function : Input → Output) (table : Table Input Output) (input : Input)
    (answer : Table Input Output × Output) (support : answer ∈ (eager function table input).support) :
    answer ∈ (oracle table input).support := by
  cases known : table.lookup input with
  | some output => simpa only [eager, oracle, known] using support
  | none =>
      simp only [eager, known, PMF.mem_support_pure_iff] at support
      subst answer
      rw [oracle, known, PMF.mem_support_map_iff]
      exact ⟨function input, PMF.mem_support_uniformOfFintype _, rfl⟩

/-- The same support inclusion holds in an independent context, retaining
both actual caches and the response. No finite input type is required. -/
theorem eager_context_step_support [Fintype Output] [Nonempty Output]
    (function : Input → Output) (context : Oracle Other Output Context)
    (state : Context × Table Input Output) (request : Other ⊕ Input)
    (answer : (Context × Table Input Output) × Output)
    (support : answer ∈ (withContext context (eager function) state request).support) :
    answer ∈ (withContext context oracle state request).support := by
  cases request with
  | inl other => exact support
  | inr input =>
      rw [withContext, PMF.mem_support_map_iff] at support ⊢
      obtain ⟨response, reachable, same⟩ := support
      exact ⟨response, eager_step_support function state.2 input response reachable, same⟩

/-- Fixed eager executions have the same reachable whole outcomes as a subset
of lazy executions. This lemma does not compare their probability masses. -/
theorem eager_run_support [Fintype Output] [Nonempty Output]
    (function : Input → Output) (program : Program Input Output Result) (table : Table Input Output)
    (out : Outcome Input Output Result (Table Input Output))
    (support : out ∈ (program.run (eager function) table).support) :
    out ∈ (program.run oracle table).support := by
  have transferred := Program.run_support_state_map id (eager function) oracle
    (fun state request answer reachable => eager_step_support function state request answer reachable)
    program table out support
  simpa only [Program.mapState, id_eq] using transferred

end CryptoOracle.RandomOracle
