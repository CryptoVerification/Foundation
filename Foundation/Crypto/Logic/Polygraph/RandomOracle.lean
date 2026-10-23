import Foundation.Crypto.Logic.Polygraph.StateCube
import Foundation.Crypto.Semantics.Oracle.RandomOracleValues

/-! Coherent exposure of a retained finite random function, connected to the
existing adaptive lazy oracle. Cache order is representation data; the public
transcript is retained. The finite function is a coupling witness, not an
instruction to enumerate an exponentially large domain in an implementation. -/
namespace CryptoOracle.RandomOracle.Cube

open Foundation.Probability Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.StateCube
set_option backward.isDefEq.respectTransparency false

variable {Input Output Result : Type} [DecidableEq Input]

/-- The second register is the retained randomness; the first records exactly
which coordinates have been exposed. Clients never receive either register. -/
abbrev cube (Input Output : Type) [DecidableEq Input] : StateCube Input where
  State := Finset Input × (Input → Output)
  vertex := Prod.fst
  step input x := (insert input x.1, x.2)
  vertex_step _ _ := rfl
  step_present _ _ hi := Prod.ext (Finset.insert_eq_of_mem hi) rfl
  square i j x _ _ _ := Prod.ext (Finset.insert_comm j i x.1) rfl

theorem query_eq (x : (cube Input Output).State) (S : Finset Input) :
    (cube Input Output).query x S = (x.1 ∪ S, x.2) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [StateCube.query_insert, ih]
    change (insert i (x.1 ∪ S), x.2) = (x.1 ∪ insert i S, x.2)
    exact Prod.ext (by ext j; simp) rfl

/-- The visible partial cache, excluding the retained unexposed coordinates. -/
def view (x : (cube Input Output).State) (input : Input) : Option Output :=
  if input ∈ x.1 then some (x.2 input) else none

def seen (table : Table Input Output) : Finset Input := (table.map Prod.fst).toFinset

def snapshot (function : Input → Output) (table : Table Input Output) :
    (cube Input Output).State := (seen table, function)

theorem mem_seen_iff (table : Table Input Output) (input : Input) :
    input ∈ seen table ↔ ∃ output, table.lookup input = some output := by
  induction table with
  | nil => simp [seen]
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    by_cases h : input = key
    · subst key; simp [seen]
    · simpa [seen, h, List.lookup_cons, beq_eq_false_iff_ne.mpr h] using ih

/-- The canonical cache agrees with every actual lookup, including absence.
Its construction does not assert equality of the raw list representations. -/
theorem snapshot_view (function : Input → Output) (table : Table Input Output)
    (valid : TableValues function table) (input : Input) :
    view (snapshot function table) input = table.lookup input := by
  cases h : table.lookup input with
  | none =>
    have hm : input ∉ seen table := by simp [mem_seen_iff, h]
    simp [view, snapshot, hm]
  | some value =>
    have hm : input ∈ seen table := (mem_seen_iff table input).mpr ⟨value, h⟩
    simp [view, snapshot, hm, valid.lookup h]

noncomputable def coordinateOracle : Oracle Input Output (cube Input Output).State :=
  fun x input => PMF.pure ((cube Input Output).step input x, x.2 input)

/-- Moving an exposure across an entire adaptive client is justified by the
local squares. The client's result, local coins and public trace are retained. -/
theorem prefetch_run (S : Finset Input) (program : Program Input Output Result)
    (x : (cube Input Output).State) :
    (program.run coordinateOracle x).map
        (Program.mapState (fun state => (cube Input Output).query state S)) =
      program.run coordinateOracle ((cube Input Output).query x S) := by
  apply Program.run_state_map
  intro state input
  simp only [coordinateOracle, PMF.pure_map]
  apply congrArg PMF.pure
  apply Prod.ext
  · exact (cube Input Output).run_step S.toList input state
  · simp [query_eq]

/-- The final exposure state is obtained by the cube evaluator on the actual
adaptive query trace. This also accounts for repeated queries. -/
theorem coordinate_final (program : Program Input Output Result)
    (x : (cube Input Output).State)
    (out : Outcome Input Output Result (cube Input Output).State)
    (ho : out ∈ (program.run coordinateOracle x).support) :
    out.state = (cube Input Output).run (out.trace.map Prod.fst) x := by
  have h := Program.run_observe_trace coordinateOracle id
    (fun state input _ => (cube Input Output).step input state)
    (by
      intro state input answer ha
      simp only [coordinateOracle, PMF.mem_support_pure_iff] at ha
      subst answer
      rfl) program x out ho
  simpa only [id_eq, StateCube.run, List.foldl_map] using h

theorem coordinate_distinct_bound {program : Program Input Output Result} {q : Nat}
    (hq : program.BoundedQueries q) (function : Input → Output)
    (out : Outcome Input Output Result (cube Input Output).State)
    (ho : out ∈ (program.run coordinateOracle (∅, function)).support) :
    out.state.1.card ≤ q := by
  have hf := coordinate_final program (∅, function) out ho
  rw [StateCube.run_eq_query, query_eq, Finset.empty_union] at hf
  rw [hf]
  exact (List.toFinset_card_le _).trans
    (by simpa only [List.length_map] using hq.trace_length_le coordinateOracle (∅, function) out ho)

theorem eager_step_snapshot (function : Input → Output) (table : Table Input Output)
    (valid : TableValues function table) (input : Input) :
    (eager function table input).map (fun answer => (snapshot function answer.1, answer.2)) =
      coordinateOracle (snapshot function table) input := by
  cases h : table.lookup input with
  | none => simp [eager, h, coordinateOracle, snapshot, seen, cube, PMF.pure_map]
  | some value =>
    have hm : input ∈ seen table := (mem_seen_iff table input).mpr ⟨value, h⟩
    simp [eager, h, coordinateOracle, snapshot, cube, Finset.insert_eq_of_mem hm,
      valid.lookup h, PMF.pure_map]

/-- Equality of complete adaptive outcomes after canonicalizing the private
cache. Local coins, repeated queries, results, and ordered traces are retained. -/
theorem eager_run_snapshot (function : Input → Output)
    (program : Program Input Output Result) (table : Table Input Output)
    (valid : TableValues function table) :
    (program.run (eager function) table).map (Program.mapState (snapshot function)) =
      program.run coordinateOracle (snapshot function table) :=
  Program.run_state_map_of_invariant (snapshot function) (eager function) coordinateOracle
    (TableValues function)
    (fun table valid input answer ha => (eager_step_values function table valid input answer ha).1)
    (fun table valid input => eager_step_snapshot function table valid input)
    program table valid

variable [Fintype Input] [Fintype Output] [Nonempty Output]

/-- Independently prescribed laws at the vertices retain the whole reserve.
Their visible projection is the partially exposed random function. -/
noncomputable def model : Measured (cube Input Output) where
  law S := (uniform (Input → Output)).map (fun function => (S, function))
  supported S x hx := by
    obtain ⟨function, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    rfl
  preserve S i _ := by rw [PMF.map_comp]; rfl

/-- One adaptive execution, including its local coins, realizes all cache
prefetch choices simultaneously. The clients do not run independently. -/
noncomputable def executionJoint (program : Program Input Output Result) :
    PMF (Finset Input → Outcome Input Output Result (cube Input Output).State) :=
  (uniform (Input → Output)).bind fun function =>
    (program.run coordinateOracle (∅, function)).map fun out S =>
      Program.mapState (fun state => (cube Input Output).query state S) out

theorem execution_marginal (program : Program Input Output Result) (S : Finset Input) :
    (executionJoint program).map (fun a => a S) =
      (uniform (Input → Output)).bind (fun function =>
        program.run coordinateOracle (S, function)) := by
  simp only [executionJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext function
  simpa only [query_eq, Finset.empty_union] using
    prefetch_run S program ((∅, function) : (cube Input Output).State)

theorem execution_public (program : Program Input Output Result)
    (a : Finset Input → Outcome Input Output Result (cube Input Output).State)
    (ha : a ∈ (executionJoint program).support) (S T : Finset Input) :
    (a S).result = (a T).result ∧ (a S).trace = (a T).trace := by
  obtain ⟨function, _, ha⟩ := (PMF.mem_support_bind_iff _ _ _).mp ha
  obtain ⟨out, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  exact ⟨rfl, rfl⟩

theorem execution_edges (program : Program Input Output Result)
    (a : Finset Input → Outcome Input Output Result (cube Input Output).State)
    (ha : a ∈ (executionJoint program).support) (S : Finset Input) (i : Input) :
    (a (insert i S)).state = (cube Input Output).step i (a S).state := by
  obtain ⟨function, _, ha⟩ := (PMF.mem_support_bind_iff _ _ _).mp ha
  obtain ⟨out, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  exact (cube Input Output).query_insert out.state S i

/-- An actual lazy execution and all cube vertices share one joint law.
Only the proof witness samples the finite reserve in advance. -/
noncomputable def coupled (program : Program Input Output Result) :
    PMF (Outcome Input Output Result (Table Input Output) ×
      (Finset Input → (cube Input Output).State)) :=
  (uniform (Input → Output)).bind fun function =>
    (program.run (eager function) []).map fun out =>
      (out, fun S => (cube Input Output).query (∅, function) S)

theorem coupled_lazy (program : Program Input Output Result) :
    (coupled program).map Prod.fst = program.run oracle [] := by
  simpa [coupled, PMF.map_bind, PMF.map_comp, PMF.map, Function.comp_def] using
    (eager_lazy program ([] : Table Input Output))

theorem coupled_cube (program : Program Input Output Result) :
    (coupled program).map Prod.snd = (model (Input := Input) (Output := Output)).joint := by
  simp only [coupled, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (uniform (Input → Output)).bind (fun function =>
    (program.run (eager function) []).map (Function.const _
      (fun S => (cube Input Output).query (∅, function) S))) = _
  simp only [PMF.map_const]
  rw [Measured.joint, model, PMF.map_comp]
  rfl

omit [Fintype Input] [Fintype Output] [Nonempty Output] in
theorem eager_run_values (function : Input → Output) (program : Program Input Output Result)
    (out : Outcome Input Output Result (Table Input Output))
    (ho : out ∈ (program.run (eager function) []).support) : TableValues function out.state :=
  Program.run_preserves (eager function) (TableValues function)
    (fun table valid input answer ha => (eager_step_values function table valid input answer ha).1)
    program [] (by intro entry h; cases h) out ho

/-- The actual final lazy cache is a vertex of the same common realization.
The choice of vertex may depend on all previous answers and local coins. -/
theorem coupled_cache (program : Program Input Output Result)
    (pair : Outcome Input Output Result (Table Input Output) ×
      (Finset Input → (cube Input Output).State))
    (hp : pair ∈ (coupled program).support) :
    ∀ input, view (pair.2 (seen pair.1.state)) input = pair.1.state.lookup input := by
  obtain ⟨function, _, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
  obtain ⟨out, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  intro input
  change view ((cube Input Output).query (∅, function) (seen out.state)) input = _
  rw [query_eq, Finset.empty_union]
  exact snapshot_view function out.state (eager_run_values function program out ho) input

def observe (out : Outcome Input Output Result (cube Input Output).State) :=
  (out.result, view out.state, out.trace)

def observeTable (out : Outcome Input Output Result (Table Input Output)) :=
  (out.result, (fun input => out.state.lookup input), out.trace)

/-- Native or adaptive clients can use the common realization while the
actual executable oracle remains the existing on-demand sampler. The
observation includes every cache lookup and the ordered public transcript. -/
theorem lazy_run_snapshot (program : Program Input Output Result) :
    (uniform (Input → Output)).bind (fun function =>
      (program.run coordinateOracle (∅, function)).map observe) =
    (program.run oracle []).map observeTable := by
  have fixed (function : Input → Output) :
      (program.run coordinateOracle (∅, function)).map observe =
      (program.run (eager function) []).map observeTable := by
    change (program.run coordinateOracle (snapshot function [])).map observe = _
    rw [← eager_run_snapshot function program [] (by intro entry h; cases h), PMF.map_comp]
    unfold PMF.map
    apply bind_congr_of_support
    intro out ho
    apply congrArg PMF.pure
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext input
        exact snapshot_view function out.state (eager_run_values function program out ho) input
      · rfl
  simp_rw [fixed]
  rw [← PMF.map_bind, eager_lazy]

noncomputable def publicLaw (program : Program Input Output Result) (S : Finset Input) :=
  (uniform (Input → Output)).bind fun function =>
    (program.run coordinateOracle (S, function)).map (fun out => (out.result, out.trace))

/-- Exposing any selected cache coordinates in advance preserves the whole
public experiment. This is derived by moving the exposure across the client. -/
theorem prefetch_public (program : Program Input Output Result) (S : Finset Input) :
    publicLaw program S = publicLaw program ∅ := by
  unfold publicLaw
  congr 1
  funext function
  have h := congrArg (PMF.map (fun out => (out.result, out.trace)))
    (prefetch_run S program ((∅, function) : (cube Input Output).State))
  simpa only [PMF.map_comp, Program.mapState, Function.comp_def, query_eq,
    Finset.empty_union] using h.symm

theorem public_correct (program : Program Input Output Result) (S : Finset Input) :
    publicLaw program S = (program.run oracle []).map (fun out => (out.result, out.trace)) := by
  rw [prefetch_public program S]
  have h := congrArg (PMF.map (fun out => (out.1, out.2.2))) (lazy_run_snapshot program)
  simpa only [publicLaw, PMF.map_bind, PMF.map_comp, observe, observeTable,
    Function.comp_def] using h

/-- An exact transformation certificate for the existing game-proof layer. -/
noncomputable def prefetchPath (program : Program Input Output Result) (S : Finset Input) :
    CryptoLogic.Polygraph.Experiment.ExactPath (.sample (publicLaw program S))
      (.sample ((program.run oracle []).map (fun out => (out.result, out.trace)))) :=
  .step (.distribution (public_correct program S))

end CryptoOracle.RandomOracle.Cube
