import Foundation.Crypto.Semantics.Oracle.FiniteRequests
import Foundation.Crypto.Semantics.Oracle.RandomOracleContext

/-! Restrict only the random-oracle window to its finite possible domain.
The other independently stateful window remains unrestricted, including its
randomness and complete state. Domain enumeration is proof instrumentation. -/
namespace CryptoOracle.Program

open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Other Input Output Result : Type} [DecidableEq Other] [DecidableEq Input] [Fintype Output]

/-- All right-window requests across every response and local-coin branch. -/
noncomputable def rightRequests (program : Program (Other ⊕ Input) Output Result) : Finset Input :=
  program.possibleRequests.biUnion (fun request => match request with
    | .inl _ => ∅
    | .inr input => {input})

theorem mem_rightRequests (program : Program (Other ⊕ Input) Output Result) (input : Input) :
    input ∈ program.rightRequests ↔ Sum.inr input ∈ program.possibleRequests := by
  simp only [rightRequests, Finset.mem_biUnion]
  constructor
  · rintro ⟨request, member, included⟩
    cases request with
    | inl other => simp at included
    | inr value => simpa using (Finset.mem_singleton.mp included) ▸ member
  · intro member
    exact ⟨.inr input, member, Finset.mem_singleton_self input⟩

noncomputable def restrictRightTo (allowed : Finset Input) :
    (program : Program (Other ⊕ Input) Output Result) →
    (∀ input, Sum.inr input ∈ possibleRequests program → input ∈ allowed) →
      Program (Other ⊕ {input // input ∈ allowed}) Output Result
  | .done result, _ => .done result
  | .query (.inl other) next, included =>
      .query (.inl other) (fun response => restrictRightTo allowed (next response)
        (fun input member => included input (possibleRequests_next (.inl other) next response member)))
  | .query (.inr value) next, included =>
      .query (.inr ⟨value, included value (possibleRequests_query (.inr value) next)⟩)
        (fun response => restrictRightTo allowed (next response)
          (fun input member => included input (possibleRequests_next (.inr value) next response member)))
  | .coin next, included => .coin (fun bit => restrictRightTo allowed (next bit)
      (fun input member => included input (possibleRequests_coin next bit member)))

theorem restrictRightTo_val (allowed : Finset Input) (program : Program (Other ⊕ Input) Output Result)
    (included : ∀ input, Sum.inr input ∈ possibleRequests program → input ∈ allowed) :
    (restrictRightTo allowed program included).mapQueries (Sum.map id Subtype.val) id = program := by
  induction program with
  | done result => rfl
  | query request next ih =>
      cases request <;> simp only [restrictRightTo, mapQueries, Sum.map, id_eq] <;>
        congr 1 <;> funext response <;> exact ih response _
  | coin next ih =>
      simp only [restrictRightTo, mapQueries]
      congr 1
      funext bit
      exact ih bit _

theorem restrictRightTo_queries (allowed : Finset Input)
    {program : Program (Other ⊕ Input) Output Result} {q : Nat} (bound : program.BoundedQueries q)
    (included : ∀ input, Sum.inr input ∈ possibleRequests program → input ∈ allowed) :
    (restrictRightTo allowed program included).BoundedQueries q := by
  induction bound with
  | done result q => exact .done _ _
  | query request next q bound ih =>
      cases request <;> exact .query _ _ q (fun response => ih response _)
  | coin next q bound ih => exact .coin _ q (fun bit => ih bit _)

end CryptoOracle.Program

namespace CryptoOracle.RandomOracle

open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Input Target Other Output Context Result : Type} [DecidableEq Input] [DecidableEq Target]
  [Fintype Output] [Nonempty Output]

/-- Reindexing only the RO window leaves the independent context untouched. -/
theorem reindex_context_step (encode : Input → Target) (injective : Function.Injective encode)
    (context : Oracle Other Output Context) (state : Context) (table : Table Input Output)
    (request : Other ⊕ Input) :
    (withContext context oracle (state, table) request).map
      (fun answer => ((answer.1.1, mapTable encode answer.1.2), answer.2)) =
      withContext context oracle (state, mapTable encode table) (Sum.map id encode request) := by
  cases request with
  | inl other => simp [withContext, PMF.map_comp, Function.comp_def]
  | inr input =>
      have encoded := congrArg (PMF.map (fun answer => ((state, answer.1), answer.2)))
        (reindex_step encode injective table input)
      simpa [withContext, Sum.map, PMF.map_comp, Function.comp_def] using encoded

theorem reindex_context_run (encode : Input → Target) (injective : Function.Injective encode)
    (context : Oracle Other Output Context) (program : Program (Other ⊕ Input) Output Result)
    (state : Context) (table : Table Input Output) :
    (program.run (withContext context oracle) (state, table)).map
      (Program.mapState (fun pair => (pair.1, mapTable encode pair.2))) =
    program.run (Program.adaptOracle (Sum.map id encode) id (withContext context oracle))
      (state, mapTable encode table) := by
  apply Program.run_state_map
  intro pair request
  change _ = PMF.map id _
  rw [PMF.map_id]
  exact reindex_context_step encode injective context pair.1 pair.2 request

/-- Restricting the RO requests preserves the entire interleaved outcome:
context state, encoded RO cache, result, and original public transcript. -/
theorem finite_context_restriction_run [DecidableEq Other]
    (allowed : Finset Input) (context : Oracle Other Output Context)
    (program : Program (Other ⊕ Input) Output Result)
    (included : ∀ input, Sum.inr input ∈ program.possibleRequests → input ∈ allowed) (state : Context) :
    ((program.restrictRightTo allowed included).run (withContext context oracle) (state, [])).map
      (fun out => Program.mapTranscript (Sum.map id Subtype.val) id
        (Program.mapState (fun pair => (pair.1, mapTable Subtype.val pair.2)) out)) =
      program.run (withContext context oracle) (state, []) := by
  have reindexed := congrArg (PMF.map (Program.mapTranscript (Sum.map id Subtype.val) id))
    (reindex_context_run Subtype.val Subtype.val_injective context (program.restrictRightTo allowed included) state [])
  have mapped := Program.mapQueries_run (Sum.map id Subtype.val) id
    (program.restrictRightTo allowed included) (withContext context (oracle (Input := Input))) (state, [])
  rw [Program.restrictRightTo_val] at mapped
  have eraseFun : Program.mapTranscript (id : Other ⊕ Input → Other ⊕ Input) (id : Output → Output) =
      (id : Outcome (Other ⊕ Input) Output Result (Context × Table Input Output) → _) := by
    funext out
    cases out
    simp [Program.mapTranscript]
  rw [eraseFun, PMF.map_id] at mapped
  simpa only [PMF.map_comp, mapTable, List.map_nil, Function.comp_def] using reindexed.trans mapped.symm

/-- Only the explicitly finite RO domain is sampled eagerly. The unrestricted
context keeps its own independent kernel, with no function sampled on it. -/
theorem finite_context_restriction_eager [DecidableEq Other]
    (allowed : Finset Input) (context : Oracle Other Output Context)
    (program : Program (Other ⊕ Input) Output Result)
    (included : ∀ input, Sum.inr input ∈ program.possibleRequests → input ∈ allowed) (state : Context) :
    (uniform ({input // input ∈ allowed} → Output)).bind (fun function =>
      ((program.restrictRightTo allowed included).run (withContext context (eager function)) (state, [])).map
        (fun out => Program.mapTranscript (Sum.map id Subtype.val) id
          (Program.mapState (fun pair => (pair.1, mapTable Subtype.val pair.2)) out))) =
      program.run (withContext context oracle) (state, []) := by
  rw [← PMF.map_bind, eager_lazy_context]
  exact finite_context_restriction_run allowed context program included state

end CryptoOracle.RandomOracle
