import Foundation.Crypto.Semantics.Oracle.FiniteContextRequests

/-! Finite-function sampling with the original unrestricted query interface.
Outside the explicitly finite possible domain an arbitrary fixed value is used.
The value is unreachable in the certified program, not assumed random. -/
namespace CryptoOracle.RandomOracle

open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Input Target Other Output Context Result : Type} [DecidableEq Input] [DecidableEq Target]
  [Fintype Output] [Nonempty Output]

/-- Extend a function from a finite subset using a specified fixed default. -/
def extendFinite (allowed : Finset Input) (fallback : Output)
    (function : {input // input ∈ allowed} → Output) (input : Input) : Output :=
  if member : input ∈ allowed then function ⟨input, member⟩ else fallback

omit [DecidableEq Target] [Fintype Output] [Nonempty Output] in
theorem extendFinite_apply (allowed : Finset Input) (fallback : Output)
    (function : {input // input ∈ allowed} → Output) (input : {input // input ∈ allowed}) :
    extendFinite allowed fallback function input.val = function input := by
  simp [extendFinite, input.property]

omit [Fintype Output] [Nonempty Output] in
/-- Reindexing an eager function preserves its real cache, even when that cache
already contains values. The function is compared only along the encoding. -/
theorem reindex_eager_step (encode : Input → Target) (injective : Function.Injective encode)
    (function : Target → Output) (table : Table Input Output) (input : Input) :
    (eager (fun value => function (encode value)) table input).map
      (fun answer => (mapTable encode answer.1, answer.2)) =
      eager function (mapTable encode table) (encode input) := by
  simp only [eager, lookup_mapTable encode injective]
  cases known : table.lookup input <;> simp [PMF.pure_map, mapTable]

omit [Fintype Output] [Nonempty Output] in
theorem reindex_eager_context_step (encode : Input → Target) (injective : Function.Injective encode)
    (function : Target → Output) (context : Oracle Other Output Context)
    (state : Context) (table : Table Input Output) (request : Other ⊕ Input) :
    (withContext context (eager (fun value => function (encode value))) (state, table) request).map
      (fun answer => ((answer.1.1, mapTable encode answer.1.2), answer.2)) =
      withContext context (eager function) (state, mapTable encode table) (Sum.map id encode request) := by
  cases request with
  | inl other => simp [withContext, PMF.map_comp, Function.comp_def]
  | inr input =>
      have encoded := congrArg (PMF.map (fun answer => ((state, answer.1), answer.2)))
        (reindex_eager_step encode injective function table input)
      simpa [withContext, Sum.map, PMF.map_comp, Function.comp_def] using encoded

omit [Fintype Output] [Nonempty Output] in
theorem reindex_eager_context_run (encode : Input → Target) (injective : Function.Injective encode)
    (function : Target → Output) (context : Oracle Other Output Context)
    (program : Program (Other ⊕ Input) Output Result) (state : Context) (table : Table Input Output) :
    (program.run (withContext context (eager (fun value => function (encode value)))) (state, table)).map
      (Program.mapState (fun pair => (pair.1, mapTable encode pair.2))) =
    program.run (Program.adaptOracle (Sum.map id encode) id (withContext context (eager function)))
      (state, mapTable encode table) := by
  apply Program.run_state_map
  intro pair request
  change _ = PMF.map id _
  rw [PMF.map_id]
  exact reindex_eager_context_step encode injective function context pair.1 pair.2 request

omit [DecidableEq Target] [Nonempty Output] in
/-- Pointwise, the finite-domain program has exactly the same whole outcome as
the original program run with the finite function's fixed total extension. -/
theorem finite_context_extension_run [DecidableEq Other]
    (allowed : Finset Input) (fallback : Output) (function : {input // input ∈ allowed} → Output)
    (context : Oracle Other Output Context) (program : Program (Other ⊕ Input) Output Result)
    (included : ∀ input, Sum.inr input ∈ program.possibleRequests → input ∈ allowed) (state : Context) :
    ((program.restrictRightTo allowed included).run (withContext context (eager function)) (state, [])).map
      (fun out => Program.mapTranscript (Sum.map id Subtype.val) id
        (Program.mapState (fun pair => (pair.1, mapTable Subtype.val pair.2)) out)) =
      program.run (withContext context (eager (extendFinite allowed fallback function))) (state, []) := by
  have restrictedFunction : (fun input : {input // input ∈ allowed} =>
      extendFinite allowed fallback function input.val) = function := by
    funext input
    exact extendFinite_apply allowed fallback function input
  have reindexed := congrArg (PMF.map (Program.mapTranscript (Sum.map id Subtype.val) id))
    (reindex_eager_context_run Subtype.val Subtype.val_injective (extendFinite allowed fallback function)
      context (program.restrictRightTo allowed included) state [])
  rw [restrictedFunction] at reindexed
  have mapped := Program.mapQueries_run (Sum.map id Subtype.val) id
    (program.restrictRightTo allowed included) (withContext context (eager (extendFinite allowed fallback function))) (state, [])
  rw [Program.restrictRightTo_val] at mapped
  have eraseFun : Program.mapTranscript (id : Other ⊕ Input → Other ⊕ Input) (id : Output → Output) =
      (id : Outcome (Other ⊕ Input) Output Result (Context × Table Input Output) → _) := by
    funext out
    cases out
    simp [Program.mapTranscript]
  rw [eraseFun, PMF.map_id] at mapped
  simpa only [PMF.map_comp, mapTable, List.map_nil, Function.comp_def] using reindexed.trans mapped.symm

omit [DecidableEq Target] in
/-- Sampling a finite function and evaluating its fixed total extension on the
original query type exactly realizes the lazy oracle in the independent context.
This is a finitely supported law on total functions, not a uniform infinite law. -/
theorem finite_context_extension_eager [DecidableEq Other]
    (allowed : Finset Input) (fallback : Output) (context : Oracle Other Output Context)
    (program : Program (Other ⊕ Input) Output Result)
    (included : ∀ input, Sum.inr input ∈ program.possibleRequests → input ∈ allowed) (state : Context) :
    (uniform ({input // input ∈ allowed} → Output)).bind (fun function =>
      program.run (withContext context (eager (extendFinite allowed fallback function))) (state, [])) =
      program.run (withContext context oracle) (state, []) := by
  simp_rw [← finite_context_extension_run allowed fallback _ context program included state]
  exact finite_context_restriction_eager allowed context program included state

end CryptoOracle.RandomOracle
