import Foundation.Crypto.Semantics.Oracle.RandomOracleReindex
import Foundation.Crypto.Semantics.Oracle.RandomOracleFinite

/-! A finite response alphabet makes the entire syntax tree finitely branching.
Its set of possible requests is finite even for an infinite request alphabet.
Restricting to this proof-only domain preserves the program and its complete
random-oracle execution. This is not a uniform distribution on infinite functions,
nor an efficient algorithm for enumerating the domain. -/
namespace CryptoOracle.Program

open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Request Response Result : Type} [DecidableEq Request] [Fintype Response]

noncomputable def possibleRequests : Program Request Response Result → Finset Request
  | .done _ => ∅
  | .query request next => by
      classical
      exact insert request (Finset.univ.biUnion fun response => possibleRequests (next response))
  | .coin next => possibleRequests (next false) ∪ possibleRequests (next true)

theorem possibleRequests_query (request : Request) (next : Response → Program Request Response Result) :
    request ∈ possibleRequests (.query request next) := by simp [possibleRequests]

theorem possibleRequests_next (request : Request) (next : Response → Program Request Response Result)
    (response : Response) : possibleRequests (next response) ⊆ possibleRequests (.query request next) := by
  intro value member
  simp only [possibleRequests, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inr ⟨response, member⟩

theorem possibleRequests_coin (next : Bool → Program Request Response Result) (bit : Bool) :
    possibleRequests (next bit) ⊆ possibleRequests (.coin next) := by
  cases bit with
  | false => exact Finset.subset_union_left
  | true => exact Finset.subset_union_right

/-- The proof parameter changes only the query type. Mapping the subtype back
to the original interface gives exactly the original syntax, including results. -/
noncomputable def restrictTo (allowed : Finset Request) :
    (program : Program Request Response Result) → (possibleRequests program ⊆ allowed) →
      Program {request // request ∈ allowed} Response Result
  | .done result, _ => .done result
  | .query request next, included => .query ⟨request, included (possibleRequests_query request next)⟩
      (fun response => restrictTo allowed (next response)
        (fun _ member => included (possibleRequests_next request next response member)))
  | .coin next, included => .coin (fun bit => restrictTo allowed (next bit)
      (fun _ member => included (possibleRequests_coin next bit member)))

theorem restrictTo_val (allowed : Finset Request) (program : Program Request Response Result)
    (included : possibleRequests program ⊆ allowed) :
    (restrictTo allowed program included).mapQueries Subtype.val id = program := by
  induction program with
  | done result => rfl
  | query request next ih =>
      simp only [restrictTo, mapQueries, id_eq]
      congr 1
      funext response
      exact ih response _
  | coin next ih =>
      simp only [restrictTo, mapQueries]
      congr 1
      funext bit
      exact ih bit _

/-- Restriction retains source query bounds and introduces no extra calls. -/
theorem restrictTo_queries (allowed : Finset Request)
    {program : Program Request Response Result} {q : Nat} (bound : program.BoundedQueries q)
    (included : possibleRequests program ⊆ allowed) :
    (restrictTo allowed program included).BoundedQueries q := by
  induction bound with
  | done result q => exact .done _ _
  | query request next q bound ih => exact .query _ _ q (fun response => ih response _)
  | coin next q bound ih => exact .coin _ q (fun bit => ih bit _)

end CryptoOracle.Program

namespace CryptoOracle.RandomOracle

open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Input Output Result : Type} [DecidableEq Input] [Fintype Output] [Nonempty Output]

/-- Finite restriction retains the entire outcome, not only a final bit.
The finite domain may contain the possible requests of several experiments. -/
theorem finite_restriction_run (allowed : Finset Input) (program : Program Input Output Result)
    (included : program.possibleRequests ⊆ allowed) :
    ((program.restrictTo allowed included).run oracle []).map
      (fun out => Program.mapTranscript Subtype.val id (Program.mapState (mapTable Subtype.val) out)) =
        program.run oracle [] := by
  have reindexed := congrArg (PMF.map (Program.mapTranscript Subtype.val id))
    (reindex_run Subtype.val Subtype.val_injective (program.restrictTo allowed included) [])
  have mapped := Program.mapQueries_run Subtype.val id (program.restrictTo allowed included)
    (oracle (Input := Input) (Output := Output)) []
  rw [Program.restrictTo_val] at mapped
  have erase (out : Outcome Input Output Result (Table Input Output)) : Program.mapTranscript id id out = out := by
    cases out
    simp [Program.mapTranscript]
  have eraseFun : Program.mapTranscript (id : Input → Input) (id : Output → Output) =
      (id : Outcome Input Output Result (Table Input Output) → _) := funext erase
  rw [eraseFun, PMF.map_id] at mapped
  simpa only [PMF.map_comp, mapTable, List.map_nil, Function.comp_def] using reindexed.trans mapped.symm

/-- A uniform finite function suffices for a fixed finite-response program on
an arbitrary input type. Only the explicitly finite restriction is sampled. -/
theorem finite_restriction_eager (allowed : Finset Input) (program : Program Input Output Result)
    (included : program.possibleRequests ⊆ allowed) :
    (uniform ({input // input ∈ allowed} → Output)).bind (fun function =>
      ((program.restrictTo allowed included).run (eager function) []).map
        (fun out => Program.mapTranscript Subtype.val id (Program.mapState (mapTable Subtype.val) out))) =
      program.run oracle [] := by
  rw [← PMF.map_bind, eager_lazy]
  exact finite_restriction_run allowed program included

end CryptoOracle.RandomOracle
