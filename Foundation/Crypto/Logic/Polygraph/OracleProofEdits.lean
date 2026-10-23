import Foundation.Crypto.Semantics.Oracle.RandomOracleFinite
import Foundation.Crypto.Semantics.Oracle.Composition

/-! A restricted edit language for adaptive oracle proofs with signing history.
There is no constructor accepting an arbitrary semantic equality. History
updates and membership tests are explicit syntax. Their interpreter compiles
to the existing oracle syntax and retains the result, final signing history,
actual cache and full request/response trace. Repeated-query substitution
keeps both calls and both transcript entries; it is not a cost optimization.
-/
namespace CryptoOracle.ProofEdits
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Input Tag Result : Type} [DecidableEq Input]

inductive Command (Input Tag Result : Type) where
  | done : Result → Command Input Tag Result
  | query : Input → (Tag → Command Input Tag Result) → Command Input Tag Result
  | record : Input → Command Input Tag Result → Command Input Tag Result
  | fresh : Input → (Bool → Command Input Tag Result) → Command Input Tag Result
  | coin : (Bool → Command Input Tag Result) → Command Input Tag Result

namespace Command

/-- The history is private to the game. The attacker obtains oracle responses
only; history tests are introduced by the explicit game instrumentation. -/
def compile (signed : List Input) : Command Input Tag Result →
    Program Input Tag (Result × List Input)
  | .done result => .done (result, signed)
  | .query message next => .query message (fun tag => compile signed (next tag))
  | .record message next => compile (signed ++ [message]) next
  | .fresh message next => compile signed (next (decide (message ∉ signed)))
  | .coin next => .coin (fun bit => compile signed (next bit))

/-- Substitute a known cached response through an arbitrary adaptive suffix.
Calls are retained, including repeated calls and their actual trace entries. -/
def recall (message : Input) (tag : Tag) : Command Input Tag Result → Command Input Tag Result
  | .done result => .done result
  | .query request next => .query request (fun response =>
      recall message tag (next (if request = message then tag else response)))
  | .record request next => .record request (recall message tag next)
  | .fresh request next => .fresh request (fun bit => recall message tag (next bit))
  | .coin next => .coin (fun bit => recall message tag (next bit))

/-- Remember the first queried response on each branch, including across
intervening queries, history updates, history tests and local coins. -/
def remember : Command Input Tag Result → Command Input Tag Result
  | .done result => .done result
  | .query message next => .query message (fun tag => recall message tag (next tag))
  | .record message next => .record message (remember next)
  | .fresh message next => .fresh message (fun bit => remember (next bit))
  | .coin next => .coin (fun bit => remember (next bit))

noncomputable def run (world : Oracle Input Tag (RandomOracle.Table Input Tag))
    (signed : List Input) (table : RandomOracle.Table Input Tag) (p : Command Input Tag Result) :=
  (p.compile signed).run world table

/-- Emit an oracle program which returns the result and hides the private
history. This is program syntax, not a separately attached witness register. -/
def finish (signed : List Input) (p : Command Input Tag Result) : Program Input Tag Result :=
  (p.compile signed).bind (fun result => .done result.1)

theorem finish_result (p : Command Input Tag Result) (signed : List Input)
    (world : Oracle Input Tag (RandomOracle.Table Input Tag)) (table : RandomOracle.Table Input Tag) :
    ((p.finish signed).run world table).map Outcome.result =
      (p.run world signed table).map (fun out => out.result.1) := by
  simp [finish, Program.run_bind, Program.run, run, PMF.map, Function.comp_def]

/-- Query bounds are transported in the forward direction. The transformed
syntax still executes every query, including substituted cached responses. -/
theorem recall_queries (p : Command Input Tag Result) (message : Input) (tag : Tag)
    (signed : List Input) {q : Nat} (bound : (p.compile signed).BoundedQueries q) :
    ((p.recall message tag).compile signed).BoundedQueries q := by
  induction p generalizing signed q with
  | done result => exact .done _ _
  | record request next ih => exact ih (signed ++ [request]) bound
  | fresh request next ih => exact ih (decide (request ∉ signed)) signed bound
  | query request next ih =>
      cases bound with
      | query _ _ q bounds =>
          exact .query request _ q (fun response =>
            ih (if request = message then tag else response) signed
              (bounds (if request = message then tag else response)))
  | coin next ih =>
      cases bound with
      | coin _ _ bounds => exact .coin _ _ (fun bit => ih bit signed (bounds bit))

theorem remember_queries (p : Command Input Tag Result) (signed : List Input) {q : Nat}
    (bound : (p.compile signed).BoundedQueries q) :
    (p.remember.compile signed).BoundedQueries q := by
  induction p generalizing signed q with
  | done result => exact .done _ _
  | record request next ih => exact ih (signed ++ [request]) bound
  | fresh request next ih => exact ih (decide (request ∉ signed)) signed bound
  | query request next ih =>
      cases bound with
      | query _ _ q bounds =>
          exact .query request _ q (fun tag => (next tag).recall_queries request tag signed (bounds tag))
  | coin next ih =>
      cases bound with
      | coin _ _ bounds => exact .coin _ _ (fun bit => ih bit signed (bounds bit))

end Command

/-- A local cache law, required only for repeated-response substitution.
It says nothing about whole programs or proof routes. -/
def RepeatStable (world : Oracle Input Tag (RandomOracle.Table Input Tag)) : Prop :=
  ∀ table message answer, answer ∈ (world table message).support →
    world answer.1 message = PMF.pure (answer.1, answer.2)

theorem lazy_repeat_stable [Fintype Tag] [Nonempty Tag] :
    RepeatStable (RandomOracle.oracle (Input := Input) (Output := Tag)) := by
  intro table message answer support
  exact RandomOracle.known answer.1 message answer.2
    (RandomOracle.step table message answer support).1

theorem eager_repeat_stable (function : Input → Tag) :
    RepeatStable (RandomOracle.eager function) := by
  intro table message answer support
  cases known : table.lookup message with
  | some tag =>
      simp only [RandomOracle.eager, known, PMF.mem_support_pure_iff] at support
      subst answer
      simp [RandomOracle.eager, known]
  | none =>
      simp only [RandomOracle.eager, known, PMF.mem_support_pure_iff] at support
      subst answer
      simp [RandomOracle.eager]

/-- Local cache contracts. Retaining a known answer across *other* calls is
strictly more than the consecutive-repeat property `RepeatStable`. -/
structure CacheLaws (world : Oracle Input Tag (RandomOracle.Table Input Tag)) : Prop where
  known : ∀ table message tag, table.lookup message = some tag →
    world table message = PMF.pure (table, tag)
  stores : ∀ table request answer, answer ∈ (world table request).support →
    answer.1.lookup request = some answer.2
  retains : ∀ table request answer, answer ∈ (world table request).support →
    ∀ message tag, table.lookup message = some tag → answer.1.lookup message = some tag

theorem CacheLaws.repeatStable {world : Oracle Input Tag (RandomOracle.Table Input Tag)}
    (laws : CacheLaws world) : RepeatStable world := by
  intro table message answer support
  exact laws.known answer.1 message answer.2 (laws.stores table message answer support)

theorem lazy_cache_laws [Fintype Tag] [Nonempty Tag] :
    CacheLaws (RandomOracle.oracle (Input := Input) (Output := Tag)) where
  known := RandomOracle.known
  stores table request answer support := (RandomOracle.step table request answer support).1
  retains table request answer support := (RandomOracle.step table request answer support).2.1

theorem eager_cache_laws (function : Input → Tag) : CacheLaws (RandomOracle.eager function) where
  known table message tag known := by simp [RandomOracle.eager, known]
  stores table request answer support := by
    cases known : table.lookup request with
    | some tag =>
        simp only [RandomOracle.eager, known, PMF.mem_support_pure_iff] at support
        subst answer
        exact known
    | none =>
        simp only [RandomOracle.eager, known, PMF.mem_support_pure_iff] at support
        subst answer
        simp
  retains table request answer support message tag knownMessage := by
    cases known : table.lookup request with
    | some output =>
        simp only [RandomOracle.eager, known, PMF.mem_support_pure_iff] at support
        subst answer
        exact knownMessage
    | none =>
        simp only [RandomOracle.eager, known, PMF.mem_support_pure_iff] at support
        subst answer
        have different : message ≠ request := by
          intro same
          subst message
          rw [known] at knownMessage
          cases knownMessage
        simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr different] using knownMessage

/-- Known-coordinate substitution is justified by local cache laws and a
single lookup assertion, not by an equality of whole executions. -/
theorem Command.recall_sound (p : Command Input Tag Result)
    (world : Oracle Input Tag (RandomOracle.Table Input Tag)) (laws : CacheLaws world)
    (message : Input) (tag : Tag) (signed : List Input) (table : RandomOracle.Table Input Tag)
    (known : table.lookup message = some tag) :
    p.run world signed table = (p.recall message tag).run world signed table := by
  induction p generalizing signed table with
  | done result => rfl
  | record request next ih => exact ih (signed ++ [request]) table known
  | fresh request next ih => exact ih (decide (request ∉ signed)) signed table known
  | coin next ih =>
      simp only [recall, run, compile, Program.run]
      congr 1
      funext bit
      exact ih bit signed table known
  | query request next ih =>
      simp only [recall, run, compile, Program.run]
      apply bind_congr_of_support
      intro answer reachable
      have same : (if request = message then tag else answer.2) = answer.2 := by
        by_cases equal : request = message
        · subst request
          rw [laws.known table message tag known, PMF.mem_support_pure_iff] at reachable
          subst answer
          simp
        · simp [equal]
      rw [same]
      exact congrArg (PMF.map (fun out =>
        { out with trace := (request, answer.2) :: out.trace }))
        (ih answer.2 signed answer.1 (laws.retains table request answer reachable message tag known))

/-- Finite rule schemata and their syntactic contexts. `freshRecord` has a
real dependency condition. There is deliberately no semantic generator. -/
inductive Edit : Command Input Tag Result → Command Input Tag Result → Type where
  | refl (p) : Edit p p
  | symm {p q} : Edit p q → Edit q p
  | trans {p q r} : Edit p q → Edit q r → Edit p r
  | recordQuery (message request) (next : Tag → Command Input Tag Result) :
      Edit (.record message (.query request next))
        (.query request (fun tag => .record message (next tag)))
  | freshQuery (message request) (next : Bool → Tag → Command Input Tag Result) :
      Edit (.fresh message (fun fresh => .query request (next fresh)))
        (.query request (fun tag => .fresh message (fun fresh => next fresh tag)))
  | freshRecord (message other) (different : message ≠ other)
      (next : Bool → Command Input Tag Result) :
      Edit (.fresh message (fun fresh => .record other (next fresh)))
        (.record other (.fresh message next))
  | repeatQuery (message) (next : Tag → Tag → Command Input Tag Result) :
      Edit (.query message (fun tag => .query message (next tag)))
        (.query message (fun tag => .query message (fun _ => next tag tag)))
  | recallQuery (message) (next : Tag → Command Input Tag Result) :
      Edit (.query message next)
        (.query message (fun tag => (next tag).recall message tag))
  | query (message) {p q : Tag → Command Input Tag Result} :
      (∀ tag, Edit (p tag) (q tag)) → Edit (.query message p) (.query message q)
  | record (message) {p q} : Edit p q → Edit (.record message p) (.record message q)
  | fresh (message) {p q : Bool → Command Input Tag Result} :
      (∀ bit, Edit (p bit) (q bit)) → Edit (.fresh message p) (.fresh message q)
  | coin {p q : Bool → Command Input Tag Result} :
      (∀ bit, Edit (p bit) (q bit)) → Edit (.coin p) (.coin q)

/-- Soundness retains the actual shared cache, signing history and both
entries of a repeated query. It is uniform in all initial states. -/
theorem Edit.sound {p q : Command Input Tag Result} (edit : Edit p q)
    (world : Oracle Input Tag (RandomOracle.Table Input Tag)) (laws : CacheLaws world)
    (signed : List Input) (table : RandomOracle.Table Input Tag) :
    p.run world signed table = q.run world signed table := by
  induction edit generalizing signed table with
  | refl => rfl
  | symm edit ih => exact (ih signed table).symm
  | trans first second ihFirst ihSecond => exact (ihFirst signed table).trans (ihSecond signed table)
  | recordQuery => rfl
  | freshQuery => rfl
  | freshRecord message other different next =>
      simp [Command.run, Command.compile, different]
  | repeatQuery message next =>
      simp only [Command.run, Command.compile, Program.run]
      apply bind_congr_of_support
      intro answer reachable
      rw [laws.repeatStable table message answer reachable]
      simp only [PMF.pure_bind]
  | recallQuery message next =>
      simp only [Command.run, Command.compile, Program.run]
      apply bind_congr_of_support
      intro answer reachable
      exact congrArg (PMF.map (fun out =>
        { out with trace := (message, answer.2) :: out.trace }))
        (Command.recall_sound (next answer.2) world laws message answer.2 signed answer.1
          (laws.stores table message answer reachable))
  | query message edits ih =>
      simp only [Command.run, Command.compile, Program.run]
      congr 1
      funext answer
      exact congrArg (PMF.map (fun out =>
        { out with trace := (message, answer.2) :: out.trace })) (ih answer.2 signed answer.1)
  | record message edit ih => exact ih (signed ++ [message]) table
  | fresh message edits ih => exact ih (decide (message ∉ signed)) signed table
  | coin edits ih =>
      simp only [Command.run, Command.compile, Program.run]
      congr 1
      funext bit
      exact ih bit signed table

/-- Derive a cache-dependent edit through arbitrary private instrumentation. -/
def Command.rememberEdit (p : Command Input Tag Result) : Edit p p.remember :=
  match p with
  | .done _ => .refl _
  | .query message next => .recallQuery message next
  | .record message next => .record message next.rememberEdit
  | .fresh message next => .fresh message (fun bit => (next bit).rememberEdit)
  | .coin next => .coin (fun bit => (next bit).rememberEdit)

/-- The two orders (edit then change sampling, or change sampling then edit)
agree while retaining the residual secret function, not only the win bit.
The posterior kernel is the existing finite random-function construction.
No equality for the two whole edited programs is supplied as an input. -/
theorem Edit.posterior_square [Fintype Input] [Fintype Tag] [Nonempty Tag]
    {p q : Command Input Tag Result} (edit : Edit p q)
    (signed : List Input) (table : RandomOracle.Table Input Tag) :
    (uniform (Input → Tag)).bind (fun function =>
      (p.run (RandomOracle.eager function) signed table).map
        (fun out => (out, RandomOracle.complete table function))) =
    (q.run RandomOracle.oracle signed table).bind (fun out =>
      (uniform (Input → Tag)).map (fun function =>
        (out, RandomOracle.complete out.state function))) := by
  have sampling := RandomOracle.eager_lazy_complete (p.compile signed) table
  change (uniform (Input → Tag)).bind (fun function =>
    (p.run (RandomOracle.eager function) signed table).map
      (fun out => (out, RandomOracle.complete table function))) = _ at sampling
  rw [sampling]
  exact congrArg (fun law => law.bind (fun out =>
    (uniform (Input → Tag)).map (fun function =>
      (out, RandomOracle.complete out.state function))))
      (edit.sound RandomOracle.oracle lazy_cache_laws signed table)

/-- Forget only the residual function from the stronger posterior square. -/
theorem Edit.sampling_square [Fintype Input] [Fintype Tag] [Nonempty Tag]
    {p q : Command Input Tag Result} (edit : Edit p q)
    (signed : List Input) (table : RandomOracle.Table Input Tag) :
    (uniform (Input → Tag)).bind (fun function => p.run (RandomOracle.eager function) signed table) =
      q.run RandomOracle.oracle signed table := by
  have projected := congrArg (PMF.map Prod.fst) (edit.posterior_square signed table)
  simpa [PMF.map, Function.comp_def] using projected

end CryptoOracle.ProofEdits
