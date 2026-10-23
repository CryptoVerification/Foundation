import Foundation.Crypto.Logic.Polygraph.OracleProofEdits

/-! Elementary proof edits under explicit cache facts. A fact list is a
conjunction of observations, not an overwriting table: even facts about the
same message are retained. Inconsistent facts describe unreachable states.
Every primitive rule changes only adjacent commands or one query response.
There is no semantic-equality generator or recursive-suffix primitive.
-/
namespace CryptoOracle.ProofEdits
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Input Tag Result : Type} [DecidableEq Input]

/-- All recorded observations hold in the actual cache. Conflicting facts
are allowed syntactically, but no physical cache can satisfy them. -/
def Knows (facts : List (Input × Tag)) (table : RandomOracle.Table Input Tag) : Prop :=
  ∀ message tag, (message, tag) ∈ facts → table.lookup message = some tag

theorem knows_nil (table : RandomOracle.Table Input Tag) : Knows [] table := by
  intro message tag member
  cases member

theorem Knows.query {facts : List (Input × Tag)} {table : RandomOracle.Table Input Tag}
    (valid : Knows facts table) (world : Oracle Input Tag (RandomOracle.Table Input Tag))
    (laws : CacheLaws world) (request : Input) (answer : RandomOracle.Table Input Tag × Tag)
    (reachable : answer ∈ (world table request).support) :
    Knows ((request, answer.2) :: facts) answer.1 := by
  intro message tag member
  rcases List.mem_cons.mp member with same | old
  · cases same
    exact laws.stores table request answer reachable
  · exact laws.retains table request answer reachable message tag (valid message tag old)

/-- Finite elementary schemata with a cache-fact index. Query contexts add
the observed answer; history operations do not change the cache facts. -/
inductive LocalEdit : List (Input × Tag) → Command Input Tag Result → Command Input Tag Result → Type where
  | refl (facts p) : LocalEdit facts p p
  | symm {facts p q} : LocalEdit facts p q → LocalEdit facts q p
  | trans {facts p q r} : LocalEdit facts p q → LocalEdit facts q r → LocalEdit facts p r
  | recordQuery (facts message request) (next : Tag → Command Input Tag Result) :
      LocalEdit facts (.record message (.query request next))
        (.query request (fun tag => .record message (next tag)))
  | freshQuery (facts message request) (next : Bool → Tag → Command Input Tag Result) :
      LocalEdit facts (.fresh message (fun fresh => .query request (next fresh)))
        (.query request (fun tag => .fresh message (fun fresh => next fresh tag)))
  | freshRecord (facts message other) (different : message ≠ other)
      (next : Bool → Command Input Tag Result) :
      LocalEdit facts (.fresh message (fun fresh => .record other (next fresh)))
        (.record other (.fresh message next))
  | cachedQuery (facts message tag) (known : (message, tag) ∈ facts)
      (next : Tag → Command Input Tag Result) :
      LocalEdit facts (.query message next) (.query message (fun _ => next tag))
  | query (facts message) {p q : Tag → Command Input Tag Result} :
      (∀ tag, LocalEdit ((message, tag) :: facts) (p tag) (q tag)) →
        LocalEdit facts (.query message p) (.query message q)
  | record (facts message) {p q} :
      LocalEdit facts p q → LocalEdit facts (.record message p) (.record message q)
  | fresh (facts message) {p q : Bool → Command Input Tag Result} :
      (∀ bit, LocalEdit facts (p bit) (q bit)) → LocalEdit facts (.fresh message p) (.fresh message q)
  | coin (facts) {p q : Bool → Command Input Tag Result} :
      (∀ bit, LocalEdit facts (p bit) (q bit)) → LocalEdit facts (.coin p) (.coin q)

/-- The only semantic assumptions are the local oracle cache contracts and
the explicitly indexed facts. Whole-route equalities are conclusions. -/
theorem LocalEdit.sound {facts : List (Input × Tag)} {p q : Command Input Tag Result}
    (edit : LocalEdit facts p q) (world : Oracle Input Tag (RandomOracle.Table Input Tag))
    (laws : CacheLaws world) (signed : List Input) (table : RandomOracle.Table Input Tag)
    (valid : Knows facts table) : p.run world signed table = q.run world signed table := by
  induction edit generalizing signed table with
  | refl => rfl
  | symm edit ih => exact (ih signed table valid).symm
  | trans first second ihFirst ihSecond =>
      exact (ihFirst signed table valid).trans (ihSecond signed table valid)
  | recordQuery => rfl
  | freshQuery => rfl
  | freshRecord facts message other different next =>
      simp [Command.run, Command.compile, different]
  | cachedQuery facts message tag known next =>
      simp only [Command.run, Command.compile, Program.run,
        laws.known table message tag (valid message tag known), PMF.pure_bind]
  | query facts message edits ih =>
      simp only [Command.run, Command.compile, Program.run]
      apply bind_congr_of_support
      intro answer reachable
      exact congrArg (PMF.map (fun out =>
        { out with trace := (message, answer.2) :: out.trace }))
        (ih answer.2 signed answer.1 (valid.query world laws message answer reachable))
  | record facts message edit ih => exact ih (signed ++ [message]) table valid
  | fresh facts message edits ih => exact ih (decide (message ∉ signed)) signed table valid
  | coin facts edits ih =>
      simp only [Command.run, Command.compile, Program.run]
      congr 1
      funext bit
      exact ih bit signed table valid

/-- Expand substitution through a suffix into elementary cached-query rules
and contexts. Every recursive query is accounted for in the proof term. -/
def Command.recallLocalEdit (p : Command Input Tag Result) (facts : List (Input × Tag))
    (message : Input) (tag : Tag) (known : (message, tag) ∈ facts) :
    LocalEdit facts p (p.recall message tag) :=
  match p with
  | .done _ => .refl _ _
  | .record request next => .record facts request (next.recallLocalEdit facts message tag known)
  | .fresh request next => .fresh facts request (fun bit =>
      (next bit).recallLocalEdit facts message tag known)
  | .coin next => .coin facts (fun bit => (next bit).recallLocalEdit facts message tag known)
  | .query request next => by
      by_cases same : request = message
      · subst request
        simpa only [Command.recall, if_pos rfl, ite_true] using
          LocalEdit.trans (.cachedQuery facts message tag known next)
            (.query facts message (fun response =>
              (next tag).recallLocalEdit ((message, response) :: facts) message tag
                (List.mem_cons_of_mem _ known)))
      · simpa only [Command.recall, if_neg same] using
          LocalEdit.query facts request (fun response =>
            (next response).recallLocalEdit ((request, response) :: facts) message tag
              (List.mem_cons_of_mem _ known))

def Command.rememberLocalEdit (p : Command Input Tag Result) (facts : List (Input × Tag)) :
    LocalEdit facts p p.remember :=
  match p with
  | .done _ => .refl _ _
  | .query message next => .query facts message (fun tag =>
      (next tag).recallLocalEdit ((message, tag) :: facts) message tag (by simp))
  | .record message next => .record facts message (next.rememberLocalEdit facts)
  | .fresh message next => .fresh facts message (fun bit => (next bit).rememberLocalEdit facts)
  | .coin next => .coin facts (fun bit => (next bit).rememberLocalEdit facts)

/-- Eliminate every macro in the previous edit language, including both
consecutive repetition and whole-suffix recall. No semantic proof is used. -/
def Edit.expand {p q : Command Input Tag Result} (edit : Edit p q)
    (facts : List (Input × Tag)) : LocalEdit facts p q :=
  match edit with
  | .refl p => .refl facts p
  | .symm previous => .symm (previous.expand facts)
  | .trans first second => .trans (first.expand facts) (second.expand facts)
  | .recordQuery message request next => .recordQuery facts message request next
  | .freshQuery message request next => .freshQuery facts message request next
  | .freshRecord message other different next => .freshRecord facts message other different next
  | .repeatQuery message next =>
      .query facts message (fun tag => .cachedQuery ((message, tag) :: facts) message tag
        (by simp) (next tag))
  | .recallQuery message next =>
      .query facts message (fun tag => (next tag).recallLocalEdit
        ((message, tag) :: facts) message tag (by simp))
  | .query message edits => .query facts message (fun tag => (edits tag).expand ((message, tag) :: facts))
  | .record message previous => .record facts message (previous.expand facts)
  | .fresh message edits => .fresh facts message (fun bit => (edits bit).expand facts)
  | .coin edits => .coin facts (fun bit => (edits bit).expand facts)

/-- Retain the same complete posterior joint law using only elementary edits.
The fact precondition is checked against the actual initial cache. -/
theorem LocalEdit.posterior_square [Fintype Input] [Fintype Tag] [Nonempty Tag]
    {facts : List (Input × Tag)} {p q : Command Input Tag Result} (edit : LocalEdit facts p q)
    (signed : List Input) (table : RandomOracle.Table Input Tag) (valid : Knows facts table) :
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
      (edit.sound RandomOracle.oracle lazy_cache_laws signed table valid)

theorem LocalEdit.sampling_square [Fintype Input] [Fintype Tag] [Nonempty Tag]
    {facts : List (Input × Tag)} {p q : Command Input Tag Result} (edit : LocalEdit facts p q)
    (signed : List Input) (table : RandomOracle.Table Input Tag) (valid : Knows facts table) :
    (uniform (Input → Tag)).bind (fun function => p.run (RandomOracle.eager function) signed table) =
      q.run RandomOracle.oracle signed table := by
  have projected := congrArg (PMF.map Prod.fst) (edit.posterior_square signed table valid)
  simpa [PMF.map, Function.comp_def] using projected

end CryptoOracle.ProofEdits
