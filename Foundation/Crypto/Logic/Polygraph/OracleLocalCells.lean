import Foundation.Crypto.Logic.Polygraph.OracleLocalEdits
import Foundation.Crypto.Logic.Polygraph.GameCoherenceCoupling

/-! Restricted comparisons between elementary oracle proof edits. Two explicit
overlaps compare history operations with cached-response substitution. This is
not an enumeration of all critical branchings or a completeness theorem.
The game interpretation deliberately uses identity state transport for these
exact edits; it therefore cannot by itself establish a proof-size advantage.
-/
namespace CryptoOracle.ProofEdits
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Input Tag Result : Type} [DecidableEq Input]

namespace LocalEdit

def recordCachedLeft (facts : List (Input × Tag)) (message request : Input) (tag : Tag)
    (known : (request, tag) ∈ facts) (next : Tag → Command Input Tag Result) :
    LocalEdit facts (.record message (.query request next))
      (.query request (fun _ => .record message (next tag))) :=
  .trans (.recordQuery facts message request next)
    (.cachedQuery facts request tag known (fun response => .record message (next response)))

def recordCachedRight (facts : List (Input × Tag)) (message request : Input) (tag : Tag)
    (known : (request, tag) ∈ facts) (next : Tag → Command Input Tag Result) :
    LocalEdit facts (.record message (.query request next))
      (.query request (fun _ => .record message (next tag))) :=
  .trans (.record facts message (.cachedQuery facts request tag known next))
    (.recordQuery facts message request (fun _ => next tag))

def freshCachedLeft (facts : List (Input × Tag)) (message request : Input) (tag : Tag)
    (known : (request, tag) ∈ facts) (next : Bool → Tag → Command Input Tag Result) :
    LocalEdit facts (.fresh message (fun bit => .query request (next bit)))
      (.query request (fun _ => .fresh message (fun bit => next bit tag))) :=
  .trans (.freshQuery facts message request next)
    (.cachedQuery facts request tag known (fun response => .fresh message (fun bit => next bit response)))

def freshCachedRight (facts : List (Input × Tag)) (message request : Input) (tag : Tag)
    (known : (request, tag) ∈ facts) (next : Bool → Tag → Command Input Tag Result) :
    LocalEdit facts (.fresh message (fun bit => .query request (next bit)))
      (.query request (fun _ => .fresh message (fun bit => next bit tag))) :=
  .trans (.fresh facts message (fun bit => .cachedQuery facts request tag known (next bit)))
    (.freshQuery facts message request (fun bit _ => next bit tag))

end LocalEdit

/-- Only the displayed overlap schemata and structural pasting generate this
relation. There is no constructor accepting arbitrary semantic agreement. -/
inductive LocalCell : {facts : List (Input × Tag)} → {p q : Command Input Tag Result} →
    LocalEdit facts p q → LocalEdit facts p q → Type where
  | refl {facts p q} (edit : LocalEdit facts p q) : LocalCell edit edit
  | symm {facts p q} {first second : LocalEdit facts p q} :
      LocalCell first second → LocalCell second first
  | trans {facts p q} {first middle last : LocalEdit facts p q} :
      LocalCell first middle → LocalCell middle last → LocalCell first last
  | seq {facts p q r} {first first' : LocalEdit facts p q} {second second' : LocalEdit facts q r} :
      LocalCell first first' → LocalCell second second' →
        LocalCell (.trans first second) (.trans first' second')
  | assoc {facts p q r s} (first : LocalEdit facts p q) (second : LocalEdit facts q r)
      (third : LocalEdit facts r s) :
      LocalCell (.trans (.trans first second) third) (.trans first (.trans second third))
  | leftUnit {facts p q} (edit : LocalEdit facts p q) : LocalCell (.trans (.refl facts p) edit) edit
  | rightUnit {facts p q} (edit : LocalEdit facts p q) : LocalCell (.trans edit (.refl facts q)) edit
  | query (facts message) {p q : Tag → Command Input Tag Result}
      {first second : ∀ tag, LocalEdit ((message, tag) :: facts) (p tag) (q tag)} :
      (∀ tag, LocalCell (first tag) (second tag)) →
        LocalCell (.query facts message first) (.query facts message second)
  | record (facts message) {p q} {first second : LocalEdit facts p q} :
      LocalCell first second → LocalCell (.record facts message first) (.record facts message second)
  | fresh (facts message) {p q : Bool → Command Input Tag Result}
      {first second : ∀ bit, LocalEdit facts (p bit) (q bit)} :
      (∀ bit, LocalCell (first bit) (second bit)) →
        LocalCell (.fresh facts message first) (.fresh facts message second)
  | coin (facts) {p q : Bool → Command Input Tag Result}
      {first second : ∀ bit, LocalEdit facts (p bit) (q bit)} :
      (∀ bit, LocalCell (first bit) (second bit)) →
        LocalCell (.coin facts first) (.coin facts second)
  | recordCached (facts message request tag) (known : (request, tag) ∈ facts)
      (next : Tag → Command Input Tag Result) :
      LocalCell (LocalEdit.recordCachedLeft facts message request tag known next)
        (LocalEdit.recordCachedRight facts message request tag known next)
  | freshCached (facts message request tag) (known : (request, tag) ∈ facts)
      (next : Bool → Tag → Command Input Tag Result) :
      LocalCell (LocalEdit.freshCachedLeft facts message request tag known next)
        (LocalEdit.freshCachedRight facts message request tag known next)

namespace LocalGames
open CryptoLogic.Polygraph.Experiment
open CryptoLogic.Polygraph.Experiment.GameCoherence

abbrev State (Input Tag Result : Type) :=
  Outcome Input Tag (Result × List Input) (RandomOracle.Table Input Tag)

noncomputable abbrev game (world : Oracle Input Tag (RandomOracle.Table Input Tag))
    (signed : List Input) (table : RandomOracle.Table Input Tag)
    (event : State Input Tag Result → Prop) (p : Command Input Tag Result) : Observed :=
  ⟨State Input Tag Result, .sample (p.run world signed table), event⟩

noncomputable def transition {facts : List (Input × Tag)} {p q : Command Input Tag Result}
    (edit : LocalEdit facts p q) (world : Oracle Input Tag (RandomOracle.Table Input Tag))
    (laws : CacheLaws world) (signed : List Input) (table : RandomOracle.Table Input Tag)
    (valid : Knows facts table) (event : State Input Tag Result → Prop) :
    Step (game world signed table event p) (game world signed table event q) :=
  Step.ofMap _ _ id (by
    change (p.run world signed table).map id = q.run world signed table
    simpa only [PMF.map_id] using edit.sound world laws signed table valid)
    (fun _ _ => Iff.rfl)

/-- Sequential editing is interpreted as sequential game transport. Each
primitive/context edit uses the exact full-state equality proved above. -/
noncomputable def path {facts : List (Input × Tag)} {p q : Command Input Tag Result}
    (edit : LocalEdit facts p q) (world : Oracle Input Tag (RandomOracle.Table Input Tag))
    (laws : CacheLaws world) (signed : List Input) (table : RandomOracle.Table Input Tag)
    (valid : Knows facts table) (event : State Input Tag Result → Prop) :
    Path (game world signed table event p) (game world signed table event q) :=
  match edit with
  | .refl .. => .identity _
  | .trans first second => .seq (path first world laws signed table valid event)
      (path second world laws signed table valid event)
  | other => .step (transition other world laws signed table valid event)

theorem path_kernel {facts : List (Input × Tag)} {p q : Command Input Tag Result}
    (edit : LocalEdit facts p q) (world : Oracle Input Tag (RandomOracle.Table Input Tag))
    (laws : CacheLaws world) (signed : List Input) (table : RandomOracle.Table Input Tag)
    (valid : Knows facts table) (event : State Input Tag Result → Prop)
    (state : State Input Tag Result) :
    (path edit world laws signed table valid event).kernel state = PMF.pure state := by
  induction edit with
  | trans first second ihFirst ihSecond =>
      change ((path first world laws signed table valid event).kernel state).bind _ = _
      rw [ihFirst, PMF.pure_bind, ihSecond]
  | _ => rfl

theorem path_loss {facts : List (Input × Tag)} {p q : Command Input Tag Result}
    (edit : LocalEdit facts p q) (world : Oracle Input Tag (RandomOracle.Table Input Tag))
    (laws : CacheLaws world) (signed : List Input) (table : RandomOracle.Table Input Tag)
    (valid : Knows facts table) (event : State Input Tag Result → Prop) :
    (path edit world laws signed table valid event).loss = 0 := by
  induction edit with
  | trans first second ihFirst ihSecond =>
      change (path first world laws signed table valid event).loss +
        (path second world laws signed table valid event).loss = 0
      rw [ihFirst, ihSecond, add_zero]
  | _ => rfl

/-- Exact edits all use identity transport. This is deliberately stated for
any two derivations: semantic agreement does not imply syntactic LocalCell
generation, nor any advantage over ordinary relational lemma sharing. -/
theorem comparison {facts : List (Input × Tag)} {p q : Command Input Tag Result}
    (first second : LocalEdit facts p q) (world : Oracle Input Tag (RandomOracle.Table Input Tag))
    (laws : CacheLaws world) (signed : List Input) (table : RandomOracle.Table Input Tag)
    (valid : Knows facts table) (event : State Input Tag Result → Prop) :
    Comparison (path first world laws signed table valid event)
      (path second world laws signed table valid event) where
  kernel_eq state := (path_kernel first world laws signed table valid event state).trans
    (path_kernel second world laws signed table valid event state).symm
  loss_eq := (path_loss first world laws signed table valid event).trans
    (path_loss second world laws signed table valid event).symm

/-- A restricted syntactic cell embeds into the existing stochastic layer.
Its caller does not supply any semantic Comparison. -/
noncomputable def cell {facts : List (Input × Tag)} {p q : Command Input Tag Result}
    {first second : LocalEdit facts p q} (_cell : LocalCell first second)
    (world : Oracle Input Tag (RandomOracle.Table Input Tag)) (laws : CacheLaws world)
    (signed : List Input) (table : RandomOracle.Table Input Tag) (valid : Knows facts table)
    (event : State Input Tag Result → Prop) :
    Cell4 (path first world laws signed table valid event)
      (path second world laws signed table valid event) :=
  .generator (comparison first second world laws signed table valid event)

theorem cell_joint {facts : List (Input × Tag)} {p q : Command Input Tag Result}
    {first second : LocalEdit facts p q} (proof : LocalCell first second)
    (world : Oracle Input Tag (RandomOracle.Table Input Tag)) (laws : CacheLaws world)
    (signed : List Input) (table : RandomOracle.Table Input Tag) (valid : Knows facts table)
    (event : State Input Tag Result → Prop) :
    (path first world laws signed table valid event).joint =
      (path second world laws signed table valid event).joint :=
  (cell proof world laws signed table valid event).joint_eq

end LocalGames
end CryptoOracle.ProofEdits
