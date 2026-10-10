import Foundation.Constructions.Hash.Chains
import Foundation.Crypto.Semantics.Oracle.Composition
import Foundation.Crypto.Semantics.Oracle.RandomOracleCollision
import Mathlib.Data.List.Nodup

/-! Inlining the real two-interface experiment into ideal compression calls.
The certificate counts calls including cached/repeated evaluations. It bounds
internal compression queries, not machine transitions or wall-clock time.
-/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Result : Type} [DecidableEq Payload] [DecidableEq Digest]
  [Fintype Digest] [Nonempty Digest]

def compressionCall (initial : Digest) (terminal : Payload) :
    WorldInput Payload Digest → Program (CompressionInput Payload Digest) Digest Digest
  | .inl message => prefixFreeMD initial terminal message
  | .inr input => .query input .done

def expand (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result) :
    Program (CompressionInput Payload Digest) Digest Result :=
  attack.inline (compressionCall initial terminal)

/-- The expanded experiment computes the actual real world, retaining its
final shared compression table. Internal compression traces are hidden only at
the observation boundary, not erased from the expanded program. -/
theorem expand_run (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (table : CompressionTable Payload Digest) :
    ((expand initial terminal attack).run RandomOracle.oracle table).map Program.resultState =
      (attack.run (realWorld initial terminal) table).map Program.resultState := by
  have ho : Program.implementedOracle (compressionCall initial terminal) RandomOracle.oracle =
      realWorld initial terminal := by
    funext state request
    cases request with
    | inl message => rfl
    | inr input =>
        simp [Program.implementedOracle, compressionCall, Program.run, Program.resultState,
          realWorld, PMF.map_bind, PMF.pure_map]
  simpa only [expand, ho] using
    Program.inline_run (compressionCall initial terminal) attack RandomOracle.oracle table

/-- A source-call budget together with a per-call compression budget.
For a high-level query the latter includes the terminal block. Low-level queries
consume one compression call. All response and local-coin branches are bounded. -/
inductive WorldBound (blockLimit : Nat) :
    Program (WorldInput Payload Digest) Digest Result → Nat → Prop where
  | done (result : Result) (q : Nat) : WorldBound blockLimit (.done result) q
  | hash (message : List Payload) (next : Digest → Program (WorldInput Payload Digest) Digest Result)
      (q : Nat) (length : message.length + 1 ≤ blockLimit)
      (bound : ∀ response, WorldBound blockLimit (next response) q) :
      WorldBound blockLimit (.query (.inl message) next) (q + 1)
  | compression (input : CompressionInput Payload Digest)
      (next : Digest → Program (WorldInput Payload Digest) Digest Result)
      (q : Nat) (positive : 1 ≤ blockLimit)
      (bound : ∀ response, WorldBound blockLimit (next response) q) :
      WorldBound blockLimit (.query (.inr input) next) (q + 1)
  | coin (next : Bool → Program (WorldInput Payload Digest) Digest Result)
      (q : Nat) (bound : ∀ bit, WorldBound blockLimit (next bit) q) :
      WorldBound blockLimit (.coin next) q

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem WorldBound.mono {blockLimit q r : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit attack q) (larger : q ≤ r) :
    WorldBound blockLimit attack r := by
  induction bound generalizing r with
  | done result q => exact .done _ _
  | hash message next q hl hb ih =>
      cases r with
      | zero => omega
      | succ r => exact .hash _ _ r hl (fun response => ih response (by omega))
  | compression input next q hp hb ih =>
      cases r with
      | zero => omega
      | succ r => exact .compression _ _ r hp (fun response => ih response (by omega))
  | coin next q hb ih => exact .coin _ r (fun bit => ih bit larger)

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem WorldBound.queries {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit attack q) : attack.BoundedQueries q := by
  induction bound with
  | done result q => exact .done _ _
  | hash message next q hl hb ih => exact .query _ _ q ih
  | compression input next q hp hb ih => exact .query _ _ q ih
  | coin next q hb ih => exact .coin _ q ih

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem WorldBound.expanded_queries {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit attack q) (initial : Digest) (terminal : Payload) :
    (expand initial terminal attack).BoundedQueries (q * blockLimit) := by
  induction bound with
  | done result q => exact .done _ _
  | hash message next q hl hb ih =>
      have hh := (prefixFreeMD_queries initial terminal message).mono hl
      have ht := hh.bind (fun response => expand initial terminal (next response)) ih
      simpa only [expand, Program.inline, compressionCall, Nat.add_mul, Nat.one_mul,
        Nat.add_comm] using ht
  | compression input next q hp hb ih =>
      have hOne : (compressionCall initial terminal (.inr input)).BoundedQueries 1 :=
        .query input .done 0 (fun response => .done response 0)
      have hh := hOne.mono hp
      have ht := hh.bind (fun response => expand initial terminal (next response)) ih
      simpa only [expand, Program.inline, compressionCall, Nat.add_mul, Nat.one_mul,
        Nat.add_comm] using ht
  | coin next q hb ih => exact .coin _ (q * blockLimit) ih

/-- The first bad event is bounded for the entire two-interface real experiment,
including the compression evaluations hidden inside every adaptive hash call. -/
theorem real_collision_bound {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit attack q) (initial : Digest) (terminal : Payload) :
    eventProb (attack.run (realWorld initial terminal) [])
      (fun out => ¬RandomOracle.FreshOutputs initial out.state) ≤
      (((q * blockLimit) * (q * blockLimit + 1) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have he := congrArg (fun p : ProbComp (CompressionTable Payload Digest × Result) =>
    eventProb p (fun answer => ¬RandomOracle.FreshOutputs initial answer.1))
    (expand_run initial terminal attack [])
  simp only [eventProb_map, Program.resultState] at he
  rw [← he]
  exact RandomOracle.empty_collision_bound (bound.expanded_queries initial terminal) initial

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Distinct stored output values imply the graph invariant used by the search. -/
theorem freshOutputs_graph {initial : Digest} {table : CompressionTable Payload Digest}
    (good : RandomOracle.FreshOutputs initial table) :
    OutputInjective table ∧ AvoidInitial initial table := by
  constructor
  · intro left hl right hr he
    exact congrArg Prod.fst (List.inj_on_of_nodup_map good.1 hl hr he)
  · intro entry hm he
    exact good.2 (List.mem_map.mpr ⟨entry, hm, he⟩)

/-- The real graph invariant fails only when a sampled output collides with
an earlier output or the initial value. The bound includes all internal calls. -/
theorem real_graph_failure_bound {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit attack q) (initial : Digest) (terminal : Payload) :
    eventProb (attack.run (realWorld initial terminal) [])
      (fun out => ¬(OutputInjective out.state ∧ AvoidInitial initial out.state)) ≤
      (((q * blockLimit) * (q * blockLimit + 1) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  refine (eventProb_mono _ ?_).trans (real_collision_bound bound initial terminal)
  intro out hbad hgood
  exact hbad (freshOutputs_graph hgood)

/-- Failure to reconstruct a genuine chain in the full real compression table
has the same explicit bound. Missing private-table edges in the ideal simulator
are not covered by this lemma and require the separate hidden-chain argument. -/
theorem real_search_failure_bound {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit attack q) (initial : Digest) (terminal : Payload) :
    eventProb (attack.run (realWorld initial terminal) [])
      (fun out => ∃ blocks target, DataChain initial out.state blocks target ∧
        messagePrefix initial out.state out.state.length target ≠ some blocks) ≤
      (((q * blockLimit) * (q * blockLimit + 1) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  refine (eventProb_mono _ ?_).trans (real_graph_failure_bound bound initial terminal)
  rintro out ⟨blocks, target, chain, fails⟩ ⟨injective, avoid⟩
  exact fails (messagePrefix_complete injective avoid chain)

end Foundation.Hash
