import Foundation.Constructions.Hash.GraphFreshness
import Foundation.Crypto.Semantics.Oracle.Composition

/-! Paths witnessed by actual compression executions. These statements do not
assume collision freedom: they show existence, while graph uniqueness is a
separate theorem. Terminal blocks cannot be used as data edges. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest : Type} [DecidableEq Payload] [DecidableEq Digest]
  [Fintype Digest] [Nonempty Digest]

local instance : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Iteration over concatenated blocks is syntactically sequential iteration. -/
theorem iterate_append (initial : Digest) (left right : List Payload) :
    iterate initial (left ++ right) =
      (iterate initial left).bind (fun target => iterate target right) := by
  induction left generalizing initial with
  | nil => rfl
  | cons block rest ih =>
      simp only [List.cons_append, iterate, Program.bind]
      congr 1
      funext target
      exact ih target

/-- The data portion of an actual execution witnesses a path in the final
shared table. Future calls preserve every compression answer along that path. -/
theorem iterate_data_chain (initial : Digest) (message : List Payload)
    (table : CompressionTable Payload Digest)
    (out : Outcome (CompressionInput Payload Digest) Digest Digest
      (CompressionTable Payload Digest))
    (support : out ∈ ((iterate initial (message.map (fun block => (false, block)))).run
      RandomOracle.oracle table).support) :
    DataChain initial out.state message out.result := by
  induction message generalizing initial table out with
  | nil =>
      rw [List.map_nil, iterate, Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact .nil
  | cons block rest ih =>
      rw [List.map_cons, iterate, Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      have path := ih answer.2 answer.1 tail ht
      have records := (RandomOracle.step table (initial, (false, block)) answer ha).1
      have keep := (RandomOracle.run (iterate answer.2 (rest.map (fun b => (false, b))))
        answer.1 tail ht).1
      have final := keep (initial, (false, block)) answer.2 records
      obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp final
      have edge : ((initial, (false, block)), answer.2) ∈ tail.state := by rw [he]; simp
      have first : DataChain initial tail.state [block] answer.2 := .snoc block .nil edge
      simpa using first.append path

/-- Every actual prefix-free hash response is a data chain followed by its
unique marked terminal compression call, all present in the final shared table. -/
theorem prefixFreeMD_chain (initial : Digest) (terminal : Payload) (message : List Payload)
    (table : CompressionTable Payload Digest)
    (out : Outcome (CompressionInput Payload Digest) Digest Digest
      (CompressionTable Payload Digest))
    (support : out ∈ ((prefixFreeMD initial terminal message).run RandomOracle.oracle table).support) :
    ∃ target, DataChain initial out.state message target ∧
      ((target, (true, terminal)), out.result) ∈ out.state := by
  rw [prefixFreeMD, encode, iterate_append, Program.run_bind,
    PMF.mem_support_bind_iff] at support
  obtain ⟨first, hf, ht⟩ := support
  rw [PMF.mem_support_map_iff] at ht
  obtain ⟨last, hl, rfl⟩ := ht
  simp only [iterate, Program.run, PMF.pure_map] at hl
  rw [PMF.mem_support_bind_iff] at hl
  obtain ⟨answer, ha, he⟩ := hl
  rw [PMF.mem_support_pure_iff] at he
  subst last
  have dataPath := iterate_data_chain initial message table first hf
  obtain ⟨records, _keeps, _⟩ := RandomOracle.step first.state
    (first.result, (true, terminal)) answer ha
  have includes := RandomOracle.step_table_subset first.state
    (first.result, (true, terminal)) answer ha
  refine ⟨first.result, dataPath.mono includes, ?_⟩
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp records
  rw [he]
  simp


/-- A good compression step cannot create a new path to its own input state.
This prevents a newly added edge from being used as its own predecessor. -/
theorem compression_step_chain_input (initial : Digest)
    (table : CompressionTable Payload Digest) (input : CompressionInput Payload Digest)
    (answer : CompressionTable Payload Digest × Digest)
    (support : answer ∈ (RandomOracle.oracle table input).support)
    (good : ForwardFresh initial answer.1)
    {blocks : List Payload} (chain : DataChain initial answer.1 blocks input.1) :
    DataChain initial table blocks input.1 := by
  cases ht : table.lookup input with
  | some output =>
      rw [RandomOracle.known table input output ht, PMF.mem_support_pure_iff] at support
      subst answer
      exact chain
  | none =>
      rw [RandomOracle.fresh table input ht, PMF.mem_support_map_iff] at support
      obtain ⟨output, _, rfl⟩ := support
      apply chain.remove_new_edge
      · intro hm
        exact good.1 (by
          simp only [graphForbidden, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr (Or.inr hm)))
      · exact (good.no_fixed_point (input, output) (List.mem_cons_self ..)).symm

/-- A stored coherent data path can be replayed without drawing randomness
or changing storage. The equation retains the actual compression trace. -/
theorem DataChain.replay {initial : Digest} {table : CompressionTable Payload Digest}
    (consistent : RandomOracle.TableConsistent table)
    {message : List Payload} {target : Digest} (chain : DataChain initial table message target) :
    ∃ trace, (iterate initial (message.map (fun block => (false, block)))).run
      RandomOracle.oracle table =
      PMF.pure (⟨target, table, trace⟩ :
        Outcome (CompressionInput Payload Digest) Digest Digest (CompressionTable Payload Digest)) := by
  induction chain with
  | nil => exact ⟨[], rfl⟩
  | @snoc blocks previous target block chain edge ih =>
      obtain ⟨trace, he⟩ := ih
      refine ⟨trace ++ [((previous, (false, block)), target)], ?_⟩
      simp [List.map_append, iterate_append, Program.run_bind, he, iterate,
        Program.run, RandomOracle.known table (previous, (false, block)) target (consistent _ edge),
        PMF.pure_map]

/-- A recorded complete hash path determines the exact cached hash execution,
including its terminal call. Compression-output collisions are permitted. -/
theorem prefixFreeMD_replay {initial : Digest} {terminal : Payload}
    {table : CompressionTable Payload Digest} (consistent : RandomOracle.TableConsistent table)
    {message : List Payload} {target output : Digest}
    (chain : DataChain initial table message target)
    (terminalEdge : ((target, (true, terminal)), output) ∈ table) :
    ∃ trace, (prefixFreeMD initial terminal message).run RandomOracle.oracle table =
      PMF.pure (⟨output, table, trace⟩ :
        Outcome (CompressionInput Payload Digest) Digest Digest (CompressionTable Payload Digest)) := by
  obtain ⟨trace, he⟩ := chain.replay consistent
  refine ⟨trace ++ [((target, (true, terminal)), output)], ?_⟩
  simp [prefixFreeMD, encode, iterate_append, Program.run_bind, he, iterate, Program.run,
    RandomOracle.known table (target, (true, terminal)) output (consistent _ terminalEdge),
    PMF.pure_map]

/-- Evaluating only data blocks cannot create a new terminal-marked entry. -/
theorem iterate_data_terminal_old (initial : Digest) (message : List Payload)
    (table : CompressionTable Payload Digest)
    (out : Outcome (CompressionInput Payload Digest) Digest Digest (CompressionTable Payload Digest))
    (support : out ∈ ((iterate initial (message.map (fun block => (false, block)))).run
      RandomOracle.oracle table).support)
    (entry : CompressionInput Payload Digest × Digest) (member : entry ∈ out.state)
    (terminal : entry.1.2.1 = true) : entry ∈ table := by
  induction message generalizing initial table out with
  | nil =>
      rw [List.map_nil, iterate, Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact member
  | cons block rest ih =>
      rw [List.map_cons, iterate, Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      have old := ih answer.2 answer.1 tail ht member
      rcases List.mem_cons.mp (RandomOracle.step_entries table (initial, (false, block)) answer ha old) with he | he
      · subst entry
        cases terminal
      · exact he

/-- Apart from the one returned terminal entry, every terminal-marked entry
in a hash execution predates that execution. -/
theorem prefixFreeMD_terminal_entries (initial : Digest) (terminal : Payload) (message : List Payload)
    (table : CompressionTable Payload Digest)
    (out : Outcome (CompressionInput Payload Digest) Digest Digest (CompressionTable Payload Digest))
    (support : out ∈ ((prefixFreeMD initial terminal message).run RandomOracle.oracle table).support) :
    ∃ target, DataChain initial out.state message target ∧
      ((target, (true, terminal)), out.result) ∈ out.state ∧
      ∀ entry ∈ out.state, entry.1.2.1 = true →
        entry ∈ table ∨ entry = ((target, (true, terminal)), out.result) := by
  rw [prefixFreeMD, encode, iterate_append, Program.run_bind, PMF.mem_support_bind_iff] at support
  obtain ⟨first, hf, ht⟩ := support
  rw [PMF.mem_support_map_iff] at ht
  obtain ⟨last, hl, rfl⟩ := ht
  simp only [iterate, Program.run, PMF.pure_map] at hl
  rw [PMF.mem_support_bind_iff] at hl
  obtain ⟨answer, ha, he⟩ := hl
  rw [PMF.mem_support_pure_iff] at he
  subst last
  have includes := RandomOracle.step_table_subset first.state (first.result, (true, terminal)) answer ha
  have records := (RandomOracle.step first.state (first.result, (true, terminal)) answer ha).1
  have returned : ((first.result, (true, terminal)), answer.2) ∈ answer.1 := by
    obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp records
    rw [he]
    simp
  refine ⟨first.result, (iterate_data_chain initial message table first hf).mono includes, returned, ?_⟩
  intro entry member marked
  rcases List.mem_cons.mp (RandomOracle.step_entries first.state (first.result, (true, terminal)) answer ha member) with he | he
  · exact Or.inr he
  · exact Or.inl (iterate_data_terminal_old initial message table first hf entry he marked)

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- For any backend, the final actual query is the marked terminal call and
its response is exactly the returned high-level digest. -/
theorem prefixFreeMD_last_query {State : Type}
    (backend : Oracle (CompressionInput Payload Digest) Digest State)
    (initial : Digest) (terminal : Payload) (message : List Payload) (state : State)
    (out : Outcome (CompressionInput Payload Digest) Digest Digest State)
    (support : out ∈ ((prefixFreeMD initial terminal message).run backend state).support) :
    ∃ target, out.trace.getLast? = some ((target, (true, terminal)), out.result) := by
  rw [prefixFreeMD, encode, iterate_append, Program.run_bind, PMF.mem_support_bind_iff] at support
  obtain ⟨first, hf, ht⟩ := support
  rw [PMF.mem_support_map_iff] at ht
  obtain ⟨last, hl, rfl⟩ := ht
  simp only [iterate, Program.run, PMF.pure_map] at hl
  rw [PMF.mem_support_bind_iff] at hl
  obtain ⟨answer, ha, he⟩ := hl
  rw [PMF.mem_support_pure_iff] at he
  subst last
  exact ⟨first.result, List.getLast?_concat⟩

end Foundation.Hash
