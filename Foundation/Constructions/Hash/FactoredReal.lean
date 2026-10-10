import Foundation.Constructions.Hash.LatentGraph

/-! Exact factorization of a real compression oracle through the existing
simulator procedure, when it processes *all* compression queries, including
internal hash queries. This intermediate experiment is not the ideal world:
its private table sees internal data queries. No indifferentiability is claimed.
Completed-path registration ensures every new recognized terminal uses a fresh
ideal-hash coordinate. This fact requires no collision exclusions. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest : Type} [DecidableEq Payload] [DecidableEq Digest]
  [Fintype Digest] [Nonempty Digest]

local instance factoredCompressionBEq : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq
local instance factoredListBEq : BEq (List Payload) := instBEqOfDecidableEq

omit [Fintype Digest] [Nonempty Digest] in
/-- A registered message already has its terminal entry at the endpoint of any
of its data paths. Hence a fresh terminal input cannot represent that message. -/
theorem CompletedPaths.hash_fresh_of_terminal_fresh {initial : Digest} {terminal : Payload}
    {state : TrackedRealState Payload Digest} (completed : CompletedPaths initial terminal state)
    (consistent : RandomOracle.TableConsistent state.full)
    {message : List Payload} {target : Digest} (chain : DataChain initial state.full message target)
    (fresh : state.full.lookup (target, (true, terminal)) = none) :
    state.hashes.lookup message = none := by
  cases known : state.hashes.lookup message with
  | none => rfl
  | some output =>
      obtain ⟨before, after, table, _⟩ := List.lookup_eq_some_iff.mp known
      have member : (message, output) ∈ state.hashes := by rw [table]; simp
      obtain ⟨oldTarget, oldChain, edge⟩ := completed _ member
      have same := chain.forward_unique consistent oldChain
      subst oldTarget
      have recorded := consistent _ edge
      rw [fresh] at recorded
      cases recorded

/-- The registration invariant reuses CompletedPaths from the actual tracked
real experiment. Its unused public table and flag carry no extra assumptions. -/
def FullCompressionValid (initial : Digest) (terminal : Payload)
    (state : CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest) : Prop :=
  RandomOracle.TableConsistent state.1 ∧
    CompletedPaths initial terminal ⟨state.1, [], state.2, false⟩

/-- Giving the existing procedure every internal compression query realizes
exactly the real compression transition after forgetting its hash cache. -/
theorem compressionSimulator_full_project (initial : Digest) (terminal : Payload)
    (state : CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest)
    (valid : FullCompressionValid initial terminal state) (input : CompressionInput Payload Digest) :
    (compressionSimulator RandomOracle.oracle initial terminal state input).map
      (fun answer => (answer.1.1, answer.2)) = RandomOracle.oracle state.1 input := by
  rcases state with ⟨table, hashes⟩
  have execution := compressionSimulator_terminal_eq RandomOracle.oracle initial terminal table hashes input
  simp only [List.lookup_eq_findSome?, beq_iff_eq] at execution
  rw [execution]
  cases cached : table.lookup input with
  | some output =>
      have known := RandomOracle.known table input output cached
      simp only [List.lookup_eq_findSome?, beq_iff_eq] at cached
      simp [cached, known, PMF.pure_map]
  | none =>
      have freshFull := RandomOracle.fresh table input cached
      have cachedOriginal := cached
      simp only [List.lookup_eq_findSome?, beq_iff_eq] at cached
      simp only [cached]
      rw [freshFull]
      cases recognized : terminalMessage initial terminal table input with
      | none =>
          simp only [PMF.map_comp]
          rfl
      | some message =>
          have sound := terminalMessage_sound initial terminal table input message recognized
          have terminalEq := sound.1
          have fresh : hashes.lookup message = none := valid.2.hash_fresh_of_terminal_fresh valid.1
            sound.2 (by simpa only [← terminalEq] using cachedOriginal)
          simp only [RandomOracle.fresh hashes message fresh, PMF.map_comp]
          rfl

/-- Full-table consistency follows from the exact real marginal. Registration
is preserved by every supported recognized terminal, including collision cases. -/
theorem compressionSimulator_full_preserves (initial : Digest) (terminal : Payload)
    (state : CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest)
    (valid : FullCompressionValid initial terminal state) (input : CompressionInput Payload Digest)
    (answer : (CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest) × Digest)
    (support : answer ∈ (compressionSimulator RandomOracle.oracle initial terminal state input).support) :
    FullCompressionValid initial terminal answer.1 := by
  have projected : (answer.1.1, answer.2) ∈ (RandomOracle.oracle state.1 input).support := by
    rw [← compressionSimulator_full_project initial terminal state valid input, PMF.mem_support_map_iff]
    exact ⟨answer, support, rfl⟩
  have consistent := RandomOracle.step_table_consistent state.1 valid.1 input (answer.1.1, answer.2) projected
  refine ⟨consistent, ?_⟩
  rcases state with ⟨table, hashes⟩
  have execution := compressionSimulator_terminal_eq RandomOracle.oracle initial terminal table hashes input
  simp only [List.lookup_eq_findSome?, beq_iff_eq] at execution
  rw [execution] at support
  cases cached : table.lookup input with
  | some output =>
      simp only [List.lookup_eq_findSome?, beq_iff_eq] at cached
      simp only [cached, PMF.mem_support_pure_iff] at support
      subst answer
      exact valid.2
  | none =>
      simp only [List.lookup_eq_findSome?, beq_iff_eq] at cached
      simp only [cached] at support
      cases recognized : terminalMessage initial terminal table input with
      | none =>
          simp only [recognized, PMF.mem_support_map_iff] at support
          obtain ⟨output, _, rfl⟩ := support
          intro entry member
          obtain ⟨target, chain, edge⟩ := valid.2 entry member
          exact ⟨target, chain.mono (List.subset_cons_self _ _), List.mem_cons_of_mem _ edge⟩
      | some message =>
          simp only [recognized, PMF.mem_support_map_iff] at support
          obtain ⟨hashAnswer, hashSupport, rfl⟩ := support
          intro entry member
          rcases List.mem_cons.mp (RandomOracle.step_entries hashes message hashAnswer hashSupport member) with new | old
          · subst entry
            obtain ⟨marked, chain⟩ := terminalMessage_sound initial terminal table input message recognized
            refine ⟨input.1, chain.mono (List.subset_cons_self _ _), ?_⟩
            have terminalEq := marked
            rw [← terminalEq]
            exact List.mem_cons_self
          · obtain ⟨target, chain, edge⟩ := valid.2 entry old
            exact ⟨target, chain.mono (List.subset_cons_self _ _), List.mem_cons_of_mem _ edge⟩

/-- Exact real semantics for an arbitrary adaptive compression program. The
statement includes the entire compression transcript and final full table. -/
theorem compressionSimulator_full_run {Result : Type} (initial : Digest) (terminal : Payload)
    (program : Program (CompressionInput Payload Digest) Digest Result)
    (state : CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest)
    (valid : FullCompressionValid initial terminal state) :
    (program.run (compressionSimulator RandomOracle.oracle initial terminal) state).map
      (Program.mapState Prod.fst) = program.run RandomOracle.oracle state.1 :=
  Program.run_state_map_of_invariant Prod.fst _ _ (FullCompressionValid initial terminal)
    (compressionSimulator_full_preserves initial terminal) (compressionSimulator_full_project initial terminal)
    program state valid

/-- Expanded real-world hash and public compression calls can all be served by
the same procedure with the full internal table. This is an exact intermediate
real experiment, not the ideal world whose simulator sees only public calls. -/
theorem factored_real_resultState {Result : Type} (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result) :
    ((expand initial terminal attack).run (compressionSimulator RandomOracle.oracle initial terminal) ([], [])).map
      (fun out => (out.state.1, out.result)) =
      (attack.run (realWorld initial terminal) []).map Program.resultState := by
  have valid : FullCompressionValid initial terminal ([], []) :=
    ⟨(by intro entry member; cases member), (by intro entry member; cases member)⟩
  have same := congrArg (PMF.map Program.resultState)
    (compressionSimulator_full_run initial terminal (expand initial terminal attack) ([], []) valid)
  simp only [PMF.map_comp, Program.mapState, Program.resultState, Function.comp_def] at same
  exact same.trans (expand_run initial terminal attack [])


/-- An executable oracle program over ideal-hash requests and local uniform
draws, obtained solely by the existing expansion and stateful inliner. -/
def factoredRealCompiled {Result : Type} (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result) :
    Program (SimulatorRequest Payload) Digest (CompressionTable Payload Digest × Result) :=
  Program.inlineState (simulatorProgram initial terminal) [] (expand initial terminal attack)

/-- The actual compiled program realizes the real world's result and final
compression table. The ideal-hash backend is shared throughout this execution. -/
theorem factored_real_compiled {Result : Type} (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result) :
    ((factoredRealCompiled initial terminal attack).run (simulatorBackend RandomOracle.oracle) []).map Outcome.result =
      (attack.run (realWorld initial terminal) []).map Program.resultState := by
  have compiled := congrArg (PMF.map Prod.snd)
    (Program.inlineState_run (simulatorProgram initial terminal) (expand initial terminal attack)
      (simulatorBackend RandomOracle.oracle) [] [])
  simp only [PMF.map_comp, Program.resultState, Function.comp_def] at compiled
  exact compiled.trans (factored_real_resultState initial terminal attack)

omit [Fintype Digest] [Nonempty Digest] in
/-- This counts actual hash-or-local backend calls. It does not assign constant
machine time to a call or to the private graph's predecessor search. -/
theorem factored_real_compiled_queries {Result : Type} {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) :
    (factoredRealCompiled initial terminal attack).BoundedQueries (q * blockLimit) := by
  simpa only [factoredRealCompiled, Nat.mul_one] using
    Program.inlineState_queries (simulatorProgram initial terminal) 1 (simulatorProgram_queries initial terminal)
      (bound.expanded_queries initial terminal) []

end Foundation.Hash
