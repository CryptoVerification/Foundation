import Foundation.Constructions.Hash.LatentResources

/-! Decoding the actual symbolic reservation graph into compression data edges.
The graph contains genuine complete data paths after high-level reservation.
This deterministic bridge does not yet supply the real/ideal joint law or its
marginal proofs. The graph may have digest collisions after decoding. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest]

local instance decodedGraphBEq : BEq ((Digest ⊕ Label) × Payload) := instBEqOfDecidableEq
local instance decodedCompressionBEq : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq
local instance decodedLabelBEq : BEq Label := instBEqOfDecidableEq

/-- Interpret an explicit digest literally and a reserved vertex by its finite
coordinate. This is proof instrumentation, not an operation exposed to S. -/
def latentValue (function : Label → Digest) : Digest ⊕ Label → Digest := Sum.elim id function

def latentDecodedEdge (function : Label → Digest) (edge : ((Digest ⊕ Label) × Payload) × Label) :
    CompressionInput Payload Digest × Digest :=
  ((latentValue function edge.1.1, (false, edge.1.2)), function edge.2)

def latentDecodedGraph (function : Label → Digest) (state : LatentState Payload Digest Label) :
    CompressionTable Payload Digest := state.graph.map (latentDecodedEdge function)

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem latentDecodedGraph_mono (function : Label → Digest)
    {before after : LatentState Payload Digest Label} (included : before.graph ⊆ after.graph) :
    latentDecodedGraph function before ⊆ latentDecodedGraph function after :=
  List.map_subset _ included

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem reserveLabel_graph (state : LatentState Payload Digest Label) :
    (reserveLabel state).1.graph = state.graph := by
  cases supply : state.supply <;> simp [reserveLabel, supply]

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem reserveLabel_none_overflow (state : LatentState Payload Digest Label)
    (missing : (reserveLabel state).2 = none) : (reserveLabel state).1.overflow = true := by
  cases supply : state.supply with
  | nil => simp [reserveLabel, supply]
  | cons label rest => simp [reserveLabel, supply] at missing

omit [Fintype Digest] [Nonempty Digest] in
theorem latentAdvance_graph_subset (initial : Digest) (state : LatentState Payload Digest Label)
    (parent : Digest ⊕ Label) (block : Payload) :
    state.graph ⊆ (latentAdvance initial state parent block).1.graph := by
  unfold latentAdvance
  split
  · exact List.Subset.refl _
  · dsimp only
    split
    · simp only [reserveLabel_graph]
      exact List.subset_cons_self _ _
    · rw [reserveLabel_graph]
      exact List.Subset.refl _

omit [Fintype Digest] [Nonempty Digest] in
theorem reserveMessage_graph_subset (initial : Digest) (state : LatentState Payload Digest Label)
    (parent : Digest ⊕ Label) (message : List Payload) :
    state.graph ⊆ (reserveMessage initial state parent message).graph := by
  induction message generalizing state parent with
  | nil => exact List.Subset.refl _
  | cons block rest ih =>
      exact List.Subset.trans (latentAdvance_graph_subset initial state parent block)
        (ih (latentAdvance initial state parent block).1 (latentAdvance initial state parent block).2)


omit [Fintype Digest] [Nonempty Digest] in
theorem latentAdvance_graph_consistent (initial : Digest) (state : LatentState Payload Digest Label)
    (valid : RandomOracle.TableConsistent state.graph) (parent : Digest ⊕ Label) (block : Payload) :
    RandomOracle.TableConsistent (latentAdvance initial state parent block).1.graph := by
  unfold latentAdvance
  split
  · exact valid
  · rename_i fresh
    dsimp only
    split
    · rw [reserveLabel_graph]
      exact valid.cons _ _ fresh
    · rwa [reserveLabel_graph]

omit [Fintype Digest] [Nonempty Digest] in
theorem reserveMessage_graph_consistent (initial : Digest) (state : LatentState Payload Digest Label)
    (valid : RandomOracle.TableConsistent state.graph) (parent : Digest ⊕ Label) (message : List Payload) :
    RandomOracle.TableConsistent (reserveMessage initial state parent message).graph := by
  induction message generalizing state parent with
  | nil => exact valid
  | cons block rest ih =>
      exact ih _ (latentAdvance_graph_consistent initial state valid parent block) _

omit [Fintype Digest] [Nonempty Digest] in
theorem chooseLatent_graph_consistent (initial : Digest) (state : LatentState Payload Digest Label)
    (valid : RandomOracle.TableConsistent state.graph) (input : CompressionInput Payload Digest) :
    RandomOracle.TableConsistent (chooseLatent initial state input).1.graph := by
  unfold chooseLatent
  split
  · dsimp only
    split
    · split
      · exact valid
      · rwa [reserveLabel_graph]
    · rename_i fresh
      split
      · rw [reserveLabel_graph]
        exact valid.cons _ _ fresh
      · rwa [reserveLabel_graph]
  · rwa [reserveLabel_graph]

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem finishLatent_graph (state : LatentState Payload Digest Label)
    (input : CompressionInput Payload Digest) (selected : Option Label) (output : Digest) :
    (finishLatent state input selected output).graph = state.graph := by
  cases selected <;> rfl

/-- Symbolic graph storage is a function, even on overflowing executions and
without digest collision assumptions. This uses the actual ideal transitions. -/
theorem latent_step_graph_consistent (initial : Digest) (terminal : Payload)
    (state : LatentWorldState Payload Digest Label) (valid : RandomOracle.TableConsistent state.1.graph)
    (request : WorldInput Payload Digest) (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentWorld initial terminal RandomOracle.oracle state request).support) :
    RandomOracle.TableConsistent answer.1.1.graph := by
  rcases state with ⟨control, hashes, coordinates⟩
  rw [latentWorld_eq] at support
  cases request with
  | inl message =>
      simp only at support
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨result, _, rfl⟩ := support
      exact reserveMessage_graph_consistent initial control valid (.inl initial) message
  | inr input =>
      simp only at support
      cases cached : control.exposed.lookup input with
      | some output =>
          simp only [cached, PMF.mem_support_pure_iff] at support
          subst answer
          exact valid
      | none =>
          simp only [cached] at support
          cases recognized : terminalMessage initial terminal control.exposed input with
          | some message =>
              simp only [recognized] at support
              rw [PMF.mem_support_map_iff] at support
              obtain ⟨result, _, rfl⟩ := support
              exact valid
          | none =>
              simp only [recognized] at support
              cases selected : (chooseLatent initial control input).2 with
              | none =>
                  simp only [selected] at support
                  rw [PMF.mem_support_map_iff] at support
                  obtain ⟨output, _, rfl⟩ := support
                  rw [finishLatent_graph]
                  exact chooseLatent_graph_consistent initial control valid input
              | some label =>
                  simp only [selected] at support
                  rw [PMF.mem_support_map_iff] at support
                  obtain ⟨result, _, rfl⟩ := support
                  rw [finishLatent_graph]
                  exact chooseLatent_graph_consistent initial control valid input

theorem latent_run_graph_consistent {Result : Type} (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : LatentWorldState Payload Digest Label) (valid : RandomOracle.TableConsistent state.1.graph)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentWorld initial terminal) state).support) :
    RandomOracle.TableConsistent out.state.1.graph :=
  Program.run_preserves _ (fun state => RandomOracle.TableConsistent state.1.graph)
    (latent_step_graph_consistent initial terminal) attack state valid out support

omit [Fintype Digest] [Nonempty Digest] in
/-- Each successful reservation denotes an actual data edge in the decoded
new graph. No collision-freedom or hidden-coordinate independence is assumed. -/
theorem latentAdvance_decoded_edge (initial : Digest) (function : Label → Digest)
    (state : LatentState Payload Digest Label) (parent : Digest ⊕ Label) (block : Payload)
    (noOverflow : (latentAdvance initial state parent block).1.overflow = false) :
    ((latentValue function parent, (false, block)),
      latentValue function (latentAdvance initial state parent block).2) ∈
        latentDecodedGraph function (latentAdvance initial state parent block).1 := by
  cases lookup : state.graph.lookup (parent, block) with
  | some child =>
      simp only [latentAdvance, lookup] at noOverflow ⊢
      obtain ⟨before, after, table, _⟩ := List.lookup_eq_some_iff.mp lookup
      apply List.mem_map.mpr
      refine ⟨((parent, block), child), ?_, rfl⟩
      rw [table]
      simp
  | none =>
      simp only [latentAdvance, lookup] at noOverflow ⊢
      cases selected : (reserveLabel state).2 with
      | some child =>
          simp only [selected] at noOverflow ⊢
          apply List.mem_map.mpr
          exact ⟨_, List.mem_cons_self, rfl⟩
      | none =>
          simp only [selected] at noOverflow ⊢
          have overflow := reserveLabel_none_overflow state selected
          exact Bool.noConfusion (overflow.symm.trans noOverflow)

omit [Fintype Digest] [Nonempty Digest] in
/-- Reserving a complete message really produces its data path. The explicit
capacity hypothesis is discharged for bounded reachable worlds by LatentResources.
The terminal hash response is intentionally not a data edge in this graph. -/
theorem reserveMessage_decoded_chain (initial : Digest) (function : Label → Digest)
    (state : LatentState Payload Digest Label) (valid : state.AllocationValid)
    (notOverflow : state.overflow = false) (parent : Digest ⊕ Label) (message : List Payload)
    (available : message.length ≤ state.supply.length) :
    ∃ target, DataChain (latentValue function parent)
      (latentDecodedGraph function (reserveMessage initial state parent message)) message target := by
  induction message generalizing state parent with
  | nil => exact ⟨latentValue function parent, .nil⟩
  | cons block rest ih =>
      have allocation := latentAdvance_allocation initial state valid parent block
      have one : 1 ≤ state.supply.length := by
        simp only [List.length_cons] at available
        omega
      have noOverflow : (latentAdvance initial state parent block).1.overflow = false :=
        (allocation.overflow one).trans notOverflow
      have remaining : rest.length ≤ (latentAdvance initial state parent block).1.supply.length := by
        have := allocation.length
        simp only [List.length_cons] at available
        omega
      obtain ⟨target, tail⟩ := ih (latentAdvance initial state parent block).1 allocation.valid noOverflow
        (latentAdvance initial state parent block).2 remaining
      have first := latentAdvance_decoded_edge initial function state parent block noOverflow
      have finalEdge := latentDecodedGraph_mono function
        (reserveMessage_graph_subset initial (latentAdvance initial state parent block).1
          (latentAdvance initial state parent block).2 rest) first
      have start : DataChain (latentValue function parent)
          (latentDecodedGraph function (reserveMessage initial state parent (block :: rest))) [block]
          (latentValue function (latentAdvance initial state parent block).2) := .snoc block .nil finalEdge
      exact ⟨target, by simpa only [List.singleton_append] using start.append tail⟩


omit [Fintype Digest] [Nonempty Digest] in
/-- Decoding preserves graph functionality when no two distinct symbolic
inputs alias to the same compression input. This is a concrete deterministic
separation condition; its failure probability is not assumed to be small here. -/
theorem latentDecodedGraph_consistent (function : Label → Digest)
    (state : LatentState Payload Digest Label) (valid : RandomOracle.TableConsistent state.graph)
    (separated : ∀ left ∈ state.graph, ∀ right ∈ state.graph,
      (latentDecodedEdge function left).1 = (latentDecodedEdge function right).1 → left.1 = right.1) :
    RandomOracle.TableConsistent (latentDecodedGraph function state) := by
  apply RandomOracle.TableConsistent.of_functional
  intro input left right hl hr
  obtain ⟨leftEdge, hl, leftEq⟩ := List.mem_map.mp hl
  obtain ⟨rightEdge, hr, rightEq⟩ := List.mem_map.mp hr
  have keys : leftEdge.1 = rightEdge.1 := separated leftEdge hl rightEdge hr (by rw [leftEq, rightEq])
  have rightMember : (rightEdge.1, rightEdge.2) ∈ state.graph := hr
  rw [← keys] at rightMember
  have children : leftEdge.2 = rightEdge.2 := valid.functional hl rightMember
  calc
    left = function leftEdge.2 := (congrArg Prod.snd leftEq).symm
    _ = function rightEdge.2 := congrArg function children
    _ = right := congrArg Prod.snd rightEq

/-- The reserved decoded path has exactly the existing compression execution
semantics when its decoded table is coherent: no extra sampling or table update
occurs. The equality retains every actual data-compression query in the trace.
Coherence must be derived from the eventual real/ideal invariant, not postulated
as a security assumption. -/
theorem reserveMessage_decoded_replay (initial : Digest) (function : Label → Digest)
    (state : LatentState Payload Digest Label) (valid : state.AllocationValid)
    (notOverflow : state.overflow = false) (parent : Digest ⊕ Label) (message : List Payload)
    (available : message.length ≤ state.supply.length)
    (consistent : RandomOracle.TableConsistent
      (latentDecodedGraph function (reserveMessage initial state parent message))) :
    ∃ target trace, (iterate (latentValue function parent) (message.map (fun block => (false, block)))).run
      RandomOracle.oracle (latentDecodedGraph function (reserveMessage initial state parent message)) =
      PMF.pure (⟨target, latentDecodedGraph function (reserveMessage initial state parent message), trace⟩ :
        Outcome (CompressionInput Payload Digest) Digest Digest (CompressionTable Payload Digest)) := by
  obtain ⟨target, chain⟩ := reserveMessage_decoded_chain initial function state valid notOverflow parent message available
  obtain ⟨trace, replay⟩ := chain.replay consistent
  exact ⟨target, trace, replay⟩

end Foundation.Hash
