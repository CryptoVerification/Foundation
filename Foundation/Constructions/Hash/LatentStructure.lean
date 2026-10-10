import Foundation.Constructions.Hash.LatentPairedStep

/-! Structural and remaining-capacity premises for the actual coordinate
ideal world. Existing allocation bounds are reused with an arbitrary hash
kernel. No global transcript agreement is assumed or proved in this module. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest]
  [DecidableEq Label] [Fintype Digest] [Nonempty Digest]

/-- The existing label-allocation bound applies to every fixed-coordinate
transition, with exactly the same independent hash kernel. -/
theorem latent_coordinate_step_allocation (initial : Digest) (terminal : Payload)
    (function : Label → Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : LatentWorldState Payload Digest Label) (valid : state.1.AllocationValid)
    (request : WorldInput Payload Digest) (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function)
      hashOracle state request).support) :
    AllocationBound state.1 answer.1.1 (latentRequestCost request) :=
  latent_step_allocation initial terminal state valid request answer
    (latent_coordinate_eager_step_support initial terminal function hashOracle state request answer support)

/-- Whole adaptive coordinate executions satisfy the existing total
allocation bound for arbitrary hash kernels and arbitrary valid initial states. -/
theorem latent_coordinate_run_allocation {Result : Type} {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : LatentWorldState Payload Digest Label) (valid : state.1.AllocationValid)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function)
      hashOracle) state).support) :
    AllocationBound state.1 out.state.1 (q * blockLimit) :=
  latent_run_allocation bound initial terminal state valid out
    (latent_coordinate_eager_run_support initial terminal function hashOracle attack state out support)

/-- Unique incoming symbolic edges are preserved for every fixed coordinate
function, including functions with digest collisions. -/
theorem latent_coordinate_step_children_unique (initial : Digest) (terminal : Payload)
    (function : Label → Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : LatentWorldState Payload Digest Label) (valid : state.1.AllocationValid)
    (unique : state.1.ChildrenUnique) (request : WorldInput Payload Digest)
    (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function)
      hashOracle state request).support) : answer.1.1.ChildrenUnique :=
  latent_step_children_unique initial terminal state valid unique request answer
    (latent_coordinate_eager_step_support initial terminal function hashOracle state request answer support)

/-- Coherence, fixed-coordinate values, valid allocation and unique graph
children hold jointly throughout the actual adaptive execution. -/
theorem latent_coordinate_run_structural {Result : Type} (initial : Digest) (terminal : Payload)
    (function : Label → Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (attack : Program (WorldInput Payload Digest) Digest Result) (state : LatentWorldState Payload Digest Label)
    (valid : LatentCoherent state ∧ RandomOracle.TableValues function state.1.revealed ∧
      state.1.AllocationValid ∧ state.1.ChildrenUnique)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function)
      hashOracle) state).support) :
    LatentCoherent out.state ∧ RandomOracle.TableValues function out.state.1.revealed ∧
      out.state.1.AllocationValid ∧ out.state.1.ChildrenUnique := by
  apply Program.run_preserves _
    (fun before => LatentCoherent before ∧ RandomOracle.TableValues function before.1.revealed ∧
      before.1.AllocationValid ∧ before.1.ChildrenUnique) _ attack state valid out support
  intro before invariant request answer reachable
  exact ⟨latent_coordinate_eager_step_coherent initial terminal function hashOracle before invariant.1 request answer reachable,
    latent_coordinate_eager_step_values initial terminal function hashOracle before invariant.1 invariant.2.1 request answer reachable,
    (latent_coordinate_step_allocation initial terminal function hashOracle before invariant.2.2.1 request answer reachable).valid,
    latent_coordinate_step_children_unique initial terminal function hashOracle before invariant.2.2.1 invariant.2.2.2 request answer reachable⟩

/-- The common structural premises and absence of overflow follow from an
empty start with a duplicate-free supply of at least q*blockLimit labels. -/
theorem latent_coordinate_structural_from_empty {Result : Type} {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (supply : List Label) (nodup : supply.Nodup) (available : q * blockLimit ≤ supply.length)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function)
      hashOracle) (LatentState.empty supply, ([], []))).support) :
    LatentCoherent out.state ∧ RandomOracle.TableValues function out.state.1.revealed ∧
      out.state.1.AllocationValid ∧ out.state.1.ChildrenUnique ∧ out.state.1.overflow = false ∧
      supply.length ≤ out.state.1.supply.length + q * blockLimit := by
  have structural := latent_coordinate_run_structural initial terminal function hashOracle attack
    (LatentState.empty supply, ([], []))
    ⟨latent_empty_coherent supply, (by intro entry member; cases member), latent_empty_allocation supply nodup,
      (by intro left member; cases member)⟩ out support
  have resources := latent_coordinate_run_allocation bound initial terminal function hashOracle
    (LatentState.empty supply, ([], [])) (latent_empty_allocation supply nodup) out support
  exact ⟨structural.1, structural.2.1, structural.2.2.1, structural.2.2.2,
    resources.overflow available, resources.length⟩

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
/-- A bounded program's current outer call costs at most blockLimit labels.
The hash case counts data blocks; its terminating block uses the hash window. -/
theorem WorldBound.query_cost {Result : Type} {blockLimit q : Nat}
    {request : WorldInput Payload Digest} {next : Digest → Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit (.query request next) (q + 1)) :
    latentRequestCost request ≤ blockLimit := by
  cases bound with
  | hash message next q length rest => simp only [latentRequestCost]; omega
  | compression input next q positive rest => exact positive

/-- One actual call has enough labels and preserves capacity for all q
remaining bounded calls. The premise is a total remaining budget, not an
assumed capacity condition separately supplied at each query. -/
theorem latent_coordinate_step_capacity {Result : Type} {blockLimit q : Nat}
    {request : WorldInput Payload Digest} {next : Digest → Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit (.query request next) (q + 1))
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : LatentWorldState Payload Digest Label) (valid : state.1.AllocationValid)
    (available : (q + 1) * blockLimit ≤ state.1.supply.length)
    (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function)
      hashOracle state request).support) :
    latentRequestCost request ≤ state.1.supply.length ∧
      q * blockLimit ≤ answer.1.1.supply.length ∧ answer.1.1.overflow = state.1.overflow := by
  have resources := latent_coordinate_step_allocation initial terminal function hashOracle state valid request answer support
  have current := bound.query_cost
  have split : q * blockLimit + blockLimit ≤ state.1.supply.length := by
    simpa only [Nat.add_mul, Nat.one_mul] using available
  have length := resources.length
  have enough : latentRequestCost request ≤ state.1.supply.length := by omega
  exact ⟨enough, by omega, resources.overflow enough⟩

omit [DecidableEq Digest] [DecidableEq Label] in
/-- The actual factored backend preserves hash-cache agreement with a fixed
hash function. Coordinate and local-random requests leave that cache untouched. -/
theorem latent_coordinate_backend_hash_values
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashFunction : List Payload → Digest)
    (state : RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest)
    (valid : RandomOracle.TableValues hashFunction state.1)
    (request : LatentRequest Payload Label)
    (answer : (RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest) × Digest)
    (support : answer ∈ (Program.adaptOracle latentContextRequest id
      (RandomOracle.withContext (simulatorBackend (RandomOracle.eager hashFunction)) coordinates)
      state request).support) :
    RandomOracle.TableValues hashFunction answer.1.1 := by
  change answer ∈ (PMF.map id (RandomOracle.withContext
    (simulatorBackend (RandomOracle.eager hashFunction)) coordinates state (latentContextRequest request))).support at support
  rw [PMF.map_id] at support
  cases request with
  | inl message =>
      change answer ∈ ((RandomOracle.eager hashFunction state.1 message).map
        (fun response => ((response.1, state.2), response.2))).support at support
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨response, reachable, rfl⟩ := support
      exact (RandomOracle.eager_step_values hashFunction state.1 valid message response reachable).1
  | inr selected =>
      cases selected with
      | none =>
          change answer ∈ (((uniform Digest).map (fun output => (state.1, output))).map
            (fun response => ((response.1, state.2), response.2))).support at support
          rw [PMF.mem_support_map_iff] at support
          obtain ⟨response, reachable, rfl⟩ := support
          rw [PMF.mem_support_map_iff] at reachable
          obtain ⟨output, _, rfl⟩ := reachable
          exact valid
      | some label =>
          change answer ∈ ((coordinates state.2 label).map
            (fun response => ((state.1, response.1), response.2))).support at support
          rw [PMF.mem_support_map_iff] at support
          obtain ⟨response, _, rfl⟩ := support
          exact valid

/-- Hash-cache agreement is preserved by one actual outer ideal call,
including reservation and publication of symbolic coordinates. -/
theorem latent_coordinate_step_hash_values (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashFunction : List Payload → Digest) (state : LatentWorldState Payload Digest Label)
    (valid : RandomOracle.TableValues hashFunction state.2.1)
    (request : WorldInput Payload Digest) (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentCoordinateWorld initial terminal coordinates
      (RandomOracle.eager hashFunction) state request).support) :
    RandomOracle.TableValues hashFunction answer.1.2.1 := by
  unfold latentCoordinateWorld Program.statefulOracle at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, reachable, rfl⟩ := support
  exact Program.run_preserves _ (fun backend => RandomOracle.TableValues hashFunction backend.1)
    (latent_coordinate_backend_hash_values coordinates hashFunction)
    (latentProgram initial terminal state.1 request) state.2 valid out reachable

/-- The ideal hash cache retains its own agreement with the shared fixed
function throughout an actual adaptive execution; cache-key equality with the
real world is not required. -/
theorem latent_coordinate_run_hash_values {Result : Type} (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashFunction : List Payload → Digest) (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : LatentWorldState Payload Digest Label)
    (valid : RandomOracle.TableValues hashFunction state.2.1)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentCoordinateWorld initial terminal coordinates
      (RandomOracle.eager hashFunction)) state).support) :
    RandomOracle.TableValues hashFunction out.state.2.1 :=
  Program.run_preserves _ (fun before => RandomOracle.TableValues hashFunction before.2.1)
    (latent_coordinate_step_hash_values initial terminal coordinates hashFunction) attack state valid out support

end Foundation.Hash
