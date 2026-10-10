import Foundation.Constructions.Hash.LatentRecognition
import Foundation.Crypto.Semantics.Oracle.FiniteExtension

/-! A finite hash-function probability space for the actual compiled worlds.
Only the hash window is restricted. Local draws and the coordinate oracle stay
in an independent context, so exhaustion need not be silently deleted. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Payload Digest Label Result : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest]

/-- Reorder the existing three request cases to put the hash window on the
right of the independent local-draw/coordinate context. -/
def finiteHashRequest : SimulatorRequest Payload ⊕ Label → (Unit ⊕ Label) ⊕ List Payload
  | .inl (.inl message) => .inr message
  | .inl (.inr token) => .inl (.inl token)
  | .inr label => .inl (.inr label)

noncomputable def hashIndependentContext
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest)) :
    Oracle (Unit ⊕ Label) Digest (RandomOracle.Table Label Digest) :=
  fun table request => match request with
    | .inl _ => (uniform Digest).map (fun output => (table, output))
    | .inr label => coordinates table label

omit [DecidableEq Digest] [DecidableEq Label] in
/-- Kernel equality reorders states and requests only. No random draws are
merged, cached, or changed into a uniform function on an infinite domain. -/
theorem finite_hash_reorder_step
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (state : RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest)
    (request : SimulatorRequest Payload ⊕ Label)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    (RandomOracle.withContext (simulatorBackend hashOracle) coordinates state request).map
      (fun answer => (answer.1.swap, answer.2)) =
    RandomOracle.withContext (hashIndependentContext coordinates) hashOracle state.swap
      (finiteHashRequest request) := by
  rcases state with ⟨hashes, table⟩
  cases request with
  | inl request => cases request <;>
      simp [RandomOracle.withContext, simulatorBackend, hashIndependentContext,
        finiteHashRequest, PMF.map_comp, Function.comp_def]
  | inr label =>
      simp [RandomOracle.withContext, hashIndependentContext, finiteHashRequest,
        PMF.map_comp, Function.comp_def]

omit [DecidableEq Digest] [DecidableEq Label] in
/-- The actual compiled program retains joint backend state and result after
the request reordering. Internal target traces use the reordered interface. -/
theorem finite_hash_reorder_run
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (program : Program (SimulatorRequest Payload ⊕ Label) Digest Result)
    (hashes : RandomOracle.Table (List Payload) Digest) (table : RandomOracle.Table Label Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    ((program.mapQueries finiteHashRequest id).run
      (RandomOracle.withContext (hashIndependentContext coordinates) hashOracle) (table, hashes)).map
        Program.resultState =
    (program.run (RandomOracle.withContext (simulatorBackend hashOracle) coordinates) (hashes, table)).map
      (fun out => (out.state.swap, out.result)) := by
  have stateMap := Program.run_state_map Prod.swap
    (RandomOracle.withContext (simulatorBackend hashOracle) coordinates)
    (Program.adaptOracle finiteHashRequest id
      (RandomOracle.withContext (hashIndependentContext coordinates) hashOracle))
    (by intro state request
        change _ = PMF.map id _
        rw [PMF.map_id]
        exact finite_hash_reorder_step coordinates state request hashOracle) program (hashes, table)
  have projected := congrArg (PMF.map Program.resultState) stateMap
  have mapped := congrArg (PMF.map Program.resultState)
    (Program.mapQueries_run finiteHashRequest id program
      (RandomOracle.withContext (hashIndependentContext coordinates) hashOracle) (table, hashes))
  simp only [PMF.map_comp, Program.resultState, Program.mapState, Program.mapTranscript,
    Function.comp_def] at projected mapped
  exact mapped.trans projected.symm

omit [DecidableEq Digest] in
/-- Eagerly sampling only a finite hash domain recovers the actual original
backend's complete final caches and result. The independent coordinate kernel
may itself be eager, lazy, or a separate probabilistic kernel. -/
theorem finite_hash_execution (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (program : Program (SimulatorRequest Payload ⊕ Label) Digest Result) (allowed : Finset (List Payload))
    (included : ∀ message, Sum.inr message ∈ (program.mapQueries finiteHashRequest id).possibleRequests →
      message ∈ allowed) (table : RandomOracle.Table Label Digest) :
    (uniform ({message // message ∈ allowed} → Digest)).bind (fun function =>
      (((program.mapQueries finiteHashRequest id).restrictRightTo allowed included).run
        (RandomOracle.withContext (hashIndependentContext coordinates) (RandomOracle.eager function))
        (table, [])).map (fun out => ((out.state.1, RandomOracle.mapTable Subtype.val out.state.2), out.result))) =
    (program.run (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) coordinates) ([], table)).map
      (fun out => (out.state.swap, out.result)) := by
  have finite := congrArg (PMF.map Program.resultState)
    (RandomOracle.finite_context_restriction_eager allowed (hashIndependentContext coordinates)
      (program.mapQueries finiteHashRequest id) included table)
  simp only [PMF.map_bind, PMF.map_comp, Program.resultState, Program.mapState, Program.mapTranscript,
    Function.comp_def] at finite
  exact finite.trans (finite_hash_reorder_run coordinates program [] table)

/-- One finite domain contains every possible hash request of both actual
compiled experiments. The simulator itself does not inspect this proof domain. -/
noncomputable def coordinateHashDomain (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) : Finset (List Payload) :=
  ((realCoordinateCompiled supply (factoredRealCompiled initial terminal attack)).mapQueries
    finiteHashRequest id).rightRequests ∪
  ((latentCompiled initial terminal (LatentState.empty supply) attack).mapQueries finiteHashRequest id).rightRequests

omit [Nonempty Digest] in
theorem coordinateHashDomain_real (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (message : List Payload)
    (member : Sum.inr message ∈ ((realCoordinateCompiled supply
      (factoredRealCompiled initial terminal attack)).mapQueries finiteHashRequest id).possibleRequests) :
    message ∈ coordinateHashDomain initial terminal supply attack := by
  apply Finset.mem_union_left
  exact (Program.mem_rightRequests _ message).mpr member

omit [Nonempty Digest] in
theorem coordinateHashDomain_ideal (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (message : List Payload)
    (member : Sum.inr message ∈ ((latentCompiled initial terminal (LatentState.empty supply) attack).mapQueries
      finiteHashRequest id).possibleRequests) :
    message ∈ coordinateHashDomain initial terminal supply attack := by
  apply Finset.mem_union_right
  exact (Program.mem_rightRequests _ message).mpr member

/-- On the common finite hash domain, eager hash sampling gives the actual
outer real experiment's full final state and attacker result exactly. -/
theorem finite_hash_real_execution (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest)) :
    (uniform ({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest)).bind
      (fun function =>
        ((((realCoordinateCompiled supply (factoredRealCompiled initial terminal attack)).mapQueries
          finiteHashRequest id).restrictRightTo (coordinateHashDomain initial terminal supply attack)
            (coordinateHashDomain_real initial terminal supply attack)).run
          (RandomOracle.withContext (hashIndependentContext coordinates) (RandomOracle.eager function)) ([], [])).map
          (fun out => ((out.result.2.1,
            (out.result.1, (RandomOracle.mapTable Subtype.val out.state.2, out.state.1))), out.result.2.2))) =
    (attack.run (coordinateRealWorld initial terminal coordinates)
      ([], ((supply, false), ([], [])))).map Program.resultState := by
  have finite := congrArg (PMF.map (fun pair =>
      ((pair.2.2.1, (pair.2.1, pair.1.swap)), pair.2.2.2)))
    (finite_hash_execution coordinates (realCoordinateCompiled supply (factoredRealCompiled initial terminal attack))
      (coordinateHashDomain initial terminal supply attack) (coordinateHashDomain_real initial terminal supply attack) [])
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.swap_swap] at finite
  exact finite.trans (coordinate_real_compiled initial terminal supply attack coordinates [] [])

/-- The same finite hash domain also realizes the actual outer ideal experiment
jointly with its controller, hash cache, coordinate cache and attacker result. -/
theorem finite_hash_ideal_execution (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest)) :
    (uniform ({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest)).bind
      (fun function =>
        (((latentCompiled initial terminal (LatentState.empty supply) attack).mapQueries finiteHashRequest id).restrictRightTo
          (coordinateHashDomain initial terminal supply attack) (coordinateHashDomain_ideal initial terminal supply attack)).run
          (RandomOracle.withContext (hashIndependentContext coordinates) (RandomOracle.eager function)) ([], []) |>.map
            (fun out => ((out.result.1, (RandomOracle.mapTable Subtype.val out.state.2, out.state.1)), out.result.2))) =
    (attack.run (latentCoordinateWorld initial terminal coordinates)
      (LatentState.empty supply, ([], []))).map Program.resultState := by
  have finite := congrArg (PMF.map (fun pair => ((pair.2.1, pair.1.swap), pair.2.2)))
    (finite_hash_execution coordinates (latentCompiled initial terminal (LatentState.empty supply) attack)
      (coordinateHashDomain initial terminal supply attack) (coordinateHashDomain_ideal initial terminal supply attack) [])
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.swap_swap] at finite
  have ideal := congrArg (PMF.map (fun pair => ((pair.2.1, pair.1), pair.2.2)))
    (latent_compiled_coordinates initial terminal attack (LatentState.empty supply) ([], []) coordinates)
  simp only [PMF.map_comp, Program.resultState, Function.comp_def, Prod.mk.eta] at ideal
  exact finite.trans ideal

omit [DecidableEq Digest] in
/-- The original compiled interface can evaluate a fixed total extension of the
finite hash function. Sampling only that finite function realizes its lazy hash
backend, jointly with both caches and the program result. -/
theorem finite_hash_total_execution (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (program : Program (SimulatorRequest Payload ⊕ Label) Digest Result) (allowed : Finset (List Payload))
    (fallback : Digest)
    (included : ∀ message, Sum.inr message ∈ (program.mapQueries finiteHashRequest id).possibleRequests →
      message ∈ allowed) (table : RandomOracle.Table Label Digest) :
    (uniform ({message // message ∈ allowed} → Digest)).bind (fun function =>
      (program.run (RandomOracle.withContext
        (simulatorBackend (RandomOracle.eager (RandomOracle.extendFinite allowed fallback function))) coordinates)
        ([], table)).map (fun out => (out.state.swap, out.result))) =
    (program.run (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) coordinates) ([], table)).map
      (fun out => (out.state.swap, out.result)) := by
  have finite := congrArg (PMF.map Program.resultState)
    (RandomOracle.finite_context_extension_eager allowed fallback (hashIndependentContext coordinates)
      (program.mapQueries finiteHashRequest id) included table)
  simp only [PMF.map_bind] at finite
  simp_rw [finite_hash_reorder_run] at finite
  exact finite

/-- The original outer real-world interface can use the total extension of a
single sampled finite hash function without changing its joint final state law. -/
theorem finite_total_real_execution (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest)) (fallback : Digest) :
    (uniform ({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest)).bind
      (fun function => (attack.run (coordinateRealWorld initial terminal coordinates
        (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback function)))
        ([], ((supply, false), ([], [])))).map Program.resultState) =
    (attack.run (coordinateRealWorld initial terminal coordinates)
      ([], ((supply, false), ([], [])))).map Program.resultState := by
  have finite := congrArg (PMF.map (fun pair =>
      ((pair.2.2.1, (pair.2.1, pair.1.swap)), pair.2.2.2)))
    (finite_hash_total_execution coordinates (realCoordinateCompiled supply (factoredRealCompiled initial terminal attack))
      (coordinateHashDomain initial terminal supply attack) fallback
      (coordinateHashDomain_real initial terminal supply attack) [])
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.swap_swap] at finite
  simp_rw [coordinate_real_compiled] at finite
  exact finite

/-- The same statement holds for the original ideal-world interface, on the
same finite domain. The simulator is unchanged and never receives the function. -/
theorem finite_total_ideal_execution (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest)) (fallback : Digest) :
    (uniform ({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest)).bind
      (fun function => (attack.run (latentCoordinateWorld initial terminal coordinates
        (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback function)))
        (LatentState.empty supply, ([], []))).map Program.resultState) =
    (attack.run (latentCoordinateWorld initial terminal coordinates)
      (LatentState.empty supply, ([], []))).map Program.resultState := by
  have lower (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)) :
      ((latentCompiled initial terminal (LatentState.empty supply) attack).run
        (RandomOracle.withContext (simulatorBackend hashOracle) coordinates) ([], [])).map
          (fun out => ((out.result.1, out.state), out.result.2)) =
      (attack.run (latentCoordinateWorld initial terminal coordinates hashOracle)
        (LatentState.empty supply, ([], []))).map Program.resultState := by
    have lowered := congrArg (PMF.map (fun pair => ((pair.2.1, pair.1), pair.2.2)))
      (latent_compiled_coordinates initial terminal attack (LatentState.empty supply) ([], []) coordinates hashOracle)
    unfold Program.resultState
    simpa only [PMF.map_comp, Program.resultState, Function.comp_def, Prod.mk.eta] using lowered
  have finite := congrArg (PMF.map (fun pair => ((pair.2.1, pair.1.swap), pair.2.2)))
    (finite_hash_total_execution coordinates (latentCompiled initial terminal (LatentState.empty supply) attack)
      (coordinateHashDomain initial terminal supply attack) fallback
      (coordinateHashDomain_ideal initial terminal supply attack) [])
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.swap_swap] at finite
  simp_rw [lower] at finite
  exact finite

/-- Each fixed finite hash function has a matching reachable outcome under
the original lazy hash backend, preserving the entire final state and result.
No assertion about equal masses of the two outcomes is made. -/
theorem finite_total_real_support (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest)) (fallback : Digest)
    (function : {message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label))
    (support : out ∈ (attack.run (coordinateRealWorld initial terminal coordinates
      (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback function)))
      ([], ((supply, false), ([], [])))).support) :
    ∃ lazyOut ∈ (attack.run (coordinateRealWorld initial terminal coordinates)
      ([], ((supply, false), ([], [])))).support,
      Program.resultState lazyOut = Program.resultState out := by
  exact support_witness_of_mixture_map_eq _ _ _ Program.resultState Program.resultState
    (finite_total_real_execution initial terminal supply attack coordinates fallback)
    function (PMF.mem_support_uniformOfFintype function) out support

/-- The same support transfer for the fixed simulator preserves its graph,
public table, both backend caches, supply, exhaustion flag, and final result. -/
theorem finite_total_ideal_support (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest)) (fallback : Digest)
    (function : {message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentCoordinateWorld initial terminal coordinates
      (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback function)))
      (LatentState.empty supply, ([], []))).support) :
    ∃ lazyOut ∈ (attack.run (latentCoordinateWorld initial terminal coordinates)
      (LatentState.empty supply, ([], []))).support,
      Program.resultState lazyOut = Program.resultState out := by
  exact support_witness_of_mixture_map_eq _ _ _ Program.resultState Program.resultState
    (finite_total_ideal_execution initial terminal supply attack coordinates fallback)
    function (PMF.mem_support_uniformOfFintype function) out support

/-- With both finite functions fixed, the actual ideal execution retains the
previously proved coherence, coordinate values, unique graph children, and
capacity guarantee. Neither function needs to be injective. -/
theorem finite_total_ideal_invariants [Fintype Label] {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (supply : List Label) (nodup : supply.Nodup)
    (available : q * blockLimit ≤ supply.length) (coordinates : Label → Digest) (fallback : Digest)
    (function : {message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates)
      (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback function)))
      (LatentState.empty supply, ([], []))).support) :
    LatentCoherent out.state ∧ RandomOracle.TableValues coordinates out.state.1.revealed ∧
      out.state.1.ChildrenUnique ∧ out.state.1.overflow = false := by
  obtain ⟨lazyOut, reachable, same⟩ := finite_total_ideal_support initial terminal supply attack
    (RandomOracle.eager coordinates) fallback function out support
  have states : lazyOut.state = out.state := congrArg Prod.fst same
  have coherent := latent_eager_coherent initial terminal supply attack coordinates lazyOut reachable
  have values := latent_eager_revealed_values initial terminal supply attack coordinates lazyOut reachable
  have unique := latent_eager_children_unique initial terminal supply nodup attack coordinates lazyOut reachable
  have capacity := latent_eager_no_overflow bound initial terminal supply nodup available coordinates lazyOut reachable
  rw [states] at coherent values unique capacity
  exact ⟨coherent, values, unique, capacity⟩

/-- The concrete real allocator also avoids fallback when both finite
functions are fixed. Capacity counts internal compression calls, not time. -/
theorem finite_total_real_fin_capacity {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (coordinates : Fin (q * blockLimit) → Digest) (fallback : Digest)
    (function : {message // message ∈ coordinateHashDomain initial terminal (List.finRange (q * blockLimit)) attack} → Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result
      (CoordinateRealState Payload Digest (Fin (q * blockLimit))))
    (support : out ∈ (attack.run (coordinateRealWorld initial terminal (RandomOracle.eager coordinates)
      (RandomOracle.eager (RandomOracle.extendFinite
        (coordinateHashDomain initial terminal (List.finRange (q * blockLimit)) attack) fallback function)))
      ([], ((List.finRange (q * blockLimit), false), ([], [])))).support) :
    out.state.2.1.2 = false := by
  obtain ⟨lazyOut, reachable, same⟩ := finite_total_real_support initial terminal
    (List.finRange (q * blockLimit)) attack (RandomOracle.eager coordinates) fallback function out support
  have capacity := coordinate_real_fin_capacity bound initial terminal coordinates lazyOut reachable
  have states : lazyOut.state = out.state := congrArg Prod.fst same
  rwa [states] at capacity

end Foundation.Hash



