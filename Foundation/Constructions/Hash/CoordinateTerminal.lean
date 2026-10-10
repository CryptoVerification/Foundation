import Foundation.Constructions.Hash.LatentRelation

/-! Terminal coverage for the actual coordinate-real private hash cache.
Support transport retains the full compression and hash tables, unlike the
projection to the original real oracle which forgets the private hash cache.
No equality of probability masses or indifferentiability is asserted. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest]
  [DecidableEq Label] [Fintype Digest] [Nonempty Digest]

omit [DecidableEq Digest] [DecidableEq Label] in
/-- Arbitrary local coordinate responses are supported uniform draws. Only
hash responses require transport from the fixed hash function to the lazy RO.
Neither fresh coordinates nor an injective coordinate function are needed. -/
theorem real_coordinate_backend_hash_support
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashFunction : List Payload → Digest) (state : RealCoordinateState Payload Digest Label)
    (request : SimulatorRequest Payload) (answer : RealCoordinateState Payload Digest Label × Digest)
    (support : answer ∈ (realCoordinateWorld coordinates (RandomOracle.eager hashFunction)
      state request).support) :
    (answer.1.2.1, answer.2) ∈ (simulatorBackend RandomOracle.oracle state.2.1 request).support := by
  rw [realCoordinateWorld_eq coordinates state request (RandomOracle.eager hashFunction)] at support
  cases request with
  | inl message =>
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨response, reachable, rfl⟩ := support
      exact RandomOracle.eager_step_support hashFunction state.2.1 message response reachable
  | inr token =>
      cases token
      cases remaining : state.1.1 with
      | nil =>
          simp only [remaining, PMF.mem_support_map_iff] at support
          obtain ⟨output, _, rfl⟩ := support
          change (state.2.1, output) ∈ ((uniform Digest).map (fun value => (state.2.1, value))).support
          rw [PMF.mem_support_map_iff]
          exact ⟨output, PMF.mem_support_uniformOfFintype _, rfl⟩
      | cons label rest =>
          simp only [remaining, PMF.mem_support_map_iff] at support
          obtain ⟨response, _, rfl⟩ := support
          change (state.2.1, response.2) ∈ ((uniform Digest).map (fun value => (state.2.1, value))).support
          rw [PMF.mem_support_map_iff]
          exact ⟨response.2, PMF.mem_support_uniformOfFintype _, rfl⟩

omit [DecidableEq Label] in
/-- The full-table procedure retains both private tables when the allocator
bookkeeping is erased. This support inclusion is valid for every fixed hash
function, even for an arbitrary existing cache. -/
theorem coordinate_compression_hash_support (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashFunction : List Payload → Digest) (state : CoordinateRealState Payload Digest Label)
    (input : CompressionInput Payload Digest) (answer : CoordinateRealState Payload Digest Label × Digest)
    (support : answer ∈ (Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld coordinates (RandomOracle.eager hashFunction)) state input).support) :
    ((answer.1.1, answer.1.2.2.1), answer.2) ∈
      (compressionSimulator RandomOracle.oracle initial terminal (state.1, state.2.2.1) input).support := by
  unfold Program.statefulOracle at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, reachable, rfl⟩ := support
  have transferred := Program.run_support_state_map (fun backend => backend.2.1)
    (realCoordinateWorld coordinates (RandomOracle.eager hashFunction))
    (simulatorBackend RandomOracle.oracle)
    (real_coordinate_backend_hash_support coordinates hashFunction)
    (simulatorProgram initial terminal state.1 input) state.2 out reachable
  unfold compressionSimulator Program.statefulOracle
  rw [PMF.mem_support_map_iff]
  exact ⟨Program.mapState (fun backend => backend.2.1) out, transferred, rfl⟩

/-- Reuse the existing two-window terminal invariant for a compression-only
program by placing every request in the public compression window. -/
theorem compression_simulator_run_terminal {Result : Type} (initial : Digest) (terminal : Payload)
    (program : Program (CompressionInput Payload Digest) Digest Result)
    (table : CompressionTable Payload Digest) (hashes : RandomOracle.Table (List Payload) Digest)
    (out : Outcome (CompressionInput Payload Digest) Digest Result
      (CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest))
    (support : out ∈ (program.run (compressionSimulator RandomOracle.oracle initial terminal)
      (table, hashes)).support)
    (covered : TerminalConsistent initial terminal table hashes)
    (good : DataForwardFresh initial out.state.1) :
    TerminalConsistent initial terminal out.state.1 out.state.2 := by
  have adapter : Program.adaptOracle Sum.inr id (idealWorld RandomOracle.oracle initial terminal) =
      compressionSimulator RandomOracle.oracle initial terminal := by
    funext state input
    simp only [Program.adaptOracle, idealWorld]
    change PMF.map id _ = _
    exact PMF.map_id _
  have same := congrArg (PMF.map Program.resultState)
    (Program.mapQueries_run Sum.inr id program (idealWorld RandomOracle.oracle initial terminal) (table, hashes))
  simp only [PMF.map_comp, Program.mapTranscript, Program.resultState, Function.comp_def,
    id_eq, adapter] at same
  change ((program.mapQueries Sum.inr id).run (idealWorld RandomOracle.oracle initial terminal)
      (table, hashes)).map Program.resultState =
    (program.run (compressionSimulator RandomOracle.oracle initial terminal)
      (table, hashes)).map Program.resultState at same
  have mapped : Program.resultState out ∈
      (((program.mapQueries Sum.inr id).run (idealWorld RandomOracle.oracle initial terminal)
        (table, hashes)).map Program.resultState).support := by
    rw [same, PMF.mem_support_map_iff]
    exact ⟨out, support, rfl⟩
  rw [PMF.mem_support_map_iff] at mapped
  obtain ⟨witness, reachable, equal⟩ := mapped
  have stateEq : witness.state = out.state := congrArg Prod.fst equal
  have result := (ideal_run_terminal (program.mapQueries Sum.inr id) table hashes witness reachable).2
  rw [stateEq] at result
  exact result covered good

omit [DecidableEq Label] in
/-- Every actual adaptive two-window coordinate-real execution preserves
terminal coverage of its own private hash cache outside the final chronological
graph failure. Internal compression queries are included in this argument. -/
theorem coordinate_real_run_terminal {Result : Type} (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashFunction : List Payload → Digest)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : CoordinateRealState Payload Digest Label)
    (out : Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label))
    (support : out ∈ (attack.run (coordinateRealWorld initial terminal coordinates
      (RandomOracle.eager hashFunction)) state).support)
    (covered : TerminalConsistent initial terminal state.1 state.2.2.1)
    (good : DataForwardFresh initial out.state.1) :
    TerminalConsistent initial terminal out.state.1 out.state.2.2.1 := by
  have same := Program.inline_run (compressionCall initial terminal) attack
    (Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld coordinates (RandomOracle.eager hashFunction))) state
  have mapped : Program.resultState out ∈
      (((expand initial terminal attack).run (Program.statefulOracle (simulatorProgram initial terminal)
        (realCoordinateWorld coordinates (RandomOracle.eager hashFunction))) state).map
          Program.resultState).support := by
    rw [expand, same, PMF.mem_support_map_iff]
    exact ⟨out, support, rfl⟩
  rw [PMF.mem_support_map_iff] at mapped
  obtain ⟨expanded, reachable, equal⟩ := mapped
  have transferred := Program.run_support_state_map (fun pair => (pair.1, pair.2.2.1))
    (Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld coordinates (RandomOracle.eager hashFunction)))
    (compressionSimulator RandomOracle.oracle initial terminal)
    (coordinate_compression_hash_support initial terminal coordinates hashFunction)
    (expand initial terminal attack) state expanded reachable
  have stateEq : expanded.state = out.state := congrArg Prod.fst equal
  have result := compression_simulator_run_terminal initial terminal (expand initial terminal attack)
    state.1 state.2.2.1 (Program.mapState (fun pair => (pair.1, pair.2.2.1)) expanded) transferred covered
  simpa only [Program.mapState, stateEq] using result (by simpa only [Program.mapState, stateEq] using good)

omit [DecidableEq Label] in
/-- No initial coverage assumption is needed when the full compression table
is empty. An arbitrary existing private hash cache is allowed. -/
theorem coordinate_real_terminal_from_empty {Result : Type} (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashFunction : List Payload → Digest)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (backend : RealCoordinateState Payload Digest Label)
    (out : Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label))
    (support : out ∈ (attack.run (coordinateRealWorld initial terminal coordinates
      (RandomOracle.eager hashFunction)) ([], backend)).support)
    (good : DataForwardFresh initial out.state.1) :
    TerminalConsistent initial terminal out.state.1 out.state.2.2.1 :=
  coordinate_real_run_terminal initial terminal coordinates hashFunction attack ([], backend) out support
    (TerminalConsistent.empty initial terminal backend.2.1) good

omit [DecidableEq Digest] [DecidableEq Label] in
/-- Local coordinate draws preserve the private hash cache; hash requests
preserve its agreement with the fixed function. -/
theorem real_coordinate_backend_hash_values
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashFunction : List Payload → Digest) (state : RealCoordinateState Payload Digest Label)
    (values : RandomOracle.TableValues hashFunction state.2.1)
    (request : SimulatorRequest Payload) (answer : RealCoordinateState Payload Digest Label × Digest)
    (support : answer ∈ (realCoordinateWorld coordinates (RandomOracle.eager hashFunction)
      state request).support) :
    RandomOracle.TableValues hashFunction answer.1.2.1 := by
  rw [realCoordinateWorld_eq coordinates state request (RandomOracle.eager hashFunction)] at support
  cases request with
  | inl message =>
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨response, reachable, rfl⟩ := support
      exact (RandomOracle.eager_step_values hashFunction state.2.1 values message response reachable).1
  | inr token =>
      cases token
      cases remaining : state.1.1 <;>
        simp only [remaining, PMF.mem_support_map_iff] at support <;>
        obtain ⟨response, _, rfl⟩ := support <;>
        exact values

omit [DecidableEq Label] in
/-- Every complete internal compression procedure preserves agreement of the
real world's private hash cache with the fixed hash function. -/
theorem coordinate_compression_hash_values (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashFunction : List Payload → Digest) (state : CoordinateRealState Payload Digest Label)
    (values : RandomOracle.TableValues hashFunction state.2.2.1)
    (input : CompressionInput Payload Digest) (answer : CoordinateRealState Payload Digest Label × Digest)
    (support : answer ∈ (Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld coordinates (RandomOracle.eager hashFunction)) state input).support) :
    RandomOracle.TableValues hashFunction answer.1.2.2.1 := by
  unfold Program.statefulOracle at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, reachable, rfl⟩ := support
  exact Program.run_preserves _ (fun backend => RandomOracle.TableValues hashFunction backend.2.1)
    (real_coordinate_backend_hash_values coordinates hashFunction)
    (simulatorProgram initial terminal state.1 input) state.2 values out reachable

omit [DecidableEq Label] in
/-- Fixed-hash agreement holds throughout actual adaptive outer executions,
including all compression calls hidden inside high-level hash requests. -/
theorem coordinate_real_run_hash_values {Result : Type} (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashFunction : List Payload → Digest)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : CoordinateRealState Payload Digest Label)
    (values : RandomOracle.TableValues hashFunction state.2.2.1)
    (out : Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label))
    (support : out ∈ (attack.run (coordinateRealWorld initial terminal coordinates
      (RandomOracle.eager hashFunction)) state).support) :
    RandomOracle.TableValues hashFunction out.state.2.2.1 := by
  apply Program.run_preserves _ (fun pair => RandomOracle.TableValues hashFunction pair.2.2.1)
    _ attack state values out support
  intro pair valid request answer reachable
  unfold coordinateRealWorld Program.implementedOracle at reachable
  rw [PMF.mem_support_map_iff] at reachable
  obtain ⟨internal, internalSupport, rfl⟩ := reachable
  exact Program.run_preserves _ (fun pair => RandomOracle.TableValues hashFunction pair.2.2.1)
    (coordinate_compression_hash_values initial terminal coordinates hashFunction)
    (compressionCall initial terminal request) pair valid internal internalSupport

end Foundation.Hash
